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

/**************************************************************/
/*                                                            */
/*                        NUMBER FIELDS                       */
/*                                                            */
/**************************************************************/
#include "pari.h"
#include "parinf.h"
GEN idealhermite_aux(GEN nf, GEN x);

void
checkrnf(GEN rnf)
{
  if (typ(rnf)!=t_VEC) err(idealer1);
  if (lg(rnf)!=12) err(idealer1);
}

GEN
checkbnf(GEN bnf)
{
  if (typ(bnf)!=t_VEC) err(idealer1);
  switch (lg(bnf))
  {
    case 11: return bnf;
    case 10:
      if (typ(bnf[1])==t_POL)
        err(talker,"please apply bnfinit first");
      break;
    case 7: 
      return checkbnf((GEN)bnf[1]);
      
    case 3:
      if (typ(bnf[2])==t_POLMOD)
        return checkbnf((GEN)bnf[1]);
  }
  err(idealer1);
  return NULL; /* not reached */
}

GEN
checkbnf_discard(GEN bnf)
{
  GEN x = checkbnf(bnf);
  if (x != bnf && lg(bnf) == 3)
    err(warner,"non-monic polynomial. Change of variables discarded");
  return x;
}

GEN
checknf(GEN nf)
{
  if (typ(nf)==t_POL) err(talker,"please apply nfinit first");
  if (typ(nf)!=t_VEC) err(idealer1);
  switch(lg(nf))
  {
    case 10: return nf;
    case 11: return checknf((GEN)nf[7]);
    case 7:  return checknf((GEN)nf[1]);
    case 3: if (typ(nf[2]) == t_POLMOD) return checknf((GEN)nf[1]);
  }
  err(idealer1);
  return NULL; /* not reached */
}

void
checkbnr(GEN bnr)
{
  if (typ(bnr)!=t_VEC || lg(bnr)!=7)
    err(talker,"incorrect bigray field");
  (void)checkbnf((GEN)bnr[1]);
}

void
checkbnrgen(GEN bnr)
{
  checkbnr(bnr);
  if (lg(bnr[5])<=3)
    err(talker,"please apply bnrinit(,,1) and not bnrinit(,)");
}

GEN
check_units(GEN bnf, char *f)
{
  GEN nf, x;
  bnf = checkbnf(bnf); nf = checknf(bnf);
  x = (GEN)bnf[8];
  if (lg(x) < 7 || (lg(x[5]) == 1 && lg(nf[6]) > 2))
    err(talker,"missing units in %s", f);
  return (GEN)x[5];
}

void
checkid(GEN x, long N)
{
  if (typ(x)!=t_MAT) err(idealer2);
  if (lg(x) == 1 || lg(x[1]) != N+1)
    err(talker,"incorrect matrix for ideal");
}

void
checkbid(GEN bid)
{
  if (typ(bid)!=t_VEC || lg(bid)!=6 || lg(bid[1])!=3)
    err(talker,"incorrect bigideal");
}

void
checkprimeid(GEN id)
{
  if (typ(id) != t_VEC || lg(id) != 6)
    err(talker,"incorrect prime ideal");
}

void
checkprhall(GEN prhall)
{
  if (typ(prhall) != t_VEC || lg(prhall) != 3 || typ(prhall[1]) != t_MAT)
    err(talker,"incorrect prhall format");
}

void
check_pol_int(GEN x)
{
  long k = lgef(x)-1;
  for ( ; k>1; k--)
    if (typ(x[k])!=t_INT) err(talker,"polynomial not in Z[X]");
}

GEN
checknfelt_mod(GEN nf, GEN x, char *s)
{
  if (!gegal((GEN)x[1],(GEN)nf[1]))
    err(talker,"incompatible modulus in %s:\n  mod = %Z,\n  nf  = %Z",
        s, x[1], nf[1]);
  return (GEN)x[2];
}

GEN
get_primeid(GEN x)
{
  if (typ(x) != t_VEC) return NULL;
  if (lg(x) == 3) x = (GEN)x[1];
  if (lg(x) != 6 || typ(x[3]) != t_INT) return NULL;
  return x;
}

GEN
get_bnf(GEN x, int *t)
{
  switch(typ(x))
  {
    case t_POL: *t = typ_POL;  return NULL;
    case t_QUAD: *t = typ_Q  ; return NULL;
    case t_VEC:
      switch(lg(x))
      {
        case 3:
          if (typ(x[2]) != t_POLMOD) break;
          return get_bnf((GEN)x[1],t);
        case 6 : *t = typ_QUA; return NULL;
        case 10: *t = typ_NF; return NULL;
        case 11: *t = typ_BNF; return x;
        case 7 : *t = typ_BNR;
          x = (GEN)x[1]; if (typ(x)!=t_VEC || lg(x)!=11) break;
          return x;
      }
    case t_MAT:
      if (lg(x)==2)
        switch(lg(x[1]))
        {
          case 8: case 11:
            *t = typ_CLA; return NULL;
        }
  }
  *t = typ_NULL; return NULL;
}

GEN
get_nf(GEN x, int *t)
{
  switch(typ(x))
  {
    case t_POL : *t = typ_POL; return NULL;
    case t_QUAD: *t = typ_Q  ; return NULL;
    case t_VEC:
      switch(lg(x))
      {
        case 3:
          if (typ(x[2]) != t_POLMOD) break;
          return get_nf((GEN)x[1],t);
        case 10: *t = typ_NF; return x;
        case 11: *t = typ_BNF;
          x = (GEN)x[7]; if (typ(x)!=t_VEC || lg(x)!=10) break;
          return x;
        case 7 : *t = typ_BNR;
          x = (GEN)x[1]; if (typ(x)!=t_VEC || lg(x)!=11) break;
          x = (GEN)x[7]; if (typ(x)!=t_VEC || lg(x)!=10) break;
          return x;
        case 9 :
          x = (GEN)x[2];
          if (typ(x) == t_VEC && lg(x) == 4) *t = typ_GAL;
	  return NULL;
        case 14: case 20:
          *t = typ_ELL; return NULL;
      }break;
    case t_MAT:
      if (lg(x)==2)
        switch(lg(x[1]))
        {
          case 8: case 11:
            *t = typ_CLA; return NULL;
        }
  }
  *t = typ_NULL; return NULL;
}

/*************************************************************************/
/**									**/
/**			       GALOIS GROUP   				**/
/**									**/
/*************************************************************************/

/* exchange elements i and j in vector x */
static GEN
transroot(GEN x, int i, int j)
{
  long k;
  x = dummycopy(x);
  k=x[i]; x[i]=x[j]; x[j]=k; return x;
}

#define randshift (BITS_IN_RANDOM - 3)

GEN
tschirnhaus(GEN x)
{
  long a, v = varn(x), av = avma;
  GEN u, p1 = cgetg(5,t_POL);

  if (typ(x)!=t_POL) err(notpoler,"tschirnhaus");
  if (lgef(x) < 4) err(constpoler,"tschirnhaus");
  if (v) { u=dummycopy(x); setvarn(u,0); x=u; }
  p1[1] = evalsigne(1)|evalvarn(0)|evallgef(5);
  do
  {
    a = mymyrand() >> randshift; if (a==0) a =1; p1[4]=lstoi(a);
    a = mymyrand() >> (randshift-1); if (a>=4) a-=8; p1[3]=lstoi(a);
    a = mymyrand() >> (randshift-1); if (a>=4) a-=8; p1[2]=lstoi(a);
    u = caract2(x,p1,v); a=avma;
  }
  while (lgef(srgcd(u,derivpol(u))) > 3); /* while u not separable */
  if (DEBUGLEVEL>1)
    fprintferr("Tschirnhaus transform. New pol: %Z",u);
  avma=a; return gerepileupto(av,u);
}
#undef randshift

int
gpolcomp(GEN p1, GEN p2)
{
  int s,j = lgef(p1)-2;

  if (lgef(p2)-2 != j)
    err(bugparier,"gpolcomp (different degrees)");
  for (; j>=2; j--)
  {
    s = absi_cmp((GEN)p1[j], (GEN)p2[j]);
    if (s) return s;
  }
  return 0;
}

/* assume pol in Z[X] */
GEN
primitive_pol_to_monic(GEN pol, GEN *ptlead)
{
  long i,j,n = lgef(pol)-3;
  GEN lead,fa,e,a, POL = dummycopy(pol);

  a = POL + 2; lead = (GEN)a[n];
  if (signe(lead) < 0) { POL = gneg_i(POL); a = POL+2; lead = negi(lead); }
  if (is_pm1(lead)) { if (ptlead) *ptlead = NULL; return POL; }
  fa = auxdecomp(lead,0); lead = gun;
  e = (GEN)fa[2]; fa = (GEN)fa[1];
  for (i=lg(e)-1; i>0;i--) e[i] = itos((GEN)e[i]);
  for (i=lg(fa)-1; i>0; i--)
  {
    GEN p = (GEN)fa[i], p1,pk,pku;
    long k = (long)ceil((double)e[i] / n);
    long d = k * n - e[i], v, j0;
    /* find d, k such that  p^d pol(x / p^k) monic */
    for (j=n-1; j>0; j--)
    {
      if (!signe(a[j])) continue;
      v = pvaluation((GEN)a[j], p, &p1);
      while (v + d < k * j) { k++; d += n; }
    }
    pk = gpowgs(p,k); j0 = d/k;
    pku = gpowgs(p,d - k*j0);
    /* a[j] *= p^(d - kj) */
    for (j=j0; j>=0; j--)
    {
      if (j < j0) pku = mulii(pku, pk);
      a[j] = lmulii((GEN)a[j], pku);
    }
    j0++;
    pku = gpowgs(p,k*j0 - d);
    /* a[j] /= p^(kj - d) */
    for (j=j0; j<=n; j++)
    {
      if (j > j0) pku = mulii(pku, pk);
      a[j] = ldivii((GEN)a[j], pku);
    }
    lead = mulii(lead, pk);
  }
  if (ptlead) *ptlead = lead; return POL;
}

/* compute x1*x2^2 + x2*x3^2 + x3*x4^2 + x4*x1^2 */
static GEN
get_F4(GEN x)
{
  GEN p1=gzero;
  long i;

  for (i=1; i<=4; i++)
    p1 = gadd(p1, gmul((GEN)x[i], gsqr((GEN)x[(i&3)+1])));
  return p1;
}

GEN galoisbig(GEN x, long prec);
GEN roots_to_pol(GEN a, long v);

GEN
galois(GEN x, long prec)
{
  long av=avma,av1,i,j,k,n,f,l,l2,e,e1,pr,ind;
  GEN x1,p1,p2,p3,p4,p5,p6,w,y,z,ee;
  static int ind5[20]={2,5,3,4, 1,3,4,5, 1,5,2,4, 1,2,3,5, 1,4,2,3};
  static int ind6[60]={3,5,4,6, 2,6,4,5, 2,3,5,6, 2,4,3,6, 2,5,3,4,
                       1,4,5,6, 1,5,3,6, 1,6,3,4, 1,3,4,5, 1,6,2,5,
                       1,2,4,6, 1,5,2,4, 1,3,2,6, 1,2,3,5, 1,4,2,3};
  if (typ(x)!=t_POL) err(notpoler,"galois");
  n=lgef(x)-3; if (n<=0) err(constpoler,"galois");
  if (n>11) err(impl,"galois of degree higher than 11");
  x = gdiv(x,content(x));
  for (i=2; i<=n+2; i++)
    if (typ(x[i])!=t_INT) err(polrationer,"galois");
  if (gisirreducible(x) != gun)
    err(impl,"galois of reducible polynomial");

  if (n<4)
  {
    if (n<3)
    {
      avma=av; y=cgetg(4,t_VEC);
      y[1] = (n==1)? un: deux;
      y[2]=lnegi(gun);
    }
    else /* n=3 */
    {
      f=carreparfait(discsr(x));
      avma=av; y=cgetg(4,t_VEC);
      if (f) { y[1]=lstoi(3); y[2]=un; }
      else   { y[1]=lstoi(6); y[2]=lnegi(gun); }
    }
    y[3]=un; return y;
  }
  x1 = x = primitive_pol_to_monic(x,NULL); av1=avma;
  if (n>7) return galoisbig(x,prec);
  for(;;)
  {
    switch(n)
    {
      case 4: z = cgetg(7,t_VEC);
        for(;;)
	{
	  p1=roots(x,prec);
          z[1] = (long)get_F4(p1);
          z[2] = (long)get_F4(transroot(p1,1,2));
          z[3] = (long)get_F4(transroot(p1,1,3));
          z[4] = (long)get_F4(transroot(p1,1,4));
          z[5] = (long)get_F4(transroot(p1,2,3));
          z[6] = (long)get_F4(transroot(p1,3,4));
          p4 = roots_to_pol(z,0);
          p5=grndtoi(greal(p4),&e);
          e1=gexpo(gimag(p4)); if (e1>e) e=e1;
          if (e <= -10) break;
	  prec = (prec<<1)-2;
	}
	p6 = modulargcd(p5, derivpol(p5));
	if (typ(p6)==t_POL && lgef(p6)>3) goto tchi;
	p2 = (GEN)factor(p5)[1];
	switch(lg(p2)-1)
	{
	  case 1: f=carreparfait(discsr(x)); avma=av; y=cgetg(4,t_VEC);
	    y[3]=un;
	    if (f) { y[2]=un; y[1]=lstoi(12); return y; }
	    y[2]=lnegi(gun); y[1]=lstoi(24); return y;

	  case 2: avma=av; y=cgetg(4,t_VEC);
	    y[3]=un; y[2]=lnegi(gun); y[1]=lstoi(8); return y;
	
	  case 3: avma=av; y=cgetg(4,t_VEC);
	    y[1]=lstoi(4); y[3]=un;
	    y[2] = (lgef(p2[1])==5)? un: lnegi(gun);
	    return y;

	  default: err(bugparier,"galois (bug1)");
	}

      case 5: z = cgetg(7,t_VEC);
        ee = new_chunk(7); w = new_chunk(7);
        for(;;)
	{
          for(;;)
	  {
	    p1=roots(x,prec);
	    for (l=1; l<=6; l++)
	    {
	      p2=(l==1)?p1: ((l<6)?transroot(p1,1,l): transroot(p1,2,5));
	      p3=gzero;
              for (k=0,i=1; i<=5; i++,k+=4)
	      {
		p5 = gadd(gmul((GEN)p2[ind5[k]],(GEN)p2[ind5[k+1]]),
		          gmul((GEN)p2[ind5[k+2]],(GEN)p2[ind5[k+3]]));
		p3 = gadd(p3, gmul(gsqr((GEN)p2[i]),p5));
	      }
	      w[l]=lrndtoi(greal(p3),&e);
              e1 = gexpo(gimag(p3)); if (e1>e) e=e1;
              ee[l]=e; z[l] = (long)p3;
	    }
            p4 = roots_to_pol(z,0);
	    p5=grndtoi(greal(p4),&e);
            e1 = gexpo(gimag(p4)); if (e1>e) e=e1;
            if (e <= -10) break;
	    prec = (prec<<1)-2;
	  }
	  p6 = modulargcd(p5,derivpol(p5));
	  if (typ(p6)==t_POL && lgef(p6)>3) goto tchi;
	  p3=(GEN)factor(p5)[1];
	  f=carreparfait(discsr(x));
	  if (lg(p3)-1==1)
	  {
	    avma=av; y=cgetg(4,t_VEC); y[3]=un;
	    if (f) { y[2]=un; y[1]=lstoi(60); return y; }
	    else { y[2]=lneg(gun); y[1]=lstoi(120); return y; }
	  }
	  if (!f)
	  {
	    avma=av; y=cgetg(4,t_VEC);
	    y[3]=un; y[2]=lneg(gun); y[1]=lstoi(20); return y;
	  }
          pr = - (bit_accuracy(prec) >> 1);
          for (l=1; l<=6; l++)
	    if (ee[l] <= pr && gcmp0(poleval(p5,(GEN)w[l]))) break;
	  if (l>6) err(bugparier,"galois (bug4)");
	  p2=(l==6)? transroot(p1,2,5):transroot(p1,1,l);
	  p3=gzero;
	  for (i=1; i<=5; i++)
	  {
	    j=(i%5)+1;
	    p3=gadd(p3,gmul(gmul((GEN)p2[i],(GEN)p2[j]),
			    gsub((GEN)p2[j],(GEN)p2[i])));
	  }
	  p5=gsqr(p3); p4=grndtoi(greal(p5),&e);
          e1 = gexpo(gimag(p5)); if (e1>e) e=e1;
	  if (e <= -10)
	  {
	    if (gcmp0(p4)) goto tchi;
	    f=carreparfait(p4); avma=av; y=cgetg(4,t_VEC);
	    y[3]=y[2]=un; y[1]=lstoi(f?5:10);
	    return y;
	  }
	  prec=(prec<<1)-2;
	}

      case 6: z = cgetg(7, t_VEC);
        for(;;)
	{
          for(;;)
	  {
	    p1=roots(x,prec);
	    for (l=1; l<=6; l++)
	    {
	      p2=(l==1)?p1:transroot(p1,1,l);
	      p3=gzero; k=0;
              for (i=1; i<=5; i++) for (j=i+1; j<=6; j++)
	      {
		p5=gadd(gmul((GEN)p2[ind6[k]],(GEN)p2[ind6[k+1]]),
		        gmul((GEN)p2[ind6[k+2]],(GEN)p2[ind6[k+3]]));
		p3=gadd(p3,gmul(gsqr(gmul((GEN)p2[i],(GEN)p2[j])),p5)); k+=4;
	      }
	      z[l] = (long)p3;
	    }
            p4=roots_to_pol(z,0);
	    p5=grndtoi(greal(p4),&e);
            e1 = gexpo(gimag(p4)); if (e1>e) e=e1;
            if (e <= -10) break;
	    prec=(prec<<1)-2;
	  }
	  p6 = modulargcd(p5,derivpol(p5));
	  if (typ(p6)==t_POL && lgef(p6)>3) goto tchi;
	  p2=(GEN)factor(p5)[1];
	  switch(lg(p2)-1)
	  {
	    case 1:
              z = cgetg(11,t_VEC); ind=0;
	      p3=gadd(gmul(gmul((GEN)p1[1],(GEN)p1[2]),(GEN)p1[3]),
	              gmul(gmul((GEN)p1[4],(GEN)p1[5]),(GEN)p1[6]));
              z[++ind] = (long)p3;
	      for (i=1; i<=3; i++)
		for (j=4; j<=6; j++)
		{
		  p2=transroot(p1,i,j);
		  p3=gadd(gmul(gmul((GEN)p2[1],(GEN)p2[2]),(GEN)p2[3]),
		          gmul(gmul((GEN)p2[4],(GEN)p2[5]),(GEN)p2[6]));
		  z[++ind] = (long)p3;
		}
              p4 = roots_to_pol(z,0);
	      p5=grndtoi(greal(p4),&e);
              e1 = gexpo(gimag(p4)); if (e1>e) e=e1;
	      if (e <= -10)
	      {
		p6 = modulargcd(p5,derivpol(p5));
		if (typ(p6)==t_POL && lgef(p6)>3) goto tchi;
		p2=(GEN)factor(p5)[1];
		f=carreparfait(discsr(x));
		avma=av; y=cgetg(4,t_VEC); y[3]=un;
		if (lg(p2)-1==1)
		{
		  if (f) { y[2]=un; y[1]=lstoi(360); }
		  else { y[2]=lnegi(gun); y[1]=lstoi(720); }
		}
		else
		{
		  if (f) { y[2]=un; y[1]=lstoi(36); }
		  else { y[2]=lnegi(gun); y[1]=lstoi(72); }
		}
                return y;
	      }
	      prec=(prec<<1)-2; break;
		
	    case 2: l2=lgef(p2[1])-3; if (l2>3) l2=6-l2;
	      switch(l2)
	      {
		case 1: f=carreparfait(discsr(x));
		  avma=av; y=cgetg(4,t_VEC); y[3]=un;
		  if (f) { y[2]=un; y[1]=lstoi(60); }
		  else { y[2]=lneg(gun); y[1]=lstoi(120); }
		  return y;
		case 2: f=carreparfait(discsr(x));
		  if (f)
		  {
		    avma=av; y=cgetg(4,t_VEC);
		    y[3]=y[2]=un; y[1]=lstoi(24);
		  }
		  else
		  {
		    p3=(lgef(p2[1])==5) ? (GEN)p2[2]:(GEN)p2[1];
		    f=carreparfait(discsr(p3));
		    avma=av; y=cgetg(4,t_VEC); y[2]=lneg(gun);
		    if (f) { y[1]=lstoi(24); y[3]=deux; }
		    else { y[1]=lstoi(48); y[3]=un; }
		  }
		  return y;
		case 3: f=carreparfait(discsr((GEN)p2[1]))
		       || carreparfait(discsr((GEN)p2[2]));
		  avma=av; y=cgetg(4,t_VEC);
		  y[3]=un; y[2]=lneg(gun); y[1]=lstoi(f? 18: 36);
		  return y;
	      }
	    case 3:
	      for (l2=1; l2<=3; l2++)
		if (lgef(p2[l2])>=6) p3=(GEN)p2[l2];
	      if (lgef(p3)==6)
	      {
		f=carreparfait(discsr(p3)); avma=av; y=cgetg(4,t_VEC);
                y[2]=lneg(gun); y[1]=lstoi(f? 6: 12);
	      }
	      else
	      {
		f=carreparfait(discsr(x)); avma=av; y=cgetg(4,t_VEC);
		if (f) { y[2]=un; y[1]=lstoi(12); }
		else { y[2]=lneg(gun); y[1]=lstoi(24); }
	      }
              y[3]=un; return y;
	    case 4: avma=av; y=cgetg(4,t_VEC);
	      y[1]=lstoi(6); y[2]=lneg(gun); y[3]=deux; return y;
            default: err(bugparier,"galois (bug3)");
	  }
	}
	
      case 7: z = cgetg(36,t_VEC);
        for(;;)
	{
	  ind = 0; p1=roots(x,prec); p4=gun;
	  for (i=1; i<=5; i++)
	    for (j=i+1; j<=6; j++)
            {
              p6 = gadd((GEN)p1[i],(GEN)p1[j]);
	      for (k=j+1; k<=7; k++)
                z[++ind] = (long) gadd(p6,(GEN)p1[k]);
            }
          p4 = roots_to_pol(z,0);
          p5 = grndtoi(greal(p4),&e);
          e1 = gexpo(gimag(p4)); if (e1>e) e=e1;
	  if (e <= -10) break;
          prec = (prec<<1)-2;
	}
	p6 = modulargcd(p5,derivpol(p5));
	if (typ(p6)==t_POL && lgef(p6)>3) goto tchi;
	p2=(GEN)factor(p5)[1];
	switch(lg(p2)-1)
	{
	  case 1: f=carreparfait(discsr(x)); avma=av; y=cgetg(4,t_VEC); y[3]=un;
	    if (f) { y[2]=un; y[1]=lstoi(2520); }
	    else { y[2]=lneg(gun); y[1]=lstoi(5040); }
	    return y;
	  case 2: f=lgef(p2[1])-3; avma=av; y=cgetg(4,t_VEC); y[3]=un;
	    if (f==7 || f==28) { y[2]=un; y[1]=lstoi(168); }
	    else { y[2]=lneg(gun); y[1]=lstoi(42); }
	    return y;
	  case 3: avma=av; y=cgetg(4,t_VEC);
	    y[3]=y[2]=un; y[1]=lstoi(21); return y;
	  case 4: avma=av; y=cgetg(4,t_VEC);
	    y[3]=un; y[2]=lneg(gun); y[1]=lstoi(14); return y;
	  case 5: avma=av; y=cgetg(4,t_VEC);
	    y[3]=y[2]=un; y[1]=lstoi(7); return y;
          default: err(talker,"galois (bug2)");
	}
    }
    tchi: avma=av1; x=tschirnhaus(x1);
  }
}

GEN
galoisapply(GEN nf, GEN aut, GEN x)
{
  long av=avma,tetpil,lx,j,N;
  GEN p,p1,y,pol;

  nf=checknf(nf); pol=(GEN)nf[1];
  if (typ(aut)==t_POL) aut = gmodulcp(aut,pol);
  else
  {
    if (typ(aut)!=t_POLMOD || !gegal((GEN)aut[1],pol))
      err(talker,"incorrect galois automorphism in galoisapply");
  }
  switch(typ(x))
  {
    case t_INT: case t_INTMOD: case t_FRAC: case t_FRACN: case t_PADIC:
      avma=av; return gcopy(x);

    case t_POLMOD: x = (GEN) x[2]; /* fall through */
    case t_POL:
      p1 = gsubst(x,varn(pol),aut);
      if (typ(p1)!=t_POLMOD || !gegal((GEN)p1[1],pol)) p1 = gmodulcp(p1,pol);
      return gerepileupto(av,p1);

    case t_VEC:
      if (lg(x)==3)
      {
	y=cgetg(3,t_VEC);
	y[1]=(long)galoisapply(nf,aut,(GEN)x[1]);
        y[2]=lcopy((GEN)x[2]); return gerepileupto(av, y);
      }
      if (lg(x)!=6) err(typeer,"galoisapply");
      y=cgetg(6,t_VEC); y[1]=x[1]; y[3]=x[3]; y[4]=x[4];
      p = (GEN)x[1];
      p1=centermod(galoisapply(nf,aut,(GEN)x[2]), p);
      if (is_pm1(x[3]))
	if (ggval(subres(gmul((GEN)nf[7],p1),pol), p) > itos((GEN)x[4]))
	  p1[1] =  (signe(p1[1]) > 0)? lsub((GEN)p1[1], p)
	                             : ladd((GEN)p1[1], p);
      y[2]=(long)p1;
      y[5]=(long)centermod(galoisapply(nf,aut,(GEN)x[5]), p);
      tetpil=avma; return gerepile(av,tetpil,gcopy(y));

    case t_COL:
      N=lgef(pol)-3;
      if (lg(x)!=N+1) err(typeer,"galoisapply");
      p1=galoisapply(nf,aut,gmul((GEN)nf[7],x)); tetpil=avma;
      return gerepile(av,tetpil,algtobasis(nf,p1));

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      N=lgef(pol)-3;
      if (lg(x[1])!=N+1) err(typeer,"galoisapply");
      p1=cgetg(lx,t_MAT);
      for (j=1; j<lx; j++) p1[j]=(long)galoisapply(nf,aut,(GEN)x[j]);
      if (lx==N+1) p1 = idealhermite(nf,p1);
      return gerepileupto(av,p1);
  }
  err(typeer,"galoisapply");
  return NULL; /* not reached */
}

GEN pol_to_monic(GEN pol, GEN *lead);
int cmp_pol(GEN x, GEN y);

static GEN
get_nfpol(GEN x, GEN *nf)
{
  if (typ(x) == t_POL) { *nf = NULL; return x; }
  *nf = checknf(x); return (GEN)(*nf)[1];
}

/* if fliso test for isomorphism, for inclusion otherwise. */
static GEN
nfiso0(GEN a, GEN b, long fliso)
{
  long av=avma,tetpil,n,m,i,vb,lx;
  GEN nfa,nfb,p1,y,la,lb;

  a = get_nfpol(a, &nfa);
  b = get_nfpol(b, &nfb);
  if (fliso && nfa && !nfb) { p1=a; a=b; b=p1; p1=nfa; nfa=nfb; nfb=p1; }
  m=lgef(a)-3;
  n=lgef(b)-3; if (m<=0 || n<=0) err(constpoler,"nfiso or nfincl");
  if (fliso)
    { if (n!=m) return gzero; }
  else
    { if (n%m) return gzero; }

  if (nfb) lb = NULL; else b = pol_to_monic(b,&lb);
  if (nfa) la = NULL; else a = pol_to_monic(a,&la);
  if (nfa && nfb)
  {
    if (fliso)
    {
      if (!gegal((GEN)nfa[2],(GEN)nfb[2])
       || !gegal((GEN)nfa[3],(GEN)nfb[3])) return gzero;
    }
    else
      if (!divise((GEN)nfb[3], gpowgs((GEN)nfa[3],n/m))) return gzero;
  }
  else
  {
    GEN da = nfa? (GEN)nfa[3]: discsr(a);
    GEN db = nfb? (GEN)nfb[3]: discsr(b);
    if (fliso)
    {
      p1=gdiv(da,db);
      if (typ(p1)==t_FRAC) p1=mulii((GEN)p1[1],(GEN)p1[2]);
      if (!gcarreparfait(p1)) { avma=av; return gzero; }
    }
    else
    {
      long q=n/m;
      GEN fa=factor(da), ex=(GEN)fa[2];
      fa=(GEN)fa[1]; lx=lg(fa);
      for (i=1; i<lx; i++)
        if (mod2((GEN)ex[i]) && !divise(db,gpowgs((GEN)fa[i],q)))
          { avma=av; return gzero; }
    }
  }
  a = dummycopy(a); setvarn(a,0);
  b = dummycopy(b); vb=varn(b);
  if (nfb)
  {
    if (vb == 0) nfb = gsubst(nfb, 0, polx[MAXVARN]);
    y = lift_intern(nfroots(nfb,a));
  }
  else
  {
    if (vb == 0) setvarn(b, fetch_var());
    y = (GEN)polfnf(a,b)[1]; lx = lg(y);
    for (i=1; i<lx; i++)
    {
      if (lgef(y[i]) != 4) { setlg(y,i); break; }
      y[i] = (long)gneg_i(lift_intern(gmael(y,i,2)));
    }
    y = gen_sort(y, 0, cmp_pol);
    settyp(y, t_VEC);
    if (vb == 0) delete_var();
  }
  lx = lg(y); if (lx==1) { avma=av; return gzero; }
  for (i=1; i<lx; i++)
  {
    p1 = (GEN)y[i];
    if (typ(p1) == t_POL) setvarn(p1, vb); else p1 = scalarpol(p1, vb);
    if (lb) p1 = poleval(p1, gmul(polx[vb],lb));
    y[i] = la? ldiv(p1,la): (long)p1;
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
}

GEN
nfisisom(GEN a, GEN b)
{
  return nfiso0(a,b,1);
}

GEN
nfisincl(GEN a, GEN b)
{
  return nfiso0(a,b,0);
}

/*************************************************************************/
/**									**/
/**			       INITALG					**/
/**									**/
/*************************************************************************/
extern GEN LLL_nfbasis(GEN *x, GEN polr, GEN base, long prec);
extern GEN eleval(GEN f,GEN h,GEN a);
extern int canon_pol(GEN z);
extern GEN mat_to_vecpol(GEN x, long v);
extern GEN vecpol_to_mat(GEN v, long n);

/* For internal use. compute trace(x mod pol), sym=polsym(pol,deg(pol)-1) */
GEN
quicktrace(GEN x, GEN sym)
{
  GEN p1 = gzero;
  long i;

  if (signe(x))
  {
    sym--;
    for (i=lgef(x)-1; i>1; i--)
      p1 = gadd(p1, gmul((GEN)x[i],(GEN)sym[i]));
  }
  return p1;
}

/* T = trace(w[i]), x = sum x[i] w[i], x[i] integer */
static GEN
trace_col(GEN x, GEN T)
{
  GEN t = gzero;
  long i, l = lg(x);

  t = mulii((GEN)x[1],(GEN)T[1]);
  for (i=2; i<l; i++)
    if (signe(x[i])) t = addii(t, mulii((GEN)x[i],(GEN)T[i]));
  return t;
}

/* Seek a new, simpler, polynomial pol defining the same number field as
 * x (assumed to be monic at this point).
 * *ptx   receives pol
 * *ptdx  receives disc(pol)
 * *ptrev expresses the new root in terms of the old one.
 * base updated in place.
 * prec = 0 <==> field is totally real
 */
static void
nfinit_reduce(long flag, GEN *px, GEN *pdx, GEN *prev, GEN *pbase, long prec)
{
  GEN chbas,a,phimax,dxn,s,sn,p1,p2,p3,polmax,rev,polr;
  GEN x = *px, dx = *pdx, base = *pbase;
  long i,j,nmax,numb,flc,v=varn(x), n=lg(base)-1;

  if (n == 1)
  {
    *px = gsub(polx[v],gun); *pdx = gun;
    *prev = polymodrecip(gmodulcp(gun, x)); return;
  }
  polr = prec? roots(x, prec): NULL;
  if (polr)
    for (s=gzero,i=1; i<=n; i++) s = gadd(s,gnorm((GEN)polr[i]));
  else
    s = subii(sqri((GEN)x[n+1]), shifti((GEN)x[n],1));
    
  chbas = LLL_nfbasis(&x,polr,base,prec);
  if (DEBUGLEVEL) msgtimer("LLL basis");

  phimax=polx[v]; polmax=dummycopy(x);
  nmax=(flag & nf_PARTIAL)?min(n,3):n;

  for (numb=0,i=2; i<=nmax || (!numb && i<=n); i++)
  { /* cf pols_for_polred */
    if (DEBUGLEVEL>2) { fprintferr("i = %ld\n",i); flusherr(); }
    p1 = a = gmul(base,(GEN)chbas[i]); p3=content(p1);
    if (gcmp1(p3)) p3 = NULL; else p1 = gdiv(p1,p3);
    p1 = caract2(x,p1,v);
    if (p3)
      for (p2=gun, j=lgef(p1)-2; j>=2; j--)
      {
        p2 = gmul(p2,p3); p1[j] = lmul((GEN)p1[j], p2);
      }
    p2 = modulargcd(derivpol(p1),p1);
    if (lgef(p2) > 3) continue;

    if (DEBUGLEVEL>3) outerr(p1);
    dxn=discsr(p1); flc=absi_cmp(dxn,dx); numb++;
    if (flc>0) continue;

    if (polr)
      for (sn=gzero,j=1; j<=n; j++)
        sn = gadd(sn,gnorm(poleval(a,(GEN)polr[j])));
    else
      sn = subii(sqri((GEN)p1[n+1]), shifti((GEN)p1[n],1));
    if (flc>=0)
    {
      flc=gcmp(sn,s);
      if (flc>0 || (!flc && gpolcomp(p1,polmax) >= 0)) continue;
    }
    dx=dxn; s=sn; polmax=p1; phimax=a;
  }
  if (!numb) 
  {
    if (gisirreducible(x)!=gun) err(redpoler,"nfinit_reduce");
    err(talker,"you have found a counter-example to a conjecture, "
               "please send us\nthe polynomial as soon as possible");
  }
  if (phimax == polx[v]) /* no improvement */
    rev = gmodulcp(phimax,x);
  else
  {
    if (canon_pol(polmax) < 0) phimax = gneg_i(phimax);
    if (DEBUGLEVEL>1) fprintferr("polmax = %Z\n",polmax);
    p2 = gmodulcp(phimax,x); rev = polymodrecip(p2);
    a = base; base = cgetg(n+1,t_VEC);
    p1 = (GEN)rev[2];
    for (i=1; i<=n; i++)
      base[i] = (long)eleval(polmax, (GEN)a[i], p1);
    p1 = vecpol_to_mat(base,n); p2=denom(p1); p1=gmul(p2,p1);
    p1 = gdiv(hnfmodid(p1,p2), p2);
    base = mat_to_vecpol(p1,v);
  }
  *px=polmax; *pdx=dx; *prev=rev; *pbase = base;
}

/* pol belonging to Z[x], return a monic polynomial generating the same field
 * as pol (x-> ax+b)) set lead = NULL if pol was monic (after dividing
 * by the content), and to to leading coeff otherwise.
 * No garbage collecting done.
 */
GEN
pol_to_monic(GEN pol, GEN *lead)
{
  long n = lgef(pol)-1;
  GEN p1;

  if (n==1 || gcmp1((GEN)pol[n])) { *lead = NULL; return pol; }

  p1=content(pol); if (!gcmp1(p1)) pol = gdiv(pol,p1);
  return primitive_pol_to_monic(pol,lead);
}

/* NB: TI integral, det(TI) = d_K, ideal/dideal = codifferent */
GEN
make_MDI(GEN nf, GEN TI, GEN *ideal, GEN *dideal)
{
  GEN c = content(TI);
  GEN p1;

  *dideal = divii((GEN)nf[3], c);
  *ideal = p1 = hnfmodid(gdiv(TI,c), *dideal);
  return gmul(c, ideal_two_elt(nf, p1));
}

/* [bas[i]/den[i]]= integer basis. roo = real part of the roots */
GEN
make_M(GEN basden,GEN roo)
{
  GEN p1,d,M, bas=(GEN)basden[1], den=(GEN)basden[2];
  long i,j, ru = lg(roo), n = lg(bas);
  M = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    p1=cgetg(ru,t_COL); M[j]=(long)p1;
    for (i=1; i<ru; i++)
      p1[i]=(long)poleval((GEN)bas[j],(GEN)roo[i]);
  }
  if (den)
  {
    long prec = precision((GEN)roo[1]);
    GEN invd,rd = cgetr(prec+1);
    for (j=1; j<n; j++)
    {
      d = (GEN)den[j]; if (!d) continue;
      p1 = (GEN)M[j]; affir(d,rd); invd = ginv(rd);
      for (i=1; i<ru; i++) p1[i] = lmul((GEN)p1[i], invd);
    }
  }
  if (DEBUGLEVEL>4) msgtimer("matrix M");
  return M;
}

GEN
make_MC(long r1,GEN M)
{
  long i,j,av,tetpil, n = lg(M), ru = lg(M[1]);
  GEN p1,p2,MC=cgetg(ru,t_MAT);

  for (j=1; j<ru; j++)
  {
    p1=cgetg(n,t_COL); MC[j]=(long)p1;
    for (i=1; i<n; i++)
    {
      av=avma; p2=gconj(gcoeff(M,j,i)); tetpil=avma;
      p1[i] = (j<=r1)? (long)p2: lpile(av,tetpil,gmul2n(p2,1));
    }
  }
  if (DEBUGLEVEL>4) msgtimer("matrix MC");
  return MC;
}

GEN
get_roots(GEN x,long r1,long ru,long prec)
{
  GEN roo = (typ(x)==t_VEC)? dummycopy(x): roots(x,prec);
  long i;

  for (i=1; i<=r1; i++) roo[i]=lreal((GEN)roo[i]);
  for (   ; i<=ru; i++) roo[i]=roo[(i<<1)-r1];
  roo[0]=evaltyp(t_VEC)|evallg(ru+1); return roo;
}

/* assume lg(nf) > 3 && typ(nf) = container [hopefully a genuine nf] */
long
nf_get_r1(GEN nf)
{
  GEN x = (GEN)nf[2];
  if (typ(x) != t_VEC || lg(x) != 3 || typ(x[1]) != t_INT)
    err(talker,"false nf in nf_get_r1");
  return itos((GEN)x[1]);
}
long
nf_get_r2(GEN nf)
{
  GEN x = (GEN)nf[2];
  if (typ(x) != t_VEC || lg(x) != 3 || typ(x[2]) != t_INT)
    err(talker,"false nf in nf_get_r2");
  return itos((GEN)x[2]);
}

extern GEN mulmat_pol(GEN A, GEN x);

static GEN
get_T(GEN mul, GEN x, GEN bas, GEN den)
{
  long i,j,n = lg(bas)-1;
  GEN tr,T,T1,sym;
  T = cgetg(n+1,t_MAT);
  T1 = cgetg(n+1,t_COL);
  sym = polsym(x, n-1);

  T1[1]=lstoi(n);
  for (i=2; i<=n; i++)
  {
    tr = quicktrace((GEN)bas[i], sym);
    if (den && den[i]) tr = gdivexact(tr,(GEN)den[i]);
    T1[i] = (long)tr; /* tr(w[i]) */
  }
  T[1] = (long)T1;
  for (i=2; i<=n; i++)
  {
    T[i] = lgetg(n+1,t_COL); coeff(T,1,i) = T1[i];
    for (j=2; j<=i; j++)
      coeff(T,i,j) = coeff(T,j,i) = (long)trace_col((GEN)mul[j+(i-1)*n], T1);
  }
  return T;
}

/* return [bas[i]*denom(bas[i]), denom(bas[i])], denom 1 is given as NULL */
GEN
get_bas_den(GEN bas)
{
  GEN z,d,den, dbas = dummycopy(bas);
  long i, c = 0, l = lg(bas);
  den = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    d = denom(content((GEN)dbas[i]));
    if (is_pm1(d)) d = NULL; else { dbas[i] = lmul((GEN)dbas[i],d); c++; }
    den[i] = (long)d;
  }
  if (!c) den = NULL; /* power basis */
  z = cgetg(3,t_VEC);
  z[1] = (long)dbas;
  z[2] = (long)den; return z;
}

/* allow x or y = NULL (act as 1) */
static GEN
_mulii(GEN x, GEN y)
{
  if (!x) return y;
  if (!y) return x;
  return mulii(x,y);
}

GEN
get_mul_table(GEN x,GEN basden,GEN invbas,GEN *T)
{
  long i,j, n = lgef(x)-3;
  GEN z,d, mul = cgetg(n*n+1,t_MAT), bas=(GEN)basden[1], den=(GEN)basden[2];
  
  for (j=1; j<=n*n; j++) mul[j]=lgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
    for (j=i; j<=n; j++)
    {
      z = gres(gmul((GEN)bas[j],(GEN)bas[i]), x);
      z = mulmat_pol(invbas, z); /* integral column */
      if (den)
      {
        d = _mulii((GEN)den[i], (GEN)den[j]);
        if (d) z = gdivexact(z, d);
      }
      mul[j+(i-1)*n] = mul[i+(j-1)*n] = (long)z;
    }
  if (T) *T = get_T(mul,x,bas,den);
  return mul;
}

/* fill mat = nf[5], as well as nf[8] and nf[9]
 * If (small) only compute a subset (use dummy 0s for the rest) */
void
get_nf_matrices(GEN nf, long small)
{
  GEN x=(GEN)nf[1],dK=(GEN)nf[3],index=(GEN)nf[4],ro=(GEN)nf[6],bas=(GEN)nf[7];
  GEN basden,mul,invbas,M,MC,T,MDI,D,TI,A,dA,mat;
  long r1 = nf_get_r1(nf), n = lg(bas)-1;

  mat = cgetg(small? 4: 8,t_VEC); nf[5] = (long)mat;
  basden = get_bas_den(bas);
  M = make_M(basden,ro);
  MC = make_MC(r1,M);
  mat[1]=(long)M;
  mat[3]=(long)mulmat_real(MC,M);
  if (small) { nf[8]=nf[9]=mat[2]=zero; return; }

  invbas = invmat(vecpol_to_mat(bas,n));
  mul = get_mul_table(x,basden,invbas,&T);
  if (DEBUGLEVEL) msgtimer("mult. table");
  
  nf[8]=(long)invbas;
  nf[9]=(long)mul;

  TI = gauss(T, gscalmat(dK, n));
  MDI = make_MDI(nf,TI, &A, &dA);
  mat[6]=(long)TI;
  mat[7]=(long)MDI; /* needed in idealinv below */
  if (is_pm1(index))
    D = idealhermite_aux(nf, derivpol(x));
  else
    D = gmul(dA, idealinv(nf, A));
  mat[2]=(long)MC;
  mat[4]=(long)T;
  mat[5]=(long)D;
  if (DEBUGLEVEL) msgtimer("matrices");
}

/* Initialize the number field defined by the polynomial x (in variable v)
 * flag & nf_REGULAR
 *    regular behaviour.
 * flag & nf_SMALL
 *    compute only nf[1] (pol), nf[2] (signature), nf[5][3] (T2) and
 *    nf[7] (integer basis), the other components are filled with gzero.
 * flag & nf_REDUCE
 *    try a polred first.
 * flag & nf_PARTIAL
 *    do a partial polred, not a polredabs
 * flag & nf_ORIG
 *    do a polred and return [nfinit(x),Mod(a,red)], where
 *    Mod(a,red)=Mod(v,x) (i.e return the base change).
 */

/* here x can be a polynomial, an nf or a bnf */
GEN
initalgall0(GEN x, long flag, long prec)
{
  GEN lead = NULL,nf,ro,bas,mat,rev,dK,dx,index,res;
  long av=avma,n,i,r1,r2,ru,PRECREG;

  if (DEBUGLEVEL) timer2();
  if (typ(x)==t_POL)
  {
    n=lgef(x)-3; if (n<=0) err(constpoler,"initalgall0");
    check_pol_int(x);
    if (gisirreducible(x) == gzero) err(redpoler,"nfinit");
    if (!gcmp1((GEN)x[n+2]))
    {
      x = pol_to_monic(x,&lead);
      if (!(flag & nf_SMALL))
      {
        if (!(flag & nf_REDUCE))
          err(warner,"non-monic polynomial. Result of the form [nf,c]");
        flag = flag | nf_REDUCE | nf_ORIG;
      }
    }
    bas = allbase4(x,0,&dK,NULL);
    if (DEBUGLEVEL) msgtimer("round4");
    dx = discsr(x); r1 = sturm(x);
  }
  else
  {
    i = lg(x);
    if (typ(x) == t_VEC && i<=4 && i>=3 && typ(x[1])==t_POL)
    { /* polynomial + integer basis */
      bas=(GEN)x[2]; x=(GEN)x[1]; n=lgef(x)-3;
      if (typ(bas) == t_MAT) { mat = bas; bas = mat_to_vecpol(mat,varn(x)); }
      else mat = vecpol_to_mat(bas,n);
      dx = discsr(x); r1 = sturm(x);
      dK = gmul(dx, gsqr(det2(mat)));
    }
    else
    {
      nf=checknf(x);
      bas=(GEN)nf[7]; x=(GEN)nf[1]; n=lgef(x)-3;
      dK=(GEN)nf[3]; dx=mulii(dK, sqri((GEN)nf[4]));
      r1 = nf_get_r1(nf);
    }
    bas[1]=lpolun[varn(x)]; /* it may be gun => SEGV later */
  }
  r2=(n-r1)>>1; ru=r1+r2;
  PRECREG = prec + (expi(dK)>>(TWOPOTBITS_IN_LONG+1))
                 + (long)((sqrt((double)n)+3) / sizeof(long) * 4);
  rev = NULL;
  if (flag & nf_REDUCE)
  {
    nfinit_reduce(flag, &x, &dx, &rev, &bas, r1==n? 0: prec);
    if (DEBUGLEVEL) msgtimer("polred");
  }
  if (!carrecomplet(divii(dx,dK),&index))
    err(bugparier,"nfinit (incorrect discriminant)");

  ro=get_roots(x,r1,ru,PRECREG);
  if (DEBUGLEVEL) msgtimer("roots");

  nf=cgetg(10,t_VEC);
  nf[1]=(long)x;
  nf[2]=lgetg(3,t_VEC);
  mael(nf,2,1)=lstoi(r1);
  mael(nf,2,2)=lstoi(r2);
  nf[3]=(long)dK;
  nf[4]=(long)index;
  nf[6]=(long)ro;
  nf[7]=(long)bas;
  get_nf_matrices(nf, flag & nf_SMALL);

  if (flag & nf_ORIG)
  {
    if (!rev) err(talker,"bad flag in initalgall0");
    res = cgetg(3,t_VEC);
    res[1]=(long)nf; nf = res;
    res[2]=lead? ldiv(rev,lead): (long)rev;
  }
  return gerepileupto(av, gcopy(nf));
}

GEN
initalgred(GEN x, long prec)
{
  return initalgall0(x,nf_REDUCE,prec);
}

GEN
initalgred2(GEN x, long prec)
{
  return initalgall0(x,nf_REDUCE|nf_ORIG,prec);
}

GEN
nfinit0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0:
    case 1: return initalgall0(x,nf_REGULAR,prec);
    case 2: return initalgall0(x,nf_REDUCE,prec);
    case 3: return initalgall0(x,nf_REDUCE|nf_ORIG,prec);
    case 4: return initalgall0(x,nf_REDUCE|nf_PARTIAL,prec);
    case 5: return initalgall0(x,nf_REDUCE|nf_ORIG|nf_PARTIAL,prec);
    case 6: return initalgall0(x,nf_SMALL,prec);
    default: err(flagerr,"nfinit");
  }
  return NULL; /* not reached */
}

GEN
initalg(GEN x, long prec)
{
  return initalgall0(x,nf_REGULAR,prec);
}

/* assume x a bnr/bnf/nf */
long
nfgetprec(GEN x)
{
  GEN nf = checknf(x), ro = (GEN)nf[6];
  return (typ(ro)==t_VEC)?precision((GEN)ro[1]): DEFAULTPREC;
}

GEN
nfnewprec(GEN nf, long prec)
{
  long av=avma,r1,r2,ru,n;
  GEN y,pol,ro,basden,MC,mat,M;

  if (typ(nf) != t_VEC) err(talker,"incorrect nf in nfnewprec");
  if (lg(nf) == 11) return bnfnewprec(nf,prec);
  if (lg(nf) ==  7) return bnrnewprec(nf,prec);
  (void)checknf(nf);
  y = dummycopy(nf);
  pol=(GEN)nf[1]; n=degree(pol);
  r1 = nf_get_r1(nf);
  r2 = (n - r1) >> 1; ru = r1+r2;
  mat=dummycopy((GEN)nf[5]);
  ro=get_roots(pol,r1,ru,prec);
  y[5]=(long)mat;
  y[6]=(long)ro;
  basden = get_bas_den((GEN)nf[7]);
  M = make_M(basden,ro);
  MC = make_MC(r1,M);
  mat[1]=(long)M;
  if (typ(nf[8]) != t_INT) mat[2]=(long)MC; /* not a small nf */
  mat[3]=(long)mulmat_real(MC,M);
  return gerepileupto(av, gcopy(y));
}

static long
nf_pm1(GEN y)
{
  long i,l;

  if (!is_pm1(y[1])) return 0;
  l = lg(y);
  for (i=2; i<l; i++)
    if (signe(y[i])) return 0;
  return signe(y[1]);

}

static GEN
is_primitive_root(GEN nf, GEN fa, GEN x, long w)
{
  GEN y, exp = stoi(2), pp = (GEN)fa[1];
  long i,p, l = lg(pp);

  for (i=1; i<l; i++)
  {
    p = itos((GEN)pp[i]);
    exp[2] = w / p; y = element_pow(nf,x,exp);
    if (nf_pm1(y) > 0) /* y = 1 */
    {
      if (p!=2 || !gcmp1(gcoeff(fa,i,2))) return NULL;
      x = gneg_i(x);
    }
  }
  return x;
}

GEN
rootsof1(GEN nf)
{
  long av,tetpil,N,k,i,ws,prec;
  GEN algun,p1,y,R1,d,list,w;

  y=cgetg(3,t_VEC); av=avma; nf=checknf(nf);
  R1=gmael(nf,2,1); algun=gmael(nf,8,1);
  if (signe(R1))
  {
    y[1]=deux;
    y[2]=lneg(algun); return y;
  }
  N=lgef(nf[1])-3; prec=gprecision((GEN)nf[6]);
#ifdef LONG_IS_32BIT
  if (prec < 10) prec = 10;
#else
  if (prec < 6) prec = 6;
#endif
  for (i=1; ; i++)
  {
    p1 = fincke_pohst(nf,stoi(N),1000,1,prec,NULL);
    if (p1) break;
    if (i == MAXITERPOL) err(accurer,"rootsof1");
    prec=(prec<<1)-2;
    if (DEBUGLEVEL) err(warnprec,"rootsof1",prec);
    nf=nfnewprec(nf,prec);
  }
  if (itos(ground((GEN)p1[2])) != N) err(bugparier,"rootsof1 (bug1)");
  w=(GEN)p1[1]; ws = itos(w);
  if (ws == 2)
  {
    y[1]=deux; avma=av;
    y[2]=lneg(algun); return y;
  }

  d = decomp(w); list = (GEN)p1[3]; k = lg(list);
  for (i=1; i<k; i++)
  {
    p1 = (GEN)list[i];
    p1 = is_primitive_root(nf,d,p1,ws);
    if (p1)
    {
      tetpil=avma;
      y[2]=lpile(av,tetpil,gcopy(p1));
      y[1]=lstoi(ws); return y;
    }
  }
  err(bugparier,"rootsof1");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     DEDEKIND ZETA FUNCTION                      */
/*                                                                 */
/*******************************************************************/

ulong smulss(ulong x, ulong y, ulong *rem);

static GEN
dirzetak0(GEN nf, long N0)
{
  GEN vect,p1,pol,disc,c,c2;
  long av=avma,i,j,k,limk,lx;
  ulong q,p,rem;
  byteptr d=diffptr;
  long court[] = {evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3),0};

  pol=(GEN)nf[1]; disc=(GEN)nf[4];
  c  = (GEN) gpmalloc((N0+1)*sizeof(long));
  c2 = (GEN) gpmalloc((N0+1)*sizeof(long));
  c2[0]=c[0]=evaltyp(t_VEC) | evallg(N0+1);
  c2[1]=c[1]=1; for (i=2; i<=N0; i++) c[i]=0;
  court[2] = 0;

  while (court[2]<=N0)
  {
    court[2] += *d++; if (! *d) err(primer1);
    if (smodis(disc,court[2])) /* court does not divide index */
      { vect = (GEN) simplefactmod(pol,court)[1]; lx=lg(vect); }
    else
    {
      p1=primedec(nf,court); lx=lg(p1); vect=cgetg(lx,t_COL);
      for (i=1; i<lx; i++) vect[i]=mael(p1,i,4);
    }
    for (j=1; j<lx; j++)
    {
      p1=powgi(court, (GEN)vect[j]); /* p1 = court^f */
      if (cmpis(p1,N0) <= 0)
      {
        q=p=p1[2]; limk=N0/q;
        for (k=2; k<=N0; k++) c2[k]=c[k];
        while (q<=(ulong)N0)
        {
          for (k=1; k<=limk; k++) c2[k*q] += c[k];
          q = smulss(q,p,&rem);
          if (rem) break;
          limk /= p;
        }
        p1=c; c=c2; c2=p1;
      }
    }
    avma=av;
    if (DEBUGLEVEL>6) fprintferr(" %ld",court[2]);
  }
  if (DEBUGLEVEL>6) { fprintferr("\n"); flusherr(); }
  free(c2); return c;
}

GEN
dirzetak(GEN nf, GEN b)
{
  GEN z,c;
  long i;

  if (typ(b)!=t_INT) err(talker,"not an integer type in dirzetak");
  if (signe(b)<=0) return cgetg(1,t_VEC);
  nf = checknf(nf);
  if (is_bigint(b)) err(talker,"too many terms in dirzetak");
  c = dirzetak0(nf,itos(b));
  i = lg(c); z=cgetg(i,t_VEC);
  for (i-- ; i; i--) z[i]=lstoi(c[i]);
  free(c); return z;
}

GEN
initzeta(GEN pol, long prec)
{
  GEN nfz,nf,alpha,beta,mu,gr1,gr2,gru,p1,p2,cst,A0,c0,c1,c2,eps,coef;
  GEN limx,bnf,resi,zet,C,coeflog,racpi,aij,tabj,colzero, *tabcstn, *tabcstni;
  GEN c_even,ck_even,c_odd,ck_odd,serie_even,serie_odd,serie_exp,Pi;
  long N0,imin,imax,r1,r2,ru,R,N,i,j,k,n, av,av2,tetpil;
  long court[] = {evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3),0};
  stackzone *zone, *zone0, *zone1;

  /*************** Calcul du residu et des constantes ***************/
  eps=gmul2n(gun,-bit_accuracy(prec)-6); p1=dbltor(0.5);
  nfz=cgetg(10,t_VEC);
  bnf=buchinit(pol,p1,p1,prec+1); prec=(prec<<1)-1;
  bnf = checkbnf_discard(bnf);
  Pi = mppi(prec); racpi=gsqrt(Pi,prec);

  /* Nb de classes et regulateur */
  nf=(GEN)bnf[7]; N=lgef(nf[1])-3;
  r1 = nf_get_r1(nf); r2 = (N-r1)>>1;
  gr1=gmael(nf,2,1); gr2=gmael(nf,2,2);
  ru=r1+r2; R=ru+2;
  av=avma; p1=(GEN)bnf[8]; p2 = gmul(gmul2n(gmael(p1,1,1),r1), (GEN)p1[2]);
  tetpil = avma; resi=gerepile(av,tetpil,gdiv(p2, gmael(p1,4,1)));

  /* Calcul de N0 */
  cst = cgetr(prec); av = avma;
  mu = gadd(gmul2n(gr1,-1),gr2);
  alpha = gmul2n(stoi(ru+1),-1);
  beta = gpui(gdeux,gmul2n(gr1,-1),DEFAULTPREC);
  A0 = gmul2n(gpowgs(mu,R),r1);
  A0 = gmul(A0,gpowgs(gmul2n(Pi,1),1-ru));
  A0 = gsqrt(A0,DEFAULTPREC);

  c1 = gmul(mu,gpui(beta,ginv(mu),DEFAULTPREC));
  c0 = gdiv(gmul(A0,gpowgs(gmul2n(Pi,1),ru-1)),mu);
  c0 = gmul(c0,gpui(c1,gneg_i(alpha),DEFAULTPREC));
  c2 = gdiv(alpha,mu);

  p1 = glog(gdiv(c0,eps),DEFAULTPREC);
  limx = gdiv(gsub(glog(p1,DEFAULTPREC),glog(c1,DEFAULTPREC)),
              gadd(c2,gdiv(p1,mu)));
  limx = gmul(gpui(gdiv(c1,p1),mu,DEFAULTPREC),
              gadd(gun,gmul(alpha,limx)));
  p1 = gsqrt(absi((GEN)nf[3]),prec);
  p2 = gmul2n(gpowgs(racpi,N),r2);
  gaffect(gdiv(p1,p2), cst);

  av = avma; p1 = gfloor(gdiv(cst,limx)); N0 = p1[2];
  if (is_bigint(p1) || N0 > 10000000)
    err(talker,"discriminant too large for initzeta, sorry");
  if (DEBUGLEVEL>=2)
    { fprintferr("\ninitzeta:\nN0 = %ld\n",N0); flusherr(); timer2(); }

  /* Calcul de imax */

  imin=1; imax=1400;
  p1 = gmul(gpowgs(gmul2n(racpi,1),r2),gpowgs(stoi(5),r1));
  p1 = gdiv(p1,gmul(gmul(gsqrt(limx,DEFAULTPREC),gmul2n(eps,4)),
                         gpowgs(racpi,3)));
  while (imax-imin >= 4)
  {
    long itest = (imax+imin)>>1;
    p2 = gmul(gpowgs(mpfactr(itest,DEFAULTPREC),r2),gpowgs(limx,itest));
    p2 = gmul(p2,gpowgs(mpfactr(itest/2,DEFAULTPREC),r1));
    if (gcmp(p2,p1) >= 0) imax=itest; else imin=itest;
  }
  imax -= (imax & 1); avma = av;
  if (DEBUGLEVEL>=2) { fprintferr("imax = %ld\n",imax); flusherr(); }
  /* Tableau des i/cst (i=1 a N0) */

  i = prec*N0;
  zone  = switch_stack(NULL,i + 2*(N0+1) + 6*prec);
  zone1 = switch_stack(NULL,2*i);
  zone0 = switch_stack(NULL,2*i);
  switch_stack(zone,1);
  tabcstn  = (GEN*) cgetg(N0+1,t_VEC);
  tabcstni = (GEN*) cgetg(N0+1,t_VEC);
  p1 = ginv(cst);
  for (i=1; i<=N0; i++) { tabcstni[i] = gun; tabcstn[i] = mulsr(i,p1); }
  switch_stack(zone,0);

  /********** Calcul des coefficients a(i,j) independants de s **********/

  zet=cgetg(R,t_VEC); zet[1] = lmpeuler(prec);
  for (i=2; i<R; i++) zet[i] = (long)gzeta(stoi(i),prec);

  aij=cgetg(imax+1,t_VEC);
  for (i=1; i<=imax; i++) aij[i] = lgetg(R,t_VEC);

  c_even = realun(prec);
  c_even = gmul2n(c_even,r1);
  c_odd = gmul(c_even,gpowgs(racpi,r1));
  if (ru&1) c_odd=gneg_i(c_odd);
  ck_even=cgetg(R,t_VEC); ck_odd=cgetg(r2+2,t_VEC);
  for (k=1; k<R; k++)
  {
    ck_even[k]=lmul((GEN)zet[k],gadd(gr2,gmul2n(gr1,-k)));
    if (k&1) ck_even[k]=lneg((GEN)ck_even[k]);
  }
  gru=stoi(ru);
  for (k=1; k<=r2+1; k++)
  {
    ck_odd[k]=lmul((GEN)zet[k], gsub(gru, gmul2n(gr1,-k)));
    if (k&1) ck_odd[k]=lneg((GEN)ck_odd[k]);
    ck_odd[k]=ladd(gru,(GEN)ck_odd[k]);
  }
  ck_odd[1]=lsub((GEN)ck_odd[1],gmul(gr1,glog(gdeux,prec)));
  serie_even =cgetg(ru+3,t_SER); serie_odd=cgetg(r2+3,t_SER);
  serie_even[1] = serie_odd[1] = evalsigne(1)+evalvalp(1);
  i=0;

  while (i<imax/2)
  {
    for (k=1; k<R; k++)
      serie_even[k+1]=ldivgs((GEN)ck_even[k],k);
    serie_exp=gmul(c_even,gexp(serie_even,0));
    p1=(GEN)aij[2*i+1];
    for (j=1; j<R; j++) p1[j]=serie_exp[ru+3-j];

    for (k=1; k<=r2+1; k++)
      serie_odd[k+1]=ldivgs((GEN)ck_odd[k],k);
    serie_exp=gmul(c_odd,gexp(serie_odd,0));
    p1=(GEN)aij[2*i+2];
    for (j=1; j<=r2+1; j++) p1[j]=serie_exp[r2+3-j];
    for (   ; j<R; j++) p1[j]=zero;
    i++;

    c_even = gdiv(c_even,gmul(gpowgs(stoi(i),ru),gpowgs(stoi(2*i-1),r2)));
    c_odd  = gdiv(c_odd, gmul(gpowgs(stoi(i),r2),gpowgs(stoi(2*i+1),ru)));
    c_even = gmul2n(c_even,-r2);
    c_odd  = gmul2n(c_odd,r1-r2);
    if (r1&1) { c_even=gneg_i(c_even); c_odd=gneg_i(c_odd); }
    p1 = gr2; p2 = gru;
    for (k=1; k<R; k++)
    {
      p1=gdivgs(p1,2*i-1); p2=gdivgs(p2,2*i);
      ck_even[k] = ladd((GEN)ck_even[k], gadd(p1,p2));
    }
    p1 = gru; p2 = gr2;
    for (k=1; k<=r2+1; k++)
    {
      p1=gdivgs(p1,2*i+1); p2=gdivgs(p2,2*i);
      ck_odd[k] = ladd((GEN)ck_odd[k], gadd(p1,p2));
    }
  }
  tetpil=avma; aij=gerepile(av,tetpil,gcopy(aij));
  if (DEBUGLEVEL>=2) msgtimer("a(i,j)");
  p1=cgetg(5,t_VEC);
  p1[1]=lstoi(r1); p1[2]=lstoi(r2); p1[3]=lstoi(imax); p1[4]=(long)bnf;
  nfz[1]=(long)p1;
  nfz[2]=(long)resi;
  nfz[5]=(long)cst;
  nfz[6]=llog(cst,prec);
  nfz[7]=(long)aij;

  /************* Calcul du nombre d'ideaux de norme donnee *************/
  coef = dirzetak0(nf,N0); tabj = cgetg(N0+1,t_MAT);
  if (DEBUGLEVEL>=2) msgtimer("coef");
  colzero=cgetg(ru+2,t_COL); for (j=1; j<=ru+1; j++) colzero[j]=zero;
  for (i=1; i<=N0; i++)
    if (coef[i])
    {
      GEN t = cgetg(ru+2,t_COL);
      p1 = glog((GEN)tabcstn[i],prec); setsigne(p1, -signe(p1));
      t[1] = lstoi(coef[i]); t[2] = lmul((GEN)t[1],p1);
      for (j=2; j<=ru; j++)
      {
        long av2 = avma; p2 = gmul((GEN)t[j],p1);
        t[j+1] = (long)gerepileuptoleaf(av2, divrs(p2,j));
      }
      /* tabj[n,j]=coef(n)*ln(c/n)^(j-1)/(j-1)! */
      tabj[i] = (long)t;
    }
    else tabj[i]=(long)colzero;
  if (DEBUGLEVEL>=2) msgtimer("a(n)");

  coeflog=cgetg(N0+1,t_VEC); coeflog[1]=zero;
  for (i=2; i<=N0; i++)
    if (coef[i])
    {
      court[2]=i; p1=glog(court,prec);
      setsigne(p1,-1); coeflog[i]=(long)p1;
    }
    else coeflog[i] = zero;
  if (DEBUGLEVEL>=2) msgtimer("log(n)");

  nfz[3]=(long)tabj;
  p1 = cgetg(N0+1,t_VECSMALL);
  for (i=1; i<=N0; i++) p1[i] = coef[i];
  nfz[8]=(long)p1;
  nfz[9]=(long)coeflog;

  /******************** Calcul des coefficients Cik ********************/

  C = cgetg(ru+1,t_MAT);
  for (k=1; k<=ru; k++) C[k] = lgetg(imax+1,t_COL);
  av2 = avma;
  for (i=1; i<=imax; i++)
  {
    stackzone *z;
    for (k=1; k<=ru; k++)
    {
      p1 = NULL;
      for (n=1; n<=N0; n++)
        if (coef[n])
          for (j=1; j<=ru-k+1; j++)
          {
            p2 = gmul(tabcstni[n],
                      gmul(gmael(aij,i,j+k), gmael(tabj,n,j)));
            p1 = p1? gadd(p1,p2): p2;
          }
      coeff(C,i,k) = p1? (long)gerepileupto(av2,p1): zero;
      av2 = avma;
    }
    /* use a parallel stack */
    z = i&1? zone1: zone0;
    switch_stack(z, 1);
    for (n=1; n<=N0; n++)
      if (coef[n]) tabcstni[n] = mpmul(tabcstni[n],tabcstn[n]);
    /* come back */
    switch_stack(z, 0);
  }
  nfz[4] = (long) C;
  if (DEBUGLEVEL>=2) msgtimer("Cik");
  gunclone(aij);
  free((void*)zone); free((void*)zone1); free((void*)zone0);
  free((void*)coef); return nfz;
}

GEN
gzetakall(GEN nfz, GEN s, long flag, long prec2)
{
  GEN resi,C,cst,cstlog,coeflog,cs,coef;
  GEN lambd,gammas,gammaunmoins,gammas2,gammaunmoins2,var1,var2;
  GEN p1,unmoins,gexpro,gar,val,valm,valk,valkm;
  long ts = typ(s), r1,r2,ru,imax,i,j,k,N0,sl,prec,bigprec, av = avma;

  if (typ(nfz)!=t_VEC || lg(nfz)!=10 || typ(nfz[1]) != t_VEC)
    err(talker,"not a zeta number field in zetakall");
  if (! is_intreal_t(ts) && ts != t_COMPLEX && ! is_frac_t(ts))
    err(typeer,"gzetakall");
  resi=(GEN)nfz[2]; C=(GEN)nfz[4]; cst=(GEN)nfz[5];
  cstlog=(GEN)nfz[6]; coef=(GEN)nfz[8]; coeflog=(GEN)nfz[9];
  r1   = itos(gmael(nfz,1,1));
  r2   = itos(gmael(nfz,1,2)); ru = r1+r2;
  imax = itos(gmael(nfz,1,3)); N0 = lg(coef)-1;
  bigprec = precision(cst); prec = prec2+1;

  if (ts==t_COMPLEX && gcmp0(gimag(s))) { s=greal(s); ts = typ(s); }
  if (ts==t_REAL && !signe(gfrac(s))) { s=mptrunc(s); ts = t_INT; }
  if (ts==t_INT)
  {
    sl=itos(s);
    if (sl==1) err(talker,"s = 1 is a pole (gzetakall)");
    if (sl==0)
    {
      avma = av;
      if (flag) err(talker,"s = 0 is a pole (gzetakall)");
      if (ru == 1) return gneg(r1? ghalf: resi);
      return gzero;
    }
    if (sl<0 && (r2 || !odd(sl)))
    {
      if (!flag) return gzero;
      s = subsi(1,s); sl = 1-sl;
    }
    unmoins=subsi(1,s);
    lambd = gdiv(resi, mulis(s,sl-1));
    gammas2=ggamma(gmul2n(s,-1),prec);
    gar=gpowgs(gammas2,r1);
    cs=gexp(gmul(cstlog,s),prec); 	
    val=s; valm=unmoins;
    if (sl < 0) /* r2 = 0 && odd(sl) */
    {
      gammaunmoins2=ggamma(gmul2n(unmoins,-1),prec);
      var1=var2=gun;
      for (i=2; i<=N0; i++)
	if (coef[i])
	{
          gexpro=gexp(gmul((GEN)coeflog[i],s),bigprec);
	  var1 = gadd(var1,gmulsg(coef[i],gexpro));
	  var2 = gadd(var2,gdivsg(coef[i],gmulsg(i,gexpro)));
	}
      lambd=gadd(lambd,gmul(gmul(var1,cs),gar));
      lambd=gadd(lambd,gmul(gmul(var2,gdiv(cst,cs)),
			    gpowgs(gammaunmoins2,r1)));
      for (i=1; i<=imax; i+=2)
      {
	valk  = val;
        valkm = valm;
	for (k=1; k<=ru; k++)	
	{
          p1 = gcoeff(C,i,k);
	  lambd = gsub(lambd,gdiv(p1,valk )); valk  = mulii(val,valk);
	  lambd = gsub(lambd,gdiv(p1,valkm)); valkm = mulii(valm,valkm);
	}
	val  = addis(val, 2);
        valm = addis(valm,2);
      }
    }
    else
    {
      GEN tabj=(GEN)nfz[3], aij=(GEN)nfz[7];

      gar = gmul(gar,gpowgs(ggamma(s,prec),r2));
      var1=var2=gzero;
      for (i=1; i<=N0; i++)
	if (coef[i])
	{
	  gexpro=gexp(gmul((GEN)coeflog[i],s),bigprec);
	  var1 = gadd(var1,gmulsg(coef[i],gexpro));
          if (sl <= imax)
          {
            p1=gzero;
            for (j=1; j<=ru+1; j++)
              p1 = gadd(p1, gmul(gmael(aij,sl,j), gmael(tabj,i,j)));
            var2=gadd(var2,gdiv(p1,gmulsg(i,gexpro)));
          }
	}
      lambd=gadd(lambd,gmul(gmul(var1,cs),gar));
      lambd=gadd(lambd,gmul(var2,gdiv(cst,cs)));
      for (i=1; i<=imax; i++)
      {
	valk  = val;
        valkm = valm;
        if (i == sl)
          for (k=1; k<=ru; k++)
          {	
            p1 = gcoeff(C,i,k);
            lambd = gsub(lambd,gdiv(p1,valk)); valk = mulii(val,valk);
          }
        else
	for (k=1; k<=ru; k++)
	{	
            p1 = gcoeff(C,i,k);
            lambd = gsub(lambd,gdiv(p1,valk )); valk  = mulii(val,valk); 
            lambd = gsub(lambd,gdiv(p1,valkm)); valkm = mulii(valm,valkm);
	}
	val  = addis(val,1);
        valm = addis(valm,1);
      }
    }
  }
  else
  {
    GEN Pi = mppi(prec);
    if (is_frac_t(ts))
      s = gmul(s, realun(bigprec));
    else
      s = gprec_w(s, bigprec);

    unmoins = gsub(gun,s);
    lambd = gdiv(resi,gmul(s,gsub(s,gun)));
    gammas = ggamma(s,prec);
    gammas2= ggamma(gmul2n(s,-1),prec);
    gar = gmul(gpowgs(gammas,r2),gpowgs(gammas2,r1));
    cs = gexp(gmul(cstlog,s),prec);
    var1 = gmul(Pi,s);
    gammaunmoins = gdiv(Pi,gmul(gsin(var1,prec),gammas));
    gammaunmoins2= gdiv(gmul(gmul(gsqrt(Pi,prec),gpui(gdeux,gsub(s,gun),prec)),
                             gammas2),
                        gmul(gcos(gmul2n(var1,-1),prec),gammas));
    var1 = var2 = gun;
    for (i=2; i<=N0; i++)
      if (coef[i])
      {
        gexpro = gexp(gmul((GEN)coeflog[i],s),bigprec);
	var1 = gadd(var1,gmulsg(coef[i], gexpro));
	var2 = gadd(var2,gdivsg(coef[i], gmulsg(i,gexpro)));
      }
    lambd = gadd(lambd,gmul(gmul(var1,cs),gar));
    lambd = gadd(lambd,gmul(gmul(gmul(var2,gdiv(cst,cs)),
	 		         gpowgs(gammaunmoins,r2)),
                            gpowgs(gammaunmoins2,r1)));
    val  = s;
    valm = unmoins;
    for (i=1; i<=imax; i++)
    {
      valk  = val;
      valkm = valm;
      for (k=1; k<=ru; k++)
      {
        p1 = gcoeff(C,i,k);
	lambd = gsub(lambd,gdiv(p1,valk )); valk  = gmul(val, valk);
	lambd = gsub(lambd,gdiv(p1,valkm)); valkm = gmul(valm,valkm);
      }
      if (r2)
      {
	val  = gadd(val, gun);
        valm = gadd(valm,gun);
      }
      else
      {
	val  = gadd(val, gdeux);
        valm = gadd(valm,gdeux); i++;
      }
    }
  }
  if (!flag) lambd = gdiv(lambd,gmul(gar,cs)); /* zetak */
  return gerepileupto(av, gprec_w(lambd, prec2));
}

GEN
gzetak(GEN nfz, GEN s, long prec)
{
  return gzetakall(nfz,s,0,prec);
}

GEN
glambdak(GEN nfz, GEN s, long prec)
{
  return gzetakall(nfz,s,1,prec);
}
