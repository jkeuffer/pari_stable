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
extern GEN R_from_QR(GEN x, long prec);
extern GEN to_polmod(GEN x, GEN mod);
extern GEN roots_to_pol_r1r2(GEN a, long r1, long v);
extern GEN idealhermite_aux(GEN nf, GEN x);
extern GEN cauchy_bound(GEN p);
extern GEN galoisbig(GEN x, long prec);
extern GEN lllfp_marked(int M, GEN x, long D, long flag, long prec, int gram);
extern GEN lllint_marked(long M, GEN x, long D, int g, GEN *h, GEN *fl, GEN *B);
extern GEN mulmat_pol(GEN A, GEN x);
extern ulong smulss(ulong x, ulong y, ulong *rem);

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
check_pol_int(GEN x, char *s)
{
  long k = lgef(x)-1;
  for ( ; k>1; k--)
    if (typ(x[k])!=t_INT) err(talker,"polynomial not in Z[X] in %s",s);
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
  gpmem_t av = avma, av2;
  long a, v = varn(x);
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
    u = caract2(x,p1,v); av2=avma;
  }
  while (lgef(srgcd(u,derivpol(u))) > 3); /* while u not separable */
  if (DEBUGLEVEL>1)
    fprintferr("Tschirnhaus transform. New pol: %Z",u);
  avma=av2; return gerepileupto(av,u);
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

/* assume pol in Z[X]. Find C, L in Z such that POL = C pol(x / L) monic in Z[X].
 * Return POL and set *ptlead = L */
GEN
primitive_pol_to_monic(GEN pol, GEN *ptlead)
{
  long i,j,n = degpol(pol);
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

static GEN
roots_to_ZX(GEN z, long *e)
{
  GEN a = roots_to_pol(z,0);
  GEN b = grndtoi(greal(a),e);
  long e1 = gexpo(gimag(a));
  if (e1 > *e) *e = e1;
  return b;
}

static GEN
_res(long n, long s, long k)
{
  GEN y = cgetg(4, t_VEC);
  y[1] = lstoi(n);
  y[2] = lstoi(s);
  y[3] = lstoi(k); return y;
}

GEN
galois(GEN x, long prec)
{
  gpmem_t av = avma, av1;
  long i,j,k,n,f,l,l2,e,e1,pr,ind;
  GEN x1,p1,p2,p3,p4,p5,w,z,ee;
  static int ind5[20]={2,5,3,4, 1,3,4,5, 1,5,2,4, 1,2,3,5, 1,4,2,3};
  static int ind6[60]={3,5,4,6, 2,6,4,5, 2,3,5,6, 2,4,3,6, 2,5,3,4,
                       1,4,5,6, 1,5,3,6, 1,6,3,4, 1,3,4,5, 1,6,2,5,
                       1,2,4,6, 1,5,2,4, 1,3,2,6, 1,2,3,5, 1,4,2,3};
  if (typ(x)!=t_POL) err(notpoler,"galois");
  n=degpol(x); if (n<=0) err(constpoler,"galois");
  if (n>11) err(impl,"galois of degree higher than 11");
  x = primpart(x);
  check_pol_int(x, "galois");
  if (gisirreducible(x) != gun)
    err(impl,"galois of reducible polynomial");

  if (n<4)
  {
    if (n == 1) { avma = av; return _res(1, 1,1); }
    if (n == 2) { avma = av; return _res(2,-1,1); }
    /* n = 3 */
    f = carreparfait(ZX_disc(x));
    avma = av;
    return f? _res(3,1,1): _res(6,-1,2);
  }
  x1 = x = primitive_pol_to_monic(x,NULL); av1=avma;
  if (n > 7) return galoisbig(x,prec);
  for(;;)
  {
    GEN cb = cauchy_bound(x);
    switch(n)
    {
      case 4: z = cgetg(7,t_VEC);
        prec = DEFAULTPREC + (long)((gexpo(cb)*18. / BITS_IN_LONG));
        for(;;)
	{
	  p1=roots(x,prec);
          z[1] = (long)get_F4(p1);
          z[2] = (long)get_F4(transroot(p1,1,2));
          z[3] = (long)get_F4(transroot(p1,1,3));
          z[4] = (long)get_F4(transroot(p1,1,4));
          z[5] = (long)get_F4(transroot(p1,2,3));
          z[6] = (long)get_F4(transroot(p1,3,4));
          p5 = roots_to_ZX(z, &e);
          if (e <= -10) break;
	  prec = (prec<<1)-2;
	}
        if (!ZX_is_squarefree(p5)) goto tchi;
	p2 = (GEN)factor(p5)[1];
	switch(lg(p2)-1)
	{
	  case 1: f = carreparfait(ZX_disc(x)); avma = av;
            return f? _res(12,1,4): _res(24,-1,5);

	  case 2: avma = av; return _res(8,-1,3);
	
	  case 3: avma = av;
	    return (degpol(p2[1])==2)? _res(4,1,2): _res(4,-1,1);

	  default: err(bugparier,"galois (bug1)");
	}

      case 5: z = cgetg(7,t_VEC);
        ee= cgetg(7,t_VECSMALL);
        w = cgetg(7,t_VECSMALL);
        prec = DEFAULTPREC + (long)((gexpo(cb)*21. / BITS_IN_LONG));
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
            p5 = roots_to_ZX(z, &e);
            if (e <= -10) break;
	    prec = (prec<<1)-2;
	  }
          if (!ZX_is_squarefree(p5)) goto tchi;
	  p3=(GEN)factor(p5)[1];
	  f=carreparfait(ZX_disc(x));
	  if (lg(p3)-1==1)
	  {
	    avma = av;
            return f? _res(60,1,4): _res(120,-1,5);
	  }
	  if (!f) { avma = av; return _res(20,-1,3); }

          pr = - (bit_accuracy(prec) >> 1);
          for (l=1; l<=6; l++)
	    if (ee[l] <= pr && gcmp0(poleval(p5,(GEN)w[l]))) break;
	  if (l>6) err(bugparier,"galois (bug4)");
	  p2=(l==6)? transroot(p1,2,5):transroot(p1,1,l);
	  p3=gzero;
	  for (i=1; i<=5; i++)
	  {
	    j = i+1; if (j>5) j -= 5;
	    p3 = gadd(p3,gmul(gmul((GEN)p2[i],(GEN)p2[j]),
		              gsub((GEN)p2[j],(GEN)p2[i])));
	  }
	  p5=gsqr(p3); p4=grndtoi(greal(p5),&e);
          e1 = gexpo(gimag(p5)); if (e1>e) e=e1;
	  if (e <= -10)
	  {
	    if (gcmp0(p4)) goto tchi;
	    f = carreparfait(p4); avma = av;
            return f? _res(5,1,1): _res(10,1,2);
	  }
	  prec=(prec<<1)-2;
	}

      case 6: z = cgetg(7, t_VEC);
        prec = DEFAULTPREC + (long)((gexpo(cb)*42. / BITS_IN_LONG));
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
		p3=gadd(p3,gmul(gsqr(gmul((GEN)p2[i],(GEN)p2[j])),p5));
                k += 4;
	      }
	      z[l] = (long)p3;
	    }
            p5 = roots_to_ZX(z, &e);
            if (e <= -10) break;
	    prec=(prec<<1)-2;
	  }
	  if (!ZX_is_squarefree(p5)) goto tchi;
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
              p5 = roots_to_ZX(z, &e);
	      if (e <= -10)
	      {
                if (!ZX_is_squarefree(p5)) goto tchi;
		p2 = (GEN)factor(p5)[1];
		f = carreparfait(ZX_disc(x));
		avma = av;
		if (lg(p2)-1==1)
                  return f? _res(360,1,15): _res(720,-1,16);
		else
                  return f? _res(36,1,10): _res(72,-1,13);
	      }
	      prec=(prec<<1)-2; break;
		
	    case 2: l2=degpol(p2[1]); if (l2>3) l2=6-l2;
	      switch(l2)
	      {
		case 1: f = carreparfait(ZX_disc(x));
		  avma = av;
                  return f? _res(60,1,12): _res(120,-1,14);
		case 2: f = carreparfait(ZX_disc(x));
		  if (f) { avma = av; return _res(24,1,7); }
                  p3 = (degpol(p2[1])==2)? (GEN)p2[2]: (GEN)p2[1];
                  f = carreparfait(ZX_disc(p3));
                  avma = av;
                  return f? _res(24,-1,6): _res(48,-1,11);
		case 3: f = carreparfait(ZX_disc((GEN)p2[1]))
		         || carreparfait(ZX_disc((GEN)p2[2]));
		  avma = av;
                  return f? _res(18,-1,5): _res(36,-1,9);
	      }
	    case 3:
	      for (l2=1; l2<=3; l2++)
		if (degpol(p2[l2]) >= 3) p3 = (GEN)p2[l2];
	      if (degpol(p3) == 3)
	      {
		f = carreparfait(ZX_disc(p3)); avma = av;
                return f? _res(6,-1,1): _res(12,-1,3);
	      }
	      else
	      {
		f = carreparfait(ZX_disc(x)); avma = av;
                return f? _res(12,1,4): _res(24,-1,8);
	      }
	    case 4: avma = av; return _res(6,-1,2);
            default: err(bugparier,"galois (bug3)");
	  }
	}
	
      case 7: z = cgetg(36,t_VEC);
        prec = DEFAULTPREC + (long)((gexpo(cb)*7. / BITS_IN_LONG));
        for(;;)
	{
	  ind = 0; p1=roots(x,prec);
	  for (i=1; i<=5; i++)
	    for (j=i+1; j<=6; j++)
            {
              GEN t = gadd((GEN)p1[i],(GEN)p1[j]);
	      for (k=j+1; k<=7; k++) z[++ind] = ladd(t, (GEN)p1[k]);
            }
          p5 = roots_to_ZX(z, &e);
	  if (e <= -10) break;
          prec = (prec<<1)-2;
	}
        if (!ZX_is_squarefree(p5)) goto tchi;
	p2=(GEN)factor(p5)[1];
	switch(lg(p2)-1)
	{
	  case 1: f = carreparfait(ZX_disc(x)); avma = av;
            return f? _res(2520,1,6): _res(5040,-1,7);
	  case 2: f = degpol(p2[1]); avma = av;
	    return (f==7 || f==28)? _res(168,1,5): _res(42,-1,4);
	  case 3: avma = av; return _res(21,1,3);
	  case 4: avma = av; return _res(14,-1,2);
	  case 5: avma = av; return _res(7,1,1);
          default: err(talker,"galois (bug2)");
	}
    }
    tchi: avma = av1; x = tschirnhaus(x1);
  }
}

GEN
galoisapply(GEN nf, GEN aut, GEN x)
{
  gpmem_t av=avma,tetpil;
  long lx,j,N;
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
      return gerepilecopy(av,y);

    case t_COL:
      N=degpol(pol);
      if (lg(x)!=N+1) err(typeer,"galoisapply");
      p1=galoisapply(nf,aut,gmul((GEN)nf[7],x)); tetpil=avma;
      return gerepile(av,tetpil,algtobasis(nf,p1));

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      N=degpol(pol);
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

GEN
get_nfpol(GEN x, GEN *nf)
{
  if (typ(x) == t_POL) { *nf = NULL; return x; }
  *nf = checknf(x); return (GEN)(*nf)[1];
}

/* if fliso test for isomorphism, for inclusion otherwise. */
static GEN
nfiso0(GEN a, GEN b, long fliso)
{
  gpmem_t av = avma;
  long n,m,i,vb,lx;
  GEN nfa,nfb,p1,y,la,lb;

  a = get_nfpol(a, &nfa);
  b = get_nfpol(b, &nfb);
  if (fliso && nfa && !nfb) { p1=a; a=b; b=p1; p1=nfa; nfa=nfb; nfb=p1; }
  m=degpol(a);
  n=degpol(b); if (m<=0 || n<=0) err(constpoler,"nfiso or nfincl");
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
    GEN da = nfa? (GEN)nfa[3]: ZX_disc(a);
    GEN db = nfb? (GEN)nfb[3]: ZX_disc(b);
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
    if (vb == 0) (void)delete_var();
  }
  lx = lg(y); if (lx==1) { avma=av; return gzero; }
  for (i=1; i<lx; i++)
  {
    p1 = (GEN)y[i];
    if (typ(p1) == t_POL) setvarn(p1, vb); else p1 = scalarpol(p1, vb);
    if (lb) p1 = poleval(p1, gmul(polx[vb],lb));
    y[i] = la? ldiv(p1,la): (long)p1;
  }
  return gerepilecopy(av,y);
}

GEN
nfisisom(GEN a, GEN b) { return nfiso0(a,b,1); }

GEN
nfisincl(GEN a, GEN b) { return nfiso0(a,b,0); }

/*************************************************************************/
/**									**/
/**			       INITALG					**/
/**									**/
/*************************************************************************/

GEN
get_roots(GEN x,long r1,long prec)
{
  GEN roo = (typ(x)==t_VEC)? dummycopy(x): roots(x,prec);
  long i, ru = (lg(roo)-1 + r1) >> 1;

  for (i=1; i<=r1; i++) roo[i]=lreal((GEN)roo[i]);
  for (   ; i<=ru; i++) roo[i]=roo[(i<<1)-r1];
  roo[0]=evaltyp(t_VEC)|evallg(ru+1); return roo;
}

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
  gpmem_t av = avma;
  GEN t = gzero;
  long i, l = lg(x);

  t = mulii((GEN)x[1],(GEN)T[1]);
  for (i=2; i<l; i++)
    if (signe(x[i])) t = addii(t, mulii((GEN)x[i],(GEN)T[i]));
  return gerepileuptoint(av, t);
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

  if (n==1 || gcmp1((GEN)pol[n])) { *lead = NULL; return pol; }
  return primitive_pol_to_monic(primpart(pol), lead);
}

/* Let T = (Tr(wi wj)), then T^(-1) Z^n = codifferent = coD/dcoD
 * NB: det(T) = dK, TI = dK T^(-1) integral */
static GEN
make_MDI(GEN nf, GEN TI, GEN *coD, GEN *dcoD)
{
  GEN c, MDI, dK = (GEN)nf[3];

  TI = Q_primitive_part(TI, &c);
  *dcoD = c? diviiexact(dK, c): dK;
  *coD = hnfmodid(TI, *dcoD);
  MDI = ideal_two_elt(nf, *coD);
  return c? gmul(c, MDI): MDI;
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
void
nf_get_sign(GEN nf, long *r1, long *r2)
{
  GEN x = (GEN)nf[2];
  if (typ(x) != t_VEC || lg(x) != 3
      || typ(x[1]) != t_INT || typ(x[2]) != t_INT)
    err(talker,"false nf in nf_get_sign");
  *r1 = itos((GEN)x[1]);
  *r2 = (degpol(nf[1]) - *r1) >> 1;
}

static GEN
get_Tr(GEN mul, GEN x, GEN basden)
{
  GEN tr,T,T1,sym, bas = (GEN)basden[1], den = (GEN)basden[2];
  long i,j,n = lg(bas)-1;
  T = cgetg(n+1,t_MAT);
  T1 = cgetg(n+1,t_COL);
  sym = polsym(x, n-1);

  T1[1]=lstoi(n);
  for (i=2; i<=n; i++)
  {
    tr = quicktrace((GEN)bas[i], sym);
    if (den && den[i]) tr = diviiexact(tr,(GEN)den[i]);
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
  GEN z,b,d,den, dbas = dummycopy(bas);
  long i, l = lg(bas);
  int power = 1;
  den = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    b = Q_remove_denom((GEN)bas[i], &d);
    dbas[i]= (long)b;
    den[i] = (long)d; if (d) power = 0;
  }
  if (power) den = NULL; /* power basis */
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
get_mul_table(GEN x,GEN basden,GEN invbas)
{
  long i,j, n = degpol(x);
  GEN z,d, mul = cgetg(n*n+1,t_MAT), bas=(GEN)basden[1], den=(GEN)basden[2];

  for (j=1; j<=n*n; j++) mul[j]=lgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
    for (j=i; j<=n; j++)
    {
      gpmem_t av = avma;
      z = gres(gmul((GEN)bas[j],(GEN)bas[i]), x);
      z = mulmat_pol(invbas, z); /* integral column */
      if (den)
      {
        d = _mulii((GEN)den[i], (GEN)den[j]);
        if (d) z = gdivexact(z, d);
      }
      mul[j+(i-1)*n] = mul[i+(j-1)*n] = lpileupto(av,z);
    }
  return mul;
}

/* as get_Tr, mul_table not precomputed */
static GEN
make_Tr(GEN x, GEN w)
{
  long i,j, n = degpol(x);
  GEN p1,p2,t,d;
  GEN sym = cgetg(n+2,t_VEC);
  GEN den = cgetg(n+1,t_VEC);
  GEN T = cgetg(n+1,t_MAT);
  gpmem_t av;

  sym = polsym(x, n-1);
  p1 = get_bas_den(w);
  w   = (GEN)p1[1];
  den = (GEN)p1[2];
  for (i=1; i<=n; i++)
  {
    p1 = cgetg(n+1,t_COL); T[i] = (long)p1;
    for (j=1; j<i ; j++) p1[j] = coeff(T,i,j);
    for (   ; j<=n; j++)
    {
      av = avma;
      p2 = gres(gmul((GEN)w[i],(GEN)w[j]), x);
      t = quicktrace(p2, sym);
      if (den)
      {
        d = _mulii((GEN)den[i],(GEN)den[j]);
        if (d) t = diviiexact(t, d);
      }
      p1[j] = lpileuptoint(av, t);
    }
  }
  return T;
}

/* compute roots so that _absolute_ accuracy of M >= prec [also holds for G] */
static void
get_roots_for_M(nffp_t *F)
{
  long n, eBD, er, PREC;
  
  if (F->extraprec < 0)
  { /* not initialized yet */
    n = degpol(F->x);
    eBD = 1 + gexpo((GEN)F->basden[1]);
    er  = 1 + gexpo(F->ro? F->ro: cauchy_bound(F->x));
    if (er < 0) er = 0;
    F->extraprec = ((n*er + eBD + (long)log2(n)) >> TWOPOTBITS_IN_LONG);
  }

  PREC = F->prec + F->extraprec;
  if (F->ro && gprecision((GEN)F->ro[1]) >= PREC) return;
  F->ro = get_roots(F->x, F->r1, PREC);
}

/* [bas[i]/den[i]]= integer basis. roo = real part of the roots */
static GEN
make_M(nffp_t *F, int trunc)
{
  GEN bas = (GEN)F->basden[1], den = (GEN)F->basden[2], ro = F->ro;
  GEN m, d, M;
  long i, j, l = lg(ro), n = lg(bas);
  M = cgetg(n,t_MAT);
    m = cgetg(l, t_COL); M[1] = (long)m;
    for (i=1; i<l; i++) m[i] = un; /* bas[1] = 1 */
  for (j=2; j<n; j++)
  {
    m = cgetg(l,t_COL); M[j] = (long)m;
    for (i=1; i<l; i++) m[i] = (long)poleval((GEN)bas[j], (GEN)ro[i]);
  }
  if (den)
  {
    GEN invd, rd = cgetr(F->prec + F->extraprec);
    for (j=2; j<n; j++)
    {
      d = (GEN)den[j]; if (!d) continue;
      m = (GEN)M[j]; affir(d,rd); invd = ginv(rd);
      for (i=1; i<l; i++) m[i] = lmul((GEN)m[i], invd);
    }
  }
  
  if (trunc && gprecision(M) > F->prec)
  {
    M     = gprec_w(M, F->prec);
    F->ro = gprec_w(ro,F->prec);
  }
  if (DEBUGLEVEL>4) msgtimer("matrix M");
  return F->M = M;
}

/* return G real such that G~ * G = T_2 */
static GEN
make_G(nffp_t *F)
{
  GEN G, m, g, r, M = F->M, sqrt2 = gsqrt(gdeux, F->prec + F->extraprec);
  long i, j, k, r1 = F->r1, l = lg(M);

  G = cgetg(l, t_MAT);
  for (j=1; j<l; j++)
  {
    g = cgetg(l, t_COL);
    G[j] = (long)g; m = (GEN)M[j];
    for (k=i=1; i<=r1; i++) g[k++] = m[i];
    for (     ; k < l; i++)
    {
      r = (GEN)m[i];
      if (typ(r) == t_COMPLEX)
      {
        g[k++] = lmpmul(sqrt2, (GEN)r[1]);
        g[k++] = lmpmul(sqrt2, (GEN)r[2]);
      }
      else
      {
        g[k++] = lmpmul(sqrt2, r);
        g[k++] = zero;
      }
    }
  }
  return F->G = G;
}

static void
make_M_G(nffp_t *F, int trunc)
{
  get_roots_for_M(F);
  make_M(F, trunc);
  make_G(F);
}

void
remake_GM(GEN nf, nffp_t *F, long prec)
{
  F->x  = (GEN)nf[1];
  F->ro = NULL;
  F->r1 = nf_get_r1(nf);
  F->basden = get_bas_den((GEN)nf[7]);
  F->extraprec = -1;
  F->prec = prec; make_M_G(F, 1);
}

static void
nffp_init(nffp_t *F, nfbasic_t *T, GEN ro, long prec)
{
  F->x  = T->x;
  F->ro = ro;
  F->r1 = T->r1;
  if (!T->basden) T->basden = get_bas_den(T->bas);
  F->basden = T->basden;
  F->extraprec = -1;
  F->prec = prec;
}

static void
get_nf_fp_compo(nfbasic_t *T, nffp_t *F, GEN ro, long prec)
{
  nffp_init(F,T,ro,prec);
  make_M_G(F, 1);
}

static GEN
get_sign(long r1, long n)
{
  GEN s = cgetg(3, t_VEC);
  s[1] = lstoi(r1);
  s[2] = lstoi((n - r1) >> 1); return s;
}

GEN
nfbasic_to_nf(nfbasic_t *T, GEN ro, long prec)
{
  GEN nf = cgetg(10,t_VEC);
  GEN x = T->x;
  GEN invbas,Tr,D,TI,A,dA, mat = cgetg(8,t_VEC);
  nffp_t F;
  get_nf_fp_compo(T, &F, ro, prec);

  nf[1] = (long)T->x;
  nf[2] = (long)get_sign(T->r1, degpol(T->x));
  nf[3] = (long)T->dK;
  nf[4] = (long)T->index;
  nf[6] = (long)F.ro;
  nf[5] = (long)mat;
  nf[7] = (long)T->bas;

  mat[1] = (long)F.M;
  mat[2] = (long)F.G;

  invbas = QM_inv(vecpol_to_mat(T->bas, lg(T->bas)-1), gun);
  nf[8] = (long)invbas;
  nf[9] = (long)get_mul_table(x, F.basden, invbas);
  if (DEBUGLEVEL) msgtimer("mult. table");

  Tr = get_Tr((GEN)nf[9], x, F.basden);
  TI = ZM_inv(Tr, T->dK); /* dK T^-1 */
  mat[6] = (long)TI;
  mat[7] = (long)make_MDI(nf,TI, &A, &dA); /* needed in idealinv below */
  if (is_pm1(T->index))
    D = idealhermite_aux(nf, derivpol(x));
  else
    D = gmul(dA, idealinv(nf, A));
  mat[3] = zero; /* FIXME: was gram matrix of current mat[2]. Useless */
  mat[4] = (long)Tr;
  mat[5] = (long)D;
  if (DEBUGLEVEL) msgtimer("matrices");
  return nf;
}

static GEN
hnffromLLL(GEN nf)
{
  GEN d, x;
  x = vecpol_to_mat((GEN)nf[7], degpol(nf[1]));
  x = Q_remove_denom(x, &d);
  if (!d) return x; /* power basis */
  return gauss(hnfmodid(x, d), x);
}

static GEN
nfbasechange(GEN u, GEN x)
{
  long i,lx;
  GEN y;
  switch(typ(x))
  {
    case t_COL: /* nfelt */
      return gmul(u, x);

    case t_MAT: /* ideal */
      y = dummycopy(x);
      lx = lg(x);
      for (i=1; i<lx; i++) y[i] = lmul(u, (GEN)y[i]);
      break;

    case t_VEC: /* pr */
      checkprimeid(x);
      y = dummycopy(x);
      y[2] = lmul(u, (GEN)y[2]);
      y[5] = lmul(u, (GEN)y[5]);
      break;
    default: y = x;
  }
  return y;
}

GEN
nffromhnfbasis(GEN nf, GEN x)
{
  long tx = typ(x);
  gpmem_t av = avma;
  GEN u;
  if (!is_vec_t(tx)) return gcopy(x);
  nf = checknf(nf);
  u = hnffromLLL(nf);
  return gerepilecopy(av, nfbasechange(u, x));
}

GEN
nftohnfbasis(GEN nf, GEN x)
{
  long tx = typ(x);
  gpmem_t av = avma;
  GEN u;
  if (!is_vec_t(tx)) return gcopy(x);
  nf = checknf(nf);
  u = ZM_inv(hnffromLLL(nf), gun);
  return gerepilecopy(av, nfbasechange(u, x));
}

static GEN
get_red_G(nfbasic_t *T, GEN *pro)
{
  GEN G, u, u0 = NULL;
  gpmem_t av;
  long i, prec, extraprec = (long) (degpol(T->x) * sizeof(long) / 8.);
  nffp_t F;

  prec = DEFAULTPREC + extraprec;
  nffp_init(&F, T, *pro, prec);
  av = avma;
  for (i=1; ; i++)
  {
    F.prec = prec; make_M_G(&F, 0); G = F.G;
    if (i == 1 && F.extraprec > 10) F.extraprec += extraprec;
    if (u0) G = gmul(G, u0);
    if (DEBUGLEVEL)
      fprintferr("get_red_G: starting LLL, prec = %ld (%ld + %ld)\n",
                  prec + F.extraprec, prec, F.extraprec);
    if ((u = lllfp_marked(1, G, 100, 2, prec, 0)))
    {
      if (typ(u) == t_MAT) break;
      u = (GEN)u[1];
      if (u0) u0 = gerepileupto(av, gmul(u0,u));
      else    u0 = gerepilecopy(av, u);
    }
    if (i == MAXITERPOL) err(accurer,"red_T2");
    prec = (prec<<1)-2 + (gexpo(u0) >> TWOPOTBITS_IN_LONG);
    F.ro = NULL;
    if (DEBUGLEVEL) err(warnprec,"get_red_G", prec);
  }
  *pro = F.ro; return u0? gmul(u0,u): u;
}

/* Return the base change matrix giving an LLL-reduced basis for the
 * integer basis of nf(T).
 * *ro = roots of x, computed to precision prec [or NULL] */
static GEN
get_LLL_basis(nfbasic_t *T, GEN *pro)
{
  GEN u;
  if (T->r1 != degpol(T->x)) u = get_red_G(T, pro);
  else
  {
    u = lllint_marked(1, make_Tr(T->x, T->bas), 100, 1, &u,NULL,NULL);
    if (!u) u = idmat(1);
  }
  return u;
}

static void
set_LLL_basis(nfbasic_t *T, GEN *pro)
{
  T->bas = gmul(T->bas, get_LLL_basis(T, pro));
  T->basden = NULL; /* recompute */
}

typedef struct {
  GEN xbest, dxbest;
  long ind, indmax, indbest;
} ok_pol_t;

/* is xn better than x ? */
static int
better_pol(GEN xn, GEN dxn, GEN x, GEN dx)
{
  int fl;
  if (!x) return 1;
  fl = absi_cmp(dxn, dx);
  return (fl < 0 || (!fl && gpolcomp(xn, x) < 0));
}

static GEN
ok_pol(void *TT, GEN xn)
{
  ok_pol_t *T = (ok_pol_t*)TT;
  GEN dxn;
  
  if (++T->ind > T->indmax && T->xbest) return T->xbest;
  
  if (!ZX_is_squarefree(xn)) return (T->ind == T->indmax)? T->xbest: NULL;
  if (DEBUGLEVEL>3) outerr(xn);
  dxn = ZX_disc(xn);
  if (better_pol(xn, dxn, T->xbest, T->dxbest))
  {
    T->dxbest = dxn; T->xbest = xn; T->indbest = T->ind;
  }
  if (T->ind >= T->indmax) return T->xbest;
  return NULL;
}

/* z in Z[X] with positive leading coeff. Set z := z(-X) or z(X) so that
 * second coeff is > 0. In place. */
static int
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

static GEN _polred(GEN x, GEN a, GEN *pta, FP_chk_fun *CHECK);

/* Seek a simpler, polynomial pol defining the same number field as
 * x (assumed to be monic at this point) */
static GEN
nfpolred(int part, nfbasic_t *T)
{
  GEN x = T->x, dx = T->dx, a = T->bas;
  GEN phi, xbest, dxbest, mat, d, rev;
  long i, n = lg(a)-1, v = varn(x);
  ok_pol_t O;
  FP_chk_fun chk;

  if (degpol(x) == 1) { T->x = gsub(polx[v],gun); return gun; }

  if (!dx) dx = mulii(T->dK, sqri(T->index));

  O.ind    = 0;
  O.indmax = part? min(n,3): n;
  O.xbest  = NULL;
  chk.f    = &ok_pol;
  chk.data = (void*)&O;
  if (!_polred(x, a, NULL, &chk))
    err(talker,"you found a counter-example to a conjecture, please report!");
  xbest = O.xbest; dxbest = O.dxbest;
  if (!better_pol(xbest, dxbest, x, dx)) return NULL; /* no improvement */

  /* update T */
  phi = (GEN)a[O.indbest];
  if (canon_pol(xbest) < 0) phi = gneg_i(phi);
  if (DEBUGLEVEL>1) fprintferr("xbest = %Z\n",xbest);
  rev = modreverse_i(phi, x);
  for (i=1; i<=n; i++) a[i] = (long)RX_RXQ_compo((GEN)a[i], rev, xbest);
  mat = vecpol_to_mat(Q_remove_denom(a, &d), n);
  if (!is_pm1(d)) mat = gdiv(hnfmodid(mat,d), d); else mat = idmat(n);

  (void)carrecomplet(diviiexact(dxbest,T->dK), &(T->index));
  T->bas= mat_to_vecpol(mat, v);
  T->dx = dxbest;
  T->x  = xbest; return rev;
}

GEN
get_nfindex(GEN bas)
{
  gpmem_t av = avma;
  long n = lg(bas)-1;
  GEN d, mat = vecpol_to_mat(Q_remove_denom(bas, &d), n);
  if (!d) { avma = av; return gun; }
  return gerepileuptoint(av, diviiexact(gpowgs(d, n), det(mat)));
}

void
nfbasic_init(GEN x, long flag, GEN fa, nfbasic_t *T)
{
  GEN bas, dK, dx, index;
  long r1;

  T->basden = NULL;
  T->lead   = NULL;
  if (DEBUGLEVEL) (void)timer2();
  if (typ(x) == t_POL)
  {
    check_pol_int(x, "nfinit");
    if (gisirreducible(x) == gzero) err(redpoler, "nfinit");
    x = pol_to_monic(x, &(T->lead));
    bas = allbase(x, flag, &dx, &dK, &index, &fa);
    if (DEBUGLEVEL) msgtimer("round4");
    r1 = sturm(x);
  }
  else if (typ(x) == t_VEC && lg(x)==3 && typ(x[1])==t_POL)
  { /* monic integral polynomial + integer basis */
    GEN mat;
    bas = (GEN)x[2]; x = (GEN)x[1];
    if (typ(bas) == t_MAT)
      { mat = bas; bas = mat_to_vecpol(mat,varn(x)); }
    else
        mat = vecpol_to_mat(bas, lg(bas)-1);
    index = get_nfindex(bas);
    dx = ZX_disc(x);
    dK = diviiexact(dx, sqri(index));
    r1 = sturm(x);
  }
  else
  { /* nf, bnf, bnr */
    GEN nf = checknf(x);
    x     = (GEN)nf[1];
    dK    = (GEN)nf[3];
    index = (GEN)nf[4];
    bas   = (GEN)nf[7];
    r1 = nf_get_r1(nf); dx = NULL;
  }

  T->x     = x;
  T->r1    = r1;
  T->dx    = dx;
  T->dK    = dK;
  T->bas   = bas;
  T->index = index;
}

/* Initialize the number field defined by the polynomial x (in variable v)
 * flag & nf_RED:     try a polred first.
 * flag & nf_PARTRED: as nf_RED but check the first two elements only.
 * flag & nf_ORIG
 *    do a polred and return [nfinit(x), Mod(a,red)], where
 *    Mod(a,red) = Mod(v,x) (i.e return the base change). */
GEN
_initalg(GEN x, long flag, long prec)
{
  const gpmem_t av = avma;
  GEN nf, rev = NULL, ro = NULL;
  nfbasic_t T;

  nfbasic_init(x, flag, NULL, &T);

  if (T.lead && !(flag & (nf_RED|nf_PARTRED)))
  {
    err(warner,"non-monic polynomial. Result of the form [nf,c]");
    flag |= nf_PARTRED | nf_ORIG;
  }
  if (flag & (nf_RED|nf_PARTRED))
  {
    set_LLL_basis(&T, &ro);
    rev = nfpolred(flag & nf_PARTRED, &T);
    if (rev) ro = NULL; /* changed T.x */
    if (flag & nf_ORIG)
    {
      if (!rev) rev = polx[varn(T.x)]; /* no improvement */
      if (T.lead) rev = gdiv(rev, T.lead);
      rev = to_polmod(rev, T.x);
    }
    if (DEBUGLEVEL) msgtimer("polred");
  }

  set_LLL_basis(&T, &ro);
  if (DEBUGLEVEL) msgtimer("LLL basis");

  nf = nfbasic_to_nf(&T, ro, prec);
  if (flag & nf_ORIG)
  {
    GEN res = cgetg(3,t_VEC);
    res[1] = (long)nf;
    res[2] = (long)rev; nf = res;
  }
  return gerepilecopy(av, nf);
}

GEN
initalgred(GEN x, long prec)  { return _initalg(x, nf_RED, prec); }
GEN
initalgred2(GEN x, long prec) { return _initalg(x, nf_RED|nf_ORIG, prec); }
GEN
initalg(GEN x, long prec)     { return _initalg(x, 0, prec); }

GEN
nfinit0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0:
    case 1: return _initalg(x,0,prec);
    case 2: return _initalg(x,nf_RED,prec);
    case 3: return _initalg(x,nf_RED|nf_ORIG,prec);
    case 4: return _initalg(x,nf_PARTRED,prec);
    case 5: return _initalg(x,nf_PARTRED|nf_ORIG,prec);
    default: err(flagerr,"nfinit");
  }
  return NULL; /* not reached */
}

/* assume x a bnr/bnf/nf */
long
nfgetprec(GEN x)
{
  GEN nf = checknf(x), ro = (GEN)nf[6];
  return (typ(ro)==t_VEC)? precision((GEN)ro[1]): DEFAULTPREC;
}

GEN
nfnewprec(GEN nf, long prec)
{
  gpmem_t av = avma;
  GEN NF;
  nffp_t F;

  if (typ(nf) != t_VEC) err(talker,"incorrect nf in nfnewprec");
  if (lg(nf) == 11) return bnfnewprec(nf,prec);
  if (lg(nf) ==  7) return bnrnewprec(nf,prec);
  (void)checknf(nf);
  NF = dummycopy(nf);
  NF[5] = (long)dummycopy((GEN)NF[5]);
  remake_GM(NF, &F, prec);
  NF[6]  = (long)F.ro;
  mael(NF,5,1) = (long)F.M;
  mael(NF,5,2) = (long)F.G;
  return gerepilecopy(av, NF);
}

/********************************************************************/
/**                                                                **/
/**                           POLRED                               **/
/**                                                                **/
/********************************************************************/
/* remove duplicate polynomials in y, updating a (same indexes), in place */
static void
remove_duplicates(GEN y, GEN a)
{
  long k, i, l = lg(y);
  gpmem_t av = avma;
  GEN z;

  if (l < 2) return;
  z = new_chunk(3);
  z[1] = (long)y;
  z[2] = (long)a; (void)sort_factor(z, gcmp);
  for  (k=1, i=2; i<l; i++)
    if (!gegal((GEN)y[i], (GEN)y[k]))
    {
      k++;
      a[k] = a[i];
      y[k] = y[i];
    }
  l = k+1; setlg(a,l); setlg(y,l);
  avma = av;
}

/* if CHECK != NULL, return the first polynomial pol found such that
 * CHECK->f(CHECK->data, pol) != 0; return NULL if there are no such pol */
static GEN
_polred(GEN x, GEN a, GEN *pta, FP_chk_fun *CHECK)
{
  long i, v = varn(x), l = lg(a);
  GEN ch, d, y = cgetg(l,t_VEC);

  for (i=1; i<l; i++)
  {
    if (DEBUGLEVEL>2) { fprintferr("i = %ld\n",i); flusherr(); }
    ch = QX_caract(x, (GEN)a[i], v);
    if (CHECK)
    {
      ch = CHECK->f(CHECK->data, ch);
      if (!ch) continue;
      return ch;
    }
    d = modulargcd(derivpol(ch), ch);
    if (degpol(d)) ch = gdivexact(ch,d);

    if (canon_pol(ch) < 0 && pta) a[i] = (long)gneg_i((GEN)a[i]);
    if (DEBUGLEVEL > 3) outerr(ch);
    y[i] = (long)ch;
  }
  if (CHECK) return NULL; /* no suitable polynomial found */
  remove_duplicates(y,a);
  if (pta) *pta = a;
  return y;
}

static GEN
allpolred(GEN x, long flag, GEN fa, GEN *pta, FP_chk_fun *CHECK)
{
  GEN ro = NULL;
  nfbasic_t T; nfbasic_init(x, flag, fa, &T);
  if (T.lead) err(impl,"polred for non-monic polynomial");
  set_LLL_basis(&T, &ro);
  return _polred(T.x, T.bas, pta, CHECK);
}

/* FIXME: backward compatibility */
#define red_PARTIAL 1
#define red_ORIG    2

GEN
polred0(GEN x, long flag, GEN fa)
{
  gpmem_t av = avma;
  GEN y, a;
  int fl = 0;

  if (fa && gcmp0(fa)) fa = NULL; /* compatibility */
  if (flag & red_PARTIAL) fl |= nf_PARTIALFACT;
  if (flag & red_ORIG)    fl |= nf_ORIG;
  y = allpolred(x, fl, fa, &a, NULL);
  if (fl & nf_ORIG) {
    GEN z = cgetg(3,t_MAT);
    z[1] = (long)a;
    z[2] = (long)y; y = z;
  }
  return gerepilecopy(av, y);
}

GEN
ordred(GEN x)
{
  gpmem_t av = avma;
  GEN y;

  if (typ(x) != t_POL) err(typeer,"ordred");
  if (!gcmp1(leading_term(x))) err(impl,"ordred");
  if (!signe(x)) return gcopy(x);
  y = cgetg(3,t_VEC);
  y[1] = (long)x;
  y[2] = (long)idmat(degpol(x));
  return gerepileupto(av, polred(y));
}

GEN
polredfirstpol(GEN x, long flag, FP_chk_fun *CHECK)
{ return allpolred(x,flag,NULL,NULL,CHECK); }
GEN
polred(GEN x)
{ return polred0(x, 0, NULL); }
GEN
smallpolred(GEN x)
{ return polred0(x, red_PARTIAL, NULL); }
GEN
factoredpolred(GEN x, GEN fa)
{ return polred0(x, 0, fa); }
GEN
polred2(GEN x)
{ return polred0(x, red_ORIG, NULL); }
GEN
smallpolred2(GEN x)
{ return polred0(x, red_PARTIAL|red_ORIG, NULL); }
GEN
factoredpolred2(GEN x, GEN fa)
{ return polred0(x, red_PARTIAL, fa); }

/********************************************************************/
/**                                                                **/
/**                           POLREDABS                            **/
/**                                                                **/
/********************************************************************/

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

typedef struct {
  long r1, v, prec;
  GEN ZKembed; /* embeddings of fincke-pohst-reduced Zk basis */
  GEN u; /* matrix giving fincke-pohst-reduced Zk basis */
  GEN M; /* embeddings of initial (LLL-reduced) Zk basis */
  GEN bound; /* T2 norm of the polynomial defining nf */
} CG_data;

/* characteristic pol of x */
static GEN
get_polchar(CG_data *d, GEN x)
{
  GEN g = gmul(d->ZKembed,x);
  long e;
  g = grndtoi(roots_to_pol_r1r2(g, d->r1, d->v), &e);
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
chk_gen_init(FP_chk_fun *chk, GEN gram, GEN mat)
{
  CG_data *d = (CG_data*)chk->data;
  GEN P,bound,prev,x,B;
  long l = lg(gram), N = l-1,i,prec,prec2;
  int skipfirst = 0;

  d->u = mat;
  d->ZKembed = gmul(d->M,   mat);

  bound = d->bound;
  prev = NULL;
  x = zerocol(N);
  for (i=1; i<l; i++)
  {
    B = gcoeff(gram,i,i);
    if (gcmp(B,bound) >= 0) break;

    x[i] = un; P = get_polmin(d,x);
    x[i] = zero;
    if (degpol(P) == N)
    {
      if (gcmp(B,bound) < 0) bound = B ;
      continue;
    }
    if (DEBUGLEVEL>2) fprintferr("chk_gen_init: subfield %Z\n",P);
    if (skipfirst != i-1) continue;

    /* Q(w[1],...,w[i-1]) = Q[X]/(prev) is a strict subfield of nf */
    if (prev && degpol(prev) < N && !gegal(prev,P))
    {
      if (degpol(prev) * degpol(P) > 64) continue; /* too expensive */
      P = (GEN)compositum(prev,P)[1];
      if (degpol(P) == N) continue;
      if (DEBUGLEVEL>2 && degpol(P) != degpol(prev))
        fprintferr("chk_gen_init: subfield %Z\n",P);
    }
    skipfirst++; prev = P;
  }
  /* x_1,...,x_skipfirst generate a strict subfield [unless N=skipfirst=1] */
  chk->skipfirst = skipfirst;
  if (DEBUGLEVEL>2) fprintferr("chk_gen_init: skipfirst = %ld\n",skipfirst);

  /* should be gexpo( max_k C^n_k (bound/k)^(k/2) ) */
  prec2 = (1 + (((gexpo(bound)*N)/2) >> TWOPOTBITS_IN_LONG));
  if (prec2 < 0) prec2 = 0;
  prec = 3 + prec2;
  if (DEBUGLEVEL)
    fprintferr("chk_gen_init: new prec = %ld (initially %ld)\n", prec, d->prec);
  if (prec > d->prec) err(bugparier, "precision problem in polredabs");
  if (prec < d->prec) d->ZKembed = gprec_w(d->ZKembed, prec);
  return bound;
}

/* store phi(beta mod z). Suitable for gerepileupto */
static GEN
storeeval(GEN beta, GEN z, GEN lead)
{
  GEN y = cgetg(3,t_VEC);
  z = gcopy(z);
  beta = lead? gdiv(beta, lead): gcopy(beta);
  y[1] = (long)z;
  y[2] = (long)to_polmod(beta,z);
  return y;
}

static GEN
storeraw(GEN beta, GEN z)
{
  GEN y = cgetg(3,t_VEC);
  y[1] = lcopy(z);
  y[2] = lcopy(beta); return y;
}

static void
findmindisc(GEN *py, GEN *pa)
{
  GEN v, dmin, z, b, discs, y = *py, a = *pa;
  long i,k, l = lg(y);
  
  if (l == 2) { *py = (GEN)y[1]; *pa = (GEN)a[1]; return; }

  discs = cgetg(l,t_VEC);
  for (i=1; i<l; i++) discs[i] = labsi(ZX_disc((GEN)y[i]));
  v = sindexsort(discs);
  k = v[1];
  dmin = (GEN)discs[k];
  z    = (GEN)y[k];
  b = (GEN)a[k];
  for (i=2; i<l; i++)
  {
    k = v[i];
    if (!egalii((GEN)discs[k], dmin)) break;
    if (gpolcomp((GEN)y[k],z) < 0) { z = (GEN)y[k]; b = (GEN)a[k]; }
  }
  *py = z; *pa = b;
}

static GEN
storepol(GEN x, GEN z, GEN a, GEN lead, long flag)
{
  GEN y, b;
  if (flag & nf_RAW)
    y = storeraw(a, z);
  else if (flag & nf_ORIG)
  {
    b = modreverse_i(a, x);
    y = storeeval(b,z, lead);
  }
  else
    y = gcopy(z);
  return y;
}

static GEN
storeallpol(GEN x, GEN z, GEN a, GEN lead, long flag)
{
  GEN y, b;

  if (flag & nf_RAW)
  {
    long i, c = lg(z);
    y = cgetg(c,t_VEC);
    for (i=1; i<c; i++) y[i] = (long)storeraw((GEN)a[i], (GEN)z[i]);
  }
  else if (flag & nf_ORIG)
  {
    long i, c = lg(z);
    b = cgetg(c, t_VEC);
    for (i=1; i<c; i++)
      b[i] = (long)modreverse_i((GEN)a[i], x);

    y = cgetg(c,t_VEC);
    for (i=1; i<c; i++) y[i] = (long)storeeval((GEN)b[i], (GEN)z[i], lead);
  }
  else
    y = gcopy(z);
  return y;
}

GEN
_polredabs(nfbasic_t *T, GEN *u)
{
  long i, prec, e, n = degpol(T->x);
  GEN v, ro = NULL;
  FP_chk_fun chk = { &chk_gen, &chk_gen_init, NULL, 0 };
  nffp_t F;
  CG_data d; chk.data = (void*)&d;

  set_LLL_basis(T, &ro);
  if (DEBUGLEVEL) msgtimer("LLL basis");

  /* || polchar ||_oo < 2^e */
  e = n * (gexpo(gmulsg(n, cauchy_bound(T->x))) + 1);
  prec = DEFAULTPREC + (e >> TWOPOTBITS_IN_LONG);

  get_nf_fp_compo(T, &F, ro, prec);

  d.v = varn(T->x);
  d.r1= T->r1;
  d.bound = gmul(T2_from_embed(F.ro, d.r1), dbltor(1.00000001));
  for (i=1; ; i++)
  {
    GEN R = R_from_QR(F.G, prec);
    d.prec = prec;
    d.M    = F.M;
    if (R)
    {
      v = fincke_pohst(_vec(R),NULL,5000,1, 0, &chk);
      if (v) break;
    }
    if (i==MAXITERPOL) err(accurer,"polredabs0");
    prec = (prec<<1)-2;
    get_nf_fp_compo(T, &F, NULL, prec);
    if (DEBUGLEVEL) err(warnprec,"polredabs0",prec);
  }
  *u = d.u; return v;
}

GEN
polredabs0(GEN x, long flag)
{
  long i, l, vx;
  gpmem_t av = avma;
  GEN y, a, u;
  nfbasic_t T;

  nfbasic_init(x, flag & nf_PARTIALFACT, NULL, &T);
  x = T.x; vx = varn(x);

  if (degpol(x) == 1)
  {
    u = NULL;
    y = _vec(polx[vx]);
    a = _vec(gsub((GEN)y[1], (GEN)x[2]));
  }
  else
  {
    GEN v = _polredabs(&T, &u);
    y = (GEN)v[1];
    a = (GEN)v[2];
  }
  l = lg(a);
  for (i=1; i<l; i++)
    if (canon_pol((GEN)y[i]) < 0) a[i] = (long)gneg_i((GEN)a[i]);
  remove_duplicates(y,a);
  l = lg(a);
  if (l == 1)
  {
    y = _vec(x);
    a = _vec(polx[vx]);
  }
  if (DEBUGLEVEL) fprintferr("%ld minimal vectors found.\n",l-1);
  if (flag & nf_ALL)
  {
    if (u) for (i=1; i<l; i++) a[i] = lmul(T.bas, gmul(u, (GEN)a[i]));
    y = storeallpol(x,y,a,T.lead,flag);
  }
  else
  {
    findmindisc(&y, &a);
    if (u) a = gmul(T.bas, gmul(u, a));
    y = storepol(x,y,a,T.lead,flag);
  }
  return gerepileupto(av, y);
}

GEN
polredabsall(GEN x, long flun)
{ return polredabs0(x, flun | nf_ALL); }
GEN
polredabs(GEN x)
{ return polredabs0(x,0); }
GEN
polredabs2(GEN x)
{ return polredabs0(x,nf_ORIG); }

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

/* only roots of 1 are +/- 1 */
static GEN
trivroots(GEN nf)
{
  GEN y = cgetg(3, t_VEC);
  y[1] = deux;
  y[2] = (long)gscalcol_i(negi(gun), degpol(nf[1]));
  return y;
}

GEN
rootsof1(GEN nf)
{
  gpmem_t av = avma;
  long N,k,i,ws,prec;
  GEN p1,y,d,list,w;

  nf = checknf(nf);
  if ( nf_get_r1(nf) ) return trivroots(nf);

  N = degpol(nf[1]); prec = nfgetprec(nf);
  for (i=1; ; i++)
  {
    GEN R = R_from_QR(gmael(nf,5,2), prec);
    if (R)
    {
      p1 = fincke_pohst(_vec(R),stoi(N),1000,1, 0, NULL);
      if (p1) break;
    }
    if (i == MAXITERPOL) err(accurer,"rootsof1");
    prec = (prec<<1)-2;
    if (DEBUGLEVEL) err(warnprec,"rootsof1",prec);
    nf = nfnewprec(nf,prec);
  }
  if (itos(ground((GEN)p1[2])) != N) err(bugparier,"rootsof1 (bug1)");
  w = (GEN)p1[1]; ws = itos(w);
  if (ws == 2) { avma = av; return trivroots(nf); }

  d = decomp(w); list = (GEN)p1[3]; k = lg(list);
  for (i=1; i<k; i++)
  {
    p1 = (GEN)list[i];
    p1 = is_primitive_root(nf,d,p1,ws);
    if (p1) break;
  }
  if (!p1) err(bugparier,"rootsof1");
  y = cgetg(3, t_VEC);
  y[1] = lstoi(ws);
  y[2] = (long)p1; return gerepilecopy(av, y);
}

/*******************************************************************/
/*                                                                 */
/*                     DEDEKIND ZETA FUNCTION                      */
/*                                                                 */
/*******************************************************************/
static GEN
dirzetak0(GEN nf, long N0)
{
  GEN vect,p1,pol,disc,c,c2;
  gpmem_t av=avma;
  long i,j,k,limk,lx;
  ulong q,p,rem;
  byteptr d=diffptr;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};

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
  long N0,imin,imax,r1,r2,ru,R,N,i,j,k,n;
  gpmem_t av,av2,tetpil;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  stackzone *zone, *zone0, *zone1;

  /*************** Calcul du residu et des constantes ***************/
  eps=gmul2n(gun,-bit_accuracy(prec)-6); p1=dbltor(0.5);
  nfz=cgetg(10,t_VEC);
  bnf=buchinit(pol,p1,p1,prec+1); prec=(prec<<1)-1;
  bnf = checkbnf_discard(bnf);
  Pi = mppi(prec); racpi=gsqrt(Pi,prec);

  /* Nb de classes et regulateur */
  nf=(GEN)bnf[7]; N=degpol(nf[1]);
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
    { fprintferr("\ninitzeta:\nN0 = %ld\n",N0); flusherr(); (void)timer2(); }

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
  (void)switch_stack(zone,1);
  tabcstn  = (GEN*) cgetg(N0+1,t_VEC);
  tabcstni = (GEN*) cgetg(N0+1,t_VEC);
  p1 = ginv(cst);
  for (i=1; i<=N0; i++) { tabcstni[i] = gun; tabcstn[i] = mulsr(i,p1); }
  (void)switch_stack(zone,0);

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
  ck_odd[1]=lsub((GEN)ck_odd[1],gmul(gr1,mplog2(prec)));
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
  aij=gerepilecopy(av,aij);
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
        gpmem_t av2 = avma;
        p2 = gmul((GEN)t[j], p1);
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
    (void)switch_stack(z, 1);
    for (n=1; n<=N0; n++)
      if (coef[n]) tabcstni[n] = mpmul(tabcstni[n],tabcstn[n]);
    /* come back */
    (void)switch_stack(z, 0);
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
  long ts = typ(s), r1,r2,ru,imax,i,j,k,N0,sl,prec,bigprec;
  gpmem_t av = avma;

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
