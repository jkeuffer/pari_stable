/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                         (first part)                            **/
/**                                                                 **/
/*********************************************************************/
/* $Id$ */
#include "pari.h"

/*********************************************************************/
/**                                                                 **/
/**                  ARITHMETIC FUNCTION PROTOTYPES                 **/
/**                                                                 **/
/*********************************************************************/
GEN
garith_proto(GEN f(GEN), GEN x, int do_error)
{
  long tx=typ(x),lx,i;
  GEN y;

  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i] = (long) garith_proto(f,(GEN) x[i], do_error);
    return y;
  }
  if (tx != t_INT && do_error) err(arither1);
  return f(x);
}

GEN
arith_proto(long f(GEN), GEN x, int do_error)
{
  long tx=typ(x),lx,i;
  GEN y;

  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i] = (long) arith_proto(f,(GEN) x[i], do_error);
    return y;
  }
  if (tx != t_INT && do_error) err(arither1);
  return stoi(f(x));
}

GEN
arith_proto2(long f(GEN,GEN), GEN x, GEN n)
{
  long l,i,tx = typ(x);
  GEN y;

  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i] = (long) arith_proto2(f,(GEN) x[i],n);
    return y;
  }
  if (tx != t_INT) err(arither1);
  tx=typ(n);
  if (is_matvec_t(tx))
  {
    l=lg(n); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i] = (long) arith_proto2(f,x,(GEN) n[i]);
    return y;
  }
  if (tx != t_INT) err(arither1);
  return stoi(f(x,n));
}

static GEN
arith_proto2gs(long f(GEN,long), GEN x, long y)
{
  long l,i,tx = typ(x);
  GEN t;

  if (is_matvec_t(tx))
  {
    l=lg(x); t=cgetg(l,tx);
    for (i=1; i<l; i++) t[i]= (long) arith_proto2gs(f,(GEN) x[i],y);
    return t;
  }
  if (tx != t_INT) err(arither1);
  return stoi(f(x,y));
}

GEN
garith_proto2gs(GEN f(GEN,long), GEN x, long y)
{
  long l,i,tx = typ(x);
  GEN t;

  if (is_matvec_t(tx))
  {
    l=lg(x); t=cgetg(l,tx);
    for (i=1; i<l; i++) t[i]= (long) garith_proto2gs(f,(GEN) x[i],y);
    return t;
  }
  if (tx != t_INT) err(arither1);
  return f(x,y);
}

/*********************************************************************/
/**                                                                 **/
/**               ORDER of INTEGERMOD x  in  (Z/nZ)*                **/
/**                                                                 **/
/*********************************************************************/

GEN
order(GEN x)
{
  long av=avma,av1,i,e;
  GEN o,m,p;

  if (typ(x) != t_INTMOD || !gcmp1(mppgcd((GEN) x[1],(GEN) x[2])))
    err(talker,"not an element of (Z/nZ)* in order");
  o=phi((GEN) x[1]); m=decomp(o);
  for (i = lg(m[1])-1; i; i--)
  {
    p=gcoeff(m,i,1); e=itos(gcoeff(m,i,2));
    do
    {
      GEN o1=divii(o,p), y=powgi(x,o1);
      if (!gcmp1((GEN)y[2])) break;
      e--; o = o1;
    }
    while (e);
  }
  av1=avma; return gerepile(av,av1,icopy(o));
}

/******************************************************************/
/*                                                                */
/*                 GENERATOR of (Z/mZ)*                           */
/*                                                                */
/******************************************************************/

GEN
ggener(GEN m)
{
  return garith_proto(gener,m,1);
}

GEN
gener(GEN m)
{
  long av=avma,av1,k,i,e;
  GEN x,t,q,p;

  if (typ(m) != t_INT) err(arither1);
  e = signe(m);
  if (!e) err(talker,"zero modulus in znprimroot");
  if (is_pm1(m)) { avma=av; return gmodulss(0,1); }
  if (e<0) m = absi(m);

  e = mod4(m);
  if (e == 0) /* m = 0 mod 4 */
  {
    if (cmpis(m,4)) err(generer); /* m != 4, non cyclic */
    return gmodulsg(3,m);
  }
  if (e == 2) /* m = 0 mod 2 */
  {
    q=shifti(m,-1); x = (GEN) gener(q)[2];
    if (!mod2(x)) x = addii(x,q);
    av1=avma; return gerepile(av,av1,gmodulcp(x,m));
  }

  t=decomp(m); if (lg(t[1]) != 2) err(generer);
  p=gcoeff(t,1,1); e=itos(gcoeff(t,1,2)); q=subis(p,1);
  if (e>=2)
  {
    x = (GEN) gener(p)[2];
    if (gcmp1(powmodulo(x,q, sqri(p)))) x = addii(x,p);
    av1=avma; return gerepile(av,av1,gmodulcp(x,m));
  }

  p=(GEN)decomp(q)[1]; k=lg(p)-1; x=stoi(1);
  for(;;)
  {
    x[2]++;
    if (gcmp1(mppgcd(m,x)))
    {
      for (i=k; i; i--)
	if (gcmp1(powmodulo(x, divii(q,(GEN)p[i]), m))) break;
      if (!i) break;
    }
  }
  av1=avma; return gerepile(av,av1,gmodulcp(x,m));
}

GEN
znstar(GEN n)
{
  GEN p1,z,q,u,v,d,list,ep,h,gen,moduli,p,a;
  long i,j,nbp,sizeh,av,tetpil;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n))
  {
    z=cgetg(4,t_VEC);
    z[1]=deux; p1=cgetg(2,t_VEC);
    z[2]=(long)p1; p1[1]=deux; p1=cgetg(2,t_VEC);
    z[3]=(long)p1; p1[1]=lneg(gun);
    return z;
  }
  av=avma; n=absi(n);
  if (cmpis(n,2)<=0)
  {
    avma=av; z=cgetg(4,t_VEC);
    z[1]=un;
    z[2]=lgetg(1,t_VEC);
    z[3]=lgetg(1,t_VEC);
    return z;
  }
  list=factor(n); ep=(GEN)list[2]; list=(GEN)list[1]; nbp=lg(list)-1;
  h      = cgetg(nbp+2,t_VEC);
  gen    = cgetg(nbp+2,t_VEC);
  moduli = cgetg(nbp+2,t_VEC);
  switch(mod8(n))
  {
    case 0:
      h[1] = lmul2n(gun,itos((GEN)ep[1])-2); h[2] = deux;
      gen[1] = lstoi(5); gen[2] = laddis(gmul2n((GEN)h[1],1),-1);
      moduli[1] = moduli[2] = lmul2n(gun,itos((GEN)ep[1]));
      sizeh = nbp+1; i=3; j=2; break;
    case 4:
      h[1] = deux;
      gen[1] = lstoi(3);
      moduli[1] = lmul2n(gun,itos((GEN)ep[1]));
      sizeh = nbp; i=j=2; break;
    case 2: case 6:
      sizeh = nbp-1; i=1; j=2; break;
    default: /* 1, 3, 5, 7 */
      sizeh = nbp; i=j=1;
  }
  for ( ; j<=nbp; i++,j++)
  {
    p = (GEN)list[j]; q = gpuigs(p, itos((GEN)ep[j])-1);
    h[i] = lmulii(addis(p,-1),q); p1 = mulii(p,q);
    gen[i] = gener(p1)[2];
    moduli[i] = (long)p1;
  }
#if 0
  if (nbp == 1 && is_pm1(ep[1]))
    gen[1] = lmodulcp((GEN)gen[1],n);
  else
#endif
    for (i=1; i<=sizeh; i++)
    {
      q = (GEN)moduli[i]; a = (GEN)gen[i];
      u = mpinvmod(q,divii(n,q));
      gen[i] = lmodulcp(addii(a,mulii(mulii(subsi(1,a),u),q)), n);
    }
  
  for (i=sizeh; i>=2; i--)
    for (j=i-1; j>=1; j--)
      if (!divise((GEN)h[j],(GEN)h[i]))
      {
	d=bezout((GEN)h[i],(GEN)h[j],&u,&v);
        q=divii((GEN)h[j],d);
	h[j]=(long)mulii((GEN)h[i],q); h[i]=(long)d;
	gen[j]=ldiv((GEN)gen[j], (GEN)gen[i]);
	gen[i]=lmul((GEN)gen[i], powgi((GEN)gen[j], mulii(v,q)));
      }
  q=gun; for (i=1; i<=sizeh && !gcmp1((GEN)h[i]); i++) q=mulii(q,(GEN)h[i]);
  setlg(h,i); setlg(gen,i); z=cgetg(4,t_VEC);
  z[1]=(long)q; z[2]=(long)h; z[3]=(long)gen;
  tetpil=avma; return gerepile(av,tetpil,gcopy(z));
}

/*********************************************************************/
/**                                                                 **/
/**                     INTEGRAL SQUARE ROOT                        **/
/**                                                                 **/
/*********************************************************************/

GEN
gracine(GEN a)
{
  return garith_proto(racine,a,1); /* hm. --GN */
}

GEN
racine(GEN a)
{
  GEN x,y,z;
  long av,k;

  if (typ(a) != t_INT) err(arither1);
  switch (signe(a))
  {
    case 0: return gzero;
    case -1:
      x=cgetg(3,t_COMPLEX); x[1]=zero;
      setsigne(a,1); x[2]= (long)racine(a); setsigne(a,-1);
      return x;

    case 1:
      av=avma; k = (long) sqrt((double)(ulong)a[2]);
      x = shifti(stoi(k+1), (lgefint(a)-3)*(BITS_IN_LONG/2));
      do
      {
        z = shifti(addii(x,divii(a,x)), -1);
	y = x; x = z;
      }
      while (cmpii(x,y) < 0);
      avma = (long)y; return gerepileuptoint(av,y);
  }
  return NULL; /* not reached */
}

/*********************************************************************/
/**                                                                 **/
/**                      PERFECT SQUARE                             **/
/**                                                                 **/
/*********************************************************************/

long
carrecomplet(GEN x, GEN *pt)
{
  static int carresmod64[]={
    1,1,0,0,1,0,0,0,0,1, 0,0,0,0,0,0,1,1,0,0,
    0,0,0,0,0,1,0,0,0,0, 0,0,0,1,0,0,1,0,0,0,
    0,1,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,1,0,0,
    0,0,0,0};
  static int carresmod63[]={
    1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,1,0,1,0,
    0,0,1,0,0,1,0,0,1,0, 0,0,0,0,0,0,1,1,0,0,
    0,0,0,1,0,0,1,0,0,1, 0,0,0,0,0,0,0,0,1,0,
    0,0,0};
  static int carresmod65[]={
    1,1,0,0,1,0,0,0,0,1, 1,0,0,0,1,0,1,0,0,0,
    0,0,0,0,0,1,1,0,0,1, 1,0,0,0,0,1,1,0,0,1,
    1,0,0,0,0,0,0,0,0,1, 0,1,0,0,0,1,1,0,0,0,
    0,1,0,0,1};
  static int carresmod11[]={1,1,0,1,1,1,0,0,0,1,0};

  long av;
  GEN y;

  switch(signe(x))
  {
    case -1: return 0;
    case 0: if (pt) *pt=gzero; return 1;
    case 1: if (!carresmod64[mod64(x)]) return 0;
  }
  if (!carresmod63[smodis(x,63)]) return 0;
  if (!carresmod65[smodis(x,65)]) return 0;
  if (!carresmod11[smodis(x,11)]) return 0;
  av=avma; y=racine(x);
  if (!egalii(sqri(y),x)) { avma=av; return 0; }
  if (pt) { *pt = y; avma=(long)y; } else avma=av; 
  return 1;
}

static GEN
polcarrecomplet(GEN x, GEN *pt)
{
  long i,l,av,av2;
  GEN y,a,b;

  if (!signe(x)) return gun;
  l=lgef(x); if ((l&1) == 0) return gzero; /* odd degree */
  i=2; while (isexactzero((GEN)x[i])) i++;
  if (i&1) return gzero;
  av2 = avma; a = (GEN)x[i];
  switch (typ(a))
  {
    case t_POL: case t_INT:
      y = gcarrecomplet(a,&b); break;
    default:
      y = gcarreparfait(a); b = NULL; break;
  }
  if (y == gzero) { avma = av2; return gzero; }
  av = avma; x = gdiv(x,a);
  y = gtrunc(gsqrt(greffe(x,l,1),0)); av2 = avma;
  if (!gegal(gsqr(y), x)) { avma=av; return gzero; }
  if (pt)
  { 
    avma = av2; 
    if (!gcmp1(a))
    {
      if (!b) b = gsqrt(a,DEFAULTPREC);
      y = gmul(b,y);
    }
    *pt = gerepileupto(av,y);
  }
  else avma = av;
  return gun;
}

GEN
gcarrecomplet(GEN x, GEN *pt)
{
  long tx = typ(x),l,i;
  GEN z,y,p,t;

  if (!pt) return gcarreparfait(x);
  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx); z=cgetg(l,tx);
    for (i=1; i<l; i++)
    {
      t=gcarrecomplet((GEN)x[i],&p);
      y[i] = (long)t;
      z[i] = gcmp0(t)? zero: (long)p;
    }
    *pt=z; return y;
  }
  if (tx == t_POL) return polcarrecomplet(x,pt);
  if (tx != t_INT) err(arither1);
  return stoi(carrecomplet(x,pt));
}

GEN
gcarreparfait(GEN x)
{
  GEN p1,p2,p3,p4;
  long tx=typ(x),l,i,av,v;

  switch(tx)
  {
    case t_INT:
      return carreparfait(x)? gun: gzero;

    case t_REAL:
      return (signe(x)>=0)? gun: gzero;

    case t_INTMOD:
      if (!signe(x[2])) return gun;
      av=avma; p1=factor(absi((GEN)x[1]));
      p2=(GEN)p1[1]; l=lg(p2); p3=(GEN)p1[2];
      for (i=1; i<l; i++)
      {
	v = pvaluation((GEN)x[2],(GEN)p2[i],&p4);
	if (v < itos((GEN)p3[i]))
	{
	  if (v&1) break;
	  if (!egalii((GEN)p2[i], gdeux))
            { if (kronecker(p4,(GEN)p2[i]) == -1) break; }
          else
	  {
	    v = itos((GEN)p3[i]) - v;
	    if ((v>=3 && mod8(p4) != 1 ) ||
	        (v==2 && mod4(p4) != 1)) break;
	  }
	}
      }
      avma=av; return i<l? gzero: gun;

    case t_FRAC: case t_FRACN:
      av=avma; l=carreparfait(mulii((GEN)x[1],(GEN)x[2]));
      avma=av; return l? gun: gzero;

    case t_COMPLEX:
      return gun;

    case t_PADIC:
      p4=(GEN)x[4]; if (!signe(p4)) return gun;
      if (valp(x)&1) return gzero;
      if (cmpis((GEN)x[2],2))
        return (kronecker((GEN)x[4],(GEN)x[2])== -1)? gzero: gun;

      v=precp(x); /* here p=2 */
      if ((v>=3 && mod8(p4) != 1 ) ||
          (v==2 && mod4(p4) != 1)) return gzero;
      return gun;

    case t_POL:
      return polcarrecomplet(x,NULL);

    case t_SER:
      if (!signe(x)) return gun;
      if (valp(x)&1) return gzero;
      return gcarreparfait((GEN)x[2]);

    case t_RFRAC: case t_RFRACN:
      av=avma;
      l=itos(gcarreparfait(gmul((GEN)x[1],(GEN)x[2])));
      avma=av; return stoi(l);

    case t_QFR: case t_QFI:
      return gcarreparfait((GEN)x[1]);

    case t_VEC: case t_COL: case t_MAT:
      l=lg(x); p1=cgetg(l,tx);
      for (i=1; i<l; i++) p1[i]=(long)gcarreparfait((GEN)x[i]);
      return p1;
  }
  err(typeer,"issquare");
  return NULL; /* not reached */
}

/*********************************************************************/
/**                                                                 **/
/**                        KRONECKER SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/
#define ome(t) (labs(mod8(t)-4) == 1)

GEN
gkronecker(GEN x, GEN y)
{
  return arith_proto2(kronecker,x,y);
}

long
kronecker(GEN x, GEN y)
{
  GEN z;
  long av,r,s=1;

  av=avma;
  switch (signe(y))
  {
    case -1: y=negi(y); if (signe(x)<0) s= -1; break;
    case 0: return is_pm1(x);
  }
  r=vali(y);
  if (r)
  {
    if (mpodd(x))
    {
      if (odd(r) && ome(x)) s= -s;
      y=shifti(y,-r);
    }
    else { avma=av; return 0; }
  }
  x=modii(x,y);
  while (signe(x))
  {
    r=vali(x);
    if (r)
    {
      if (odd(r) && ome(y)) s= -s;
      x=shifti(x,-r);
    }
    /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
    if (y[lgefint(y)-1]&2 && x[lgefint(x)-1]&2) s = -s;
    z=resii(y,x); y=x; x=z;
  }
  avma=av; return is_pm1(y)? s: 0;
}

GEN
gkrogs(GEN x, long y)
{
  return arith_proto2gs(krogs,x,y);
}

long
krogs(GEN x, long y)
{
  long av,r,s=1,x1,z;

  av=avma;
  if (y<=0)
  {
    if (y) { y = -y; if (signe(x)<0) s = -1; }
    else  return is_pm1(x);
  }
  r=vals(y);
  if (r)
  {
    if (mpodd(x))
    {
      if (odd(r) && ome(x)) s= -s;
      y>>=r;
    }
    else return 0;
  }
  x1=smodis(x,y);
  while (x1)
  {
    r=vals(x1);
    if (r)
    {
      if (odd(r) && (labs((y&7)-4)==1)) s= -s;
      x1>>=r;
    }
    if (y&2 && x1&2) s= -s;
    z=y%x1; y=x1; x1=z;
  }
  avma=av; return (y==1)? s: 0;
}

long
krosg(long s, GEN x)
{
  long av = avma, y = kronecker(stoi(s),x);
  avma = av; return y;
}

long
kross(long x, long y)
{
  long r,s=1,x1,z;

  if (y<=0)
  {
    if (y) { y= -y; if (x<0) s = -1; }
    else  return (labs(x)==1);
  }
  r=vals(y);
  if (r)
  {
    if (odd(x))
    {
      if (odd(r) && labs((x&7)-4) == 1) s = -s;
      y>>=r;
    }
    else return 0;
  }
  x1=x%y; if (x1<0) x1+=y;
  while (x1)
  {
    r=vals(x1);
    if (r)
    {
      if (odd(r) && labs((y&7)-4) == 1) s= -s;
      x1>>=r;
    }
    if (y&2 && x1&2) s= -s;
    z=y%x1; y=x1; x1=z;
  }
  return (y==1)? s: 0;
}

long
hil0(GEN x, GEN y, GEN p)
{
  return p? hil(x,y,p): hil(x,y,gzero);
}

#define eps(t) (((signe(t)*(t[lgefint(t)-1]))&3)==3)
long
hil(GEN x, GEN y, GEN p)
{
  long a,b,av,tx,ty,z;
  GEN p1,p2,u,v;

  if (gcmp0(x) || gcmp0(y)) return 0;
  av=avma; tx=typ(x); ty=typ(y);
  if (tx>ty) { p1=x; x=y; y=p1; a=tx,tx=ty; ty=a; }
  switch(tx)
  {
    case t_INT:
      switch(ty)
      {
	case t_INT:
	  if (signe(p)<=0)
	    return (signe(x)<0 && signe(y)<0)? -1: 1;
	  a = odd(pvaluation(x,p,&u));
          b = odd(pvaluation(y,p,&v));
	  if (egalii(p,gdeux))
          {
	    z = (eps(u) && eps(v))? -1: 1;
	    if (a && ome(v)) z= -z;
	    if (b && ome(u)) z= -z;
          }
          else
	  {
	    z = (a && b && eps(p))? -1: 1;
	    if (a && kronecker(v,p)<0) z= -z;
	    if (b && kronecker(u,p)<0) z= -z;
	  }
	  avma=av; return z;
	case t_REAL:
	  return (signe(x)<0 && signe(y)<0)? -1: 1;
	case t_INTMOD:
	  if (egalii(gdeux,(GEN)y[1])) err(hiler1);
	  return hil(x,(GEN)y[2],(GEN)y[1]);
	case t_FRAC: case t_FRACN:
	  p1=mulii((GEN)y[1],(GEN)y[2]); z=hil(x,p1,p);
	  avma=av; return z;
	case t_PADIC:
	  if (egalii(gdeux,(GEN)y[2]) && precp(y) <= 2) err(hiler1);
	  p1 = odd(valp(y))? mulii((GEN)y[2],(GEN)y[4]): (GEN)y[4];
	  z=hil(x,p1,(GEN)y[2]); avma=av; return z;
      }
      break;

    case t_REAL:
      if (! is_frac_t(ty)) break;
      if (signe(x) > 0) return 1;
      return signe(y[1])*signe(y[2]);

    case t_INTMOD:
      if (egalii(gdeux,(GEN)y[1])) err(hiler1);
      switch(ty)
      {
        case t_INTMOD:
          if (!egalii((GEN)x[1],(GEN)y[1])) break;
          return hil((GEN)x[2],(GEN)y[2],(GEN)x[1]);
        case t_FRAC: case t_FRACN:
	  return hil((GEN)x[2],y,(GEN)x[1]);
        case t_PADIC:
          if (!egalii((GEN)x[1],(GEN)y[2])) break;
          return hil((GEN)x[2],y,(GEN)x[1]);
      }
      break;

    case t_FRAC: case t_FRACN:
      p1=mulii((GEN)x[1],(GEN)x[2]);
      switch(ty)
      {
	case t_FRAC: case t_FRACN:
	  p2=mulii((GEN)y[1],(GEN)y[2]);
	  z=hil(p1,p2,p); avma=av; return z;
	case t_PADIC:
	  z=hil(p1,y,NULL); avma=av; return z;
      }
      break;

    case t_PADIC:
      if (ty != t_PADIC || !egalii((GEN)x[2],(GEN)y[2])) break;
      p1 = odd(valp(x))? mulii((GEN)x[2],(GEN)x[4]): (GEN)x[4];
      p2 = odd(valp(y))? mulii((GEN)y[2],(GEN)y[4]): (GEN)y[4];
      z=hil(p1,p2,(GEN)x[2]); avma=av; return z;
  }
  err(talker,"forbidden or incompatible types in hil");
  return 0; /* not reached */
}
#undef eps
#undef ome

/*******************************************************************/
/*                                                                 */
/*                       SQUARE ROOT MODULO p                      */
/*                                                                 */
/*******************************************************************/

#define sqrmod(x,p) (resii(sqri(x),p))

/* Assume p is prime. return NULL if (a,p) = -1 */
GEN
mpsqrtmod(GEN a, GEN p)
{
  long av = avma, av1,lim,i,k,e;
  GEN p1,q,v,y,w,m;

  if (typ(a) != t_INT || typ(p) != t_INT) err(arither1);
  if (signe(p) <= 0 || is_pm1(p)) err(talker,"not a prime in mpsqrtmod");
  p1 = addsi(-1,p); e = vali(p1);
  if (e == 0) /* p = 2 */
  {
    avma = av;
    if (!egalii(p, gdeux))
      err(talker,"composite modulus in mpsqrtmod: %Z",p);
    if (!signe(a) || !mod2(a)) return gzero;
    return gun;
  }
  q = shifti(p1,-e); /* q = (p-1)/2^oo is odd */
  if (e == 1) y = p1;
  else /* look for an odd power of a primitive root */
    for (k=2; ; k++)
    { /* loop terminates for k < p (even if p composite) */
  
      i = krosg(k,p);
      if (i >= 0)
      {
        if (i) continue;
        err(talker,"composite modulus in mpsqrtmod: %Z",p);
      }
      av1 = avma;
      y = m = powmodulo(stoi(k),q,p);
      for (i=1; i<e; i++)
	if (gcmp1(m = sqrmod(m,p))) break;
      if (i == e) break; /* success */
      avma = av1;
    }

  p1 = powmodulo(a, shifti(q,-1), p); /* a ^ [(q-1)/2] */
  if (!signe(p1)) { avma=av; return gzero; }
  v = modii(mulii(a, p1), p);
  w = modii(mulii(v, p1), p);
  lim = stack_lim(av,1);
  while (!gcmp1(w))
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = sqrmod(w,p);
    for (k=1; !gcmp1(p1) && k < e; k++) p1 = sqrmod(p1,p);
    if (k == e) { avma=av; return NULL; } /* p composite or (a/p) != 1 */
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = sqrmod(p1,p);
    y = sqrmod(p1, p); e = k;
    w = modii(mulii(y, w), p);
    v = modii(mulii(v, p1), p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[3]; gptr[0]=&y; gptr[1]=&w; gptr[2]=&v;
      if(DEBUGMEM>1) err(warnmem,"mpsqrtmod");
      gerepilemany(av,gptr,3);
    }
  }
  av1 = avma;
  p1 = subii(p,v); if (cmpii(v,p1) > 0) v = p1; else avma = av1;
  return gerepileuptoint(av, v);
}

/*******************************************************************/
/*                                                                 */
/*                       n-th ROOT MODULO p                        */
/*                                                                 */
/*******************************************************************/

/* UNCLEAN
 * p-1=l^e*r
 * l doit etre premier
 * q=p-1
 * q=(l^e)*r
 * e>=1
 * pgcd(r,l)=1
 * return a non l-power residue and set zeta to a primitive l root of unity.
 */

static GEN
mplgenmod(GEN l, long e, GEN r,GEN p,GEN *zeta)
{
  ulong av1;
  GEN m,m1;
  long k,i; 
  av1 = avma;
  for (k=1; ; k++)
  {
    m1 = m = powmodulo(stoi(k+1),r,p);
    for (i=1; i<e; i++)
      if (gcmp1(m=powmodulo(m,l,p))) break;
    if (i==e) break;
    avma = av1;
  }
  *zeta=m;
  return m1;
}
/* resoud x^l=a mod (p)
 * l doit etre premier
 * q=p-1
 * q=(l^e)*r
 * e>=1
 * pgcd(r,l)=1
 * m=y^(q/l)
 * y n'est pas une puissance l-ieme
 * m!=1
 * ouf!
 * FIXME: use baby-step giant-step.
 */
static GEN
mpsqrtlmod(GEN a, GEN l, GEN p, GEN q,long e, GEN r, GEN y, GEN m)
{
  ulong av = avma, tetpil,lim;
  long i,k;
  GEN p1,p2,u1,u2,v,w,z;
  /* y contient un generateur de (Z/pZ)^* eleve a la puis (p-1)/(l^e) */
  bezout(r,l,&u1,&u2);
  v=powmodulo(a,u2,p);
  w=powmodulo(a,modii(mulii(negi(u1),r),q),p);
  lim = stack_lim(av,1);
  while (!gcmp1(w))
  {
    /* if p is not prime, next loop will not end */
    k=0;
    p1=w;
    do
    {
      z=p1;
      p1=powmodulo(p1,l,p);
      k++;
    }while(!gcmp1(p1));
    if (k==e) { avma=av; return NULL; }
    p2 = modii(mulii(z,m),p);
    for(i=1; !gcmp1(p2); i++) p2 = modii(mulii(p2,m),p);/*should be a baby step
							  giant step instead*/
    p1=powmodulo(y,modii(mulsi(i,gpowgs(l,e-k-1)),q),p);
    m=powmodulo(m,stoi(i),p);
    e = k;
    v = modii(mulii(p1,v),p);
    y = powmodulo(p1,l,p);
    w = modii(mulii(y,w),p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4];
      if(DEBUGMEM>1) err(warnmem,"mpsqrtlmod");
      gptr[0]=&y; gptr[1]=&v; gptr[2]=&w; gptr[3]=&m;
      gerepilemany(av,gptr,4);
    }
  }
  tetpil=avma; return gerepile(av,tetpil,icopy(v));
}
/* a and n are integers, p is prime

return a solution of 

x^n=a mod p 

1)If there is no solution return NULL and if zetan is not NULL set zetan to gzero.

2) If there is solution there are exactly  m=gcd(p-1,n) of them.

If zetan is not NULL, zetan is set to a primitive mth root of unity so that
the set of solutions is {x*zetan^k;k=0 to m-1}

If a=0 ,return 0 and if zetan is not NULL zetan is set to gun
*/
GEN 
mpsqrtnmod(GEN a, GEN n, GEN p, GEN *zetan)
{
  ulong ltop=avma,lbot=0,av1,lim;
  GEN m,u1,u2;
  GEN q,z;
  GEN *gptr[2];
  if (typ(a) != t_INT || typ(n) != t_INT || typ(p)!=t_INT)
    err(typeer,"mpsqrtnmod");
  if(!signe(n))
    err(talker,"1/0 exponent in mpsqrtnmod");
  if(gcmp1(n)) {if (zetan) *zetan=gun;return gcopy(a);}
  a=modii(a,p);
  if(gcmp0(a)) {if (zetan) *zetan=gun;avma=ltop;return gzero;}
  q=addsi(-1,p);
  m=bezout(n,q,&u1,&u2);
  if (zetan) z=gun;
  lim=stack_lim(ltop,1);
  if (!gcmp1(m))
  {
    GEN F=decomp(m);
    long i,j,e; 
    GEN r,zeta,y,l;
    av1=avma;
    for (i = lg(F[1])-1; i; i--)
    {
      l=gcoeff(F,i,1); j=itos(gcoeff(F,i,2));
      e=pvaluation(q,l,&r);
      y=mplgenmod(l,e,r,p,&zeta);
      if (zetan) z=modii(mulii(z,powmodulo(y,gpowgs(l,e-j),p)),p);
      for(;j;j--)
      {
	lbot=avma;
	a=mpsqrtlmod(a,l,p,q,e,r,y,zeta);
	if (!a){avma=ltop;if (zetan)  *zetan=gzero;return NULL;}
	if (low_stack(lim, stack_lim(ltop,1)))/* n can have lots of prime factors*/
	{
	  if(DEBUGMEM>1) err(warnmem,"ffsqrtnmod");
	  if (zetan)
	  {
	    z=gcopy(z);
	    gptr[0]=&a;gptr[1]=&z;
	    gerepilemanysp(av1,lbot,gptr,2);
	  }
	  else
	    a=gerepileupto(av1,a);
	}
      }
    }
  }
  if (cmpii(m,n))
  {
    GEN b=modii(u1,q);
    lbot=avma;
    a=powmodulo(a,b,p);
  }
  if (zetan)
  {
    *zetan=gcopy(z);
    gptr[0]=&a;gptr[1]=zetan;
    gerepilemanysp(ltop,lbot,gptr,2);
  }
  else
    a=gerepileupto(ltop,a);
  return a;
}

/*********************************************************************/
/**                                                                 **/
/**                        GCD & BEZOUT                             **/
/**                                                                 **/
/*********************************************************************/

/* Ultra-fast private ulong gcd for trial divisions.  Called with y odd;
   x can be arbitrary (but will most of the time be smaller than y).
   Will also be used from inside ifactor2.c, so it's `semi-private' really.
   --GN */

/* Gotos are Harmful, and Programming is a Science.  E.W.Dijkstra. */
ulong
ugcd(ulong x, ulong y)         /* assume y&1==1, y > 1 */
{
  if (!x) return y;
  /* fix up x */
  while (!(x&1)) x>>=1;
  if (x==1) return 1;
  if (x==y) return y;
  else if (x>y) goto xislarger;/* will be rare, given how we'll use this */
  /* loop invariants: x,y odd and distinct. */
 yislarger:
  if ((x^y)&2)                 /* ...01, ...11 or vice versa */
    y=(x>>2)+(y>>2)+1;         /* ==(x+y)>>2 except it can't overflow */
  else                         /* ...01,...01 or ...11,...11 */
    y=(y-x)>>2;                /* now y!=0 in either case */
  while (!(y&1)) y>>=1;        /* kill any windfall-gained powers of 2 */
  if (y==1) return 1;          /* comparand == return value... */
  if (x==y) return y;          /* this and the next is just one comparison */
  else if (x<y) goto yislarger;/* else fall through to xislarger */

 xislarger:                    /* same as above, seen through a mirror */
  if ((x^y)&2)
    x=(x>>2)+(y>>2)+1;
  else
    x=(x-y)>>2;                /* x!=0 */
  while (!(x&1)) x>>=1;
  if (x==1) return 1;
  if (x==y) return y;
  else if (x>y) goto xislarger;/* again, a decent [g]cc should notice that
                                  it can re-use the comparison */
  goto yislarger;
}
/* Gotos are useful, and Programming is an Art.  D.E.Knuth. */
/* PS: Of course written with Dijkstra's lessons firmly in mind... --GN */

/* modified right shift binary algorithm with at most one division */
long
cgcd(long a,long b)
{
  long v;
  a=labs(a); if (!b) return a;
  b=labs(b); if (!a) return b;
  if (a>b) { a %= b; if (!a) return b; }
  else { b %= a; if (!b) return a; }
  v=vals(a|b); a>>=v; b>>=v;
  if (a==1 || b==1) return 1L<<v;
  if (b&1)
    return ((long)ugcd((ulong)a, (ulong)b)) << v;
  else
    return ((long)ugcd((ulong)b, (ulong)a)) << v;
}
long
clcm(long a,long b)
{
  long d;
  if(!a) return 0;
  d=cgcd(a,b);
  if(d!=1) return a*(b/d);
  return a*b;
}

/* assume a>b>0, return gcd(a,b) as a GEN (for mppgcd) */
static GEN
mppgcd_cgcd(ulong a, ulong b)
{
  GEN r = cgeti(3);
  long v;

  r[1] = evalsigne(1)|evallgefint(3);
  a %= b; if (!a) { r[2]=(long)b; return r; }
  v=vals(a|b); a>>=v; b>>=v;
  if (a==1 || b==1) { r[2]=(long)(1UL<<v); return r; }
  if (b&1)
    r[2] = (long)(ugcd((ulong)a, (ulong)b) << v);
  else
    r[2] = (long)(ugcd((ulong)b, (ulong)a) << v);
  return r;
}

void mppgcd_plus_minus(GEN x, GEN y, GEN t);
ulong mppgcd_resiu(GEN y, ulong x);

/* uses modified right-shift binary algorithm now --GN 1998Jul23 */
GEN
mppgcd(GEN a, GEN b)
{
  long av,v,w;
  GEN t, p1;

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  switch (absi_cmp(a,b))
  {
    case 0: return absi(a);
    case -1: t=b; b=a; a=t;
  }
  if (!signe(b)) return absi(a);
  /* here |a|>|b|>0. Try single precision first */
  if (lgefint(a)==3)
    return mppgcd_cgcd((ulong)a[2], (ulong)b[2]);
  if (lgefint(b)==3)
  {
    ulong u = mppgcd_resiu(a,(ulong)b[2]);
    if (!u) return absi(b);
    return mppgcd_cgcd((ulong)b[2], u);
  }

  /* larger than gcd: "avma=av" gerepile (erasing t) is valid */
  av = avma; new_chunk(lgefint(b));
  t = resii(a,b);
  if (!signe(t)) { avma=av; return absi(b); }

  a = b; b = t;
  v = vali(a); a = shifti(a,-v); setsigne(a,1);
  w = vali(b); b = shifti(b,-w); setsigne(b,1);
  if (w < v) v = w;
  switch(absi_cmp(a,b))
  {
    case  0: avma=av; a=shifti(a,v); return a;
    case -1: p1=b; b=a; a=p1;
  }
  if (is_pm1(b)) { avma=av; return shifti(gun,v); }

  /* we have three consecutive memory locations: a,b,t.
   * All computations are done in place */

  /* a and b are odd now, and a>b>1 */
  while (lgefint(a) > 3)
  {
    /* if a=b mod 4 set t=a-b, otherwise t=a+b, then strip powers of 2 */
    /* so that t <= (a+b)/4 < a/2 */
    mppgcd_plus_minus(a,b, t);
    if (is_pm1(t)) { avma=av; return shifti(gun,v); }
    switch(absi_cmp(t,b))
    {
      case -1: p1 = a; a = b; b = t; t = p1; break;
      case  1: p1 = a; a = t; t = p1; break;
      case  0: avma = av; b=shifti(b,v); return b;
    }
  }
  {
    long r[] = {evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 0};
    r[2] = (long) ugcd((ulong)b[2], (ulong)a[2]);
    avma = av; return shifti(r,v);
  }
}
GEN
mpppcm(GEN x, GEN y)
{
  ulong av;
  GEN p1,p2;
  if (typ(x) != t_INT || typ(y) != t_INT) err(arither1);
  if (!signe(x)) return gzero;
  av = avma;
  p1 = mppgcd(x,y); if (!is_pm1(p1)) y = divii(y,p1);
  p2 = mulii(x,y);
  if (signe(p2) < 0) setsigne(p2,1);
  return gerepileupto(av, p2);
}
/* Extended bezout. Return d=pgcd(a,b) and &u,&v */
long
cbezout(long a,long b,long *uu,long *vv)
{
  long av=avma,v,q,u,t,s, d = labs(a), r = labs(b);
  GEN p1;

  if (!b)
  {
    *vv=0;
    if (!a) { *uu=1; return 1; }
    if (a<0)
      { *uu=-1; return -a; }
    else
      { *uu= 1; return  a; }
  }
  u=1; t=0;
  for(;;)
  {
    if (!r)
    {
      if (a<0) u = -u;
      p1 = mulss(a,u); s = signe(p1);
      if (!s) v = d / b;
      else if (!is_bigint(p1))
      {
        ulong ul;
        long sb = (b<0);
        b = labs(b);
        if (s < 0)
        {
          ul = (p1[2]+d);
          ul /= b; v = sb? -(long)ul: (long)ul;
        }
        else
        {
          ul = p1[2]-d;
          ul /= b; v = sb? (long)ul: -(long)ul;
        }
      }
      else v = - itos(divis(addsi(-d,p1), b));
      avma=av; *uu = u; *vv = v; return d;
    }
    v=d; d=r; q = v/r; r = v - q*r;
    v=t; t = u - q*t; u=v;
  }
}

GEN
bezout(GEN a, GEN b, GEN *ptu, GEN *ptv)
{
  GEN u,v,t,x,y,q,r, *tmp;
  long av;

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  if (absi_cmp(a,b) < 0)
  {
    t=b; b=a; a=t;
    tmp=ptu; ptu=ptv; ptv=tmp;
  }
  /* now |a| >= |b| */
  if (!signe(b))
  {
    *ptv = gzero;
    switch(signe(a))
    {
      case  0: *ptu = gun; return gzero;
      case  1: *ptu = gun; return icopy(a);
      case -1: *ptu = negi(gun); return negi(a);
    }
  }
  if (!is_bigint(a))
  {
    long uu,vv, dd = cbezout(itos(a),itos(b),&uu,&vv);
    *ptu = stoi(uu); *ptv = stoi(vv); return stoi(dd);
  }
  av = avma;
  (void)new_chunk(lgefint(b) + (lgefint(a)<<1)); /* room for x, u and v */
  x = a; y = b; u = gun; v = gzero;
  do
  {
    q = dvmdii(x,y,&r);
    v = subii(v, mulii(q,u));
    t=v; v=u; u=t;
    x=y; y=r;
  } while (signe(y));
  u = divii(subii(x, mulii(b,v)), a);
  avma = av; x = icopy(x); v = icopy(v); u = icopy(u);
  if (signe(x) < 0)
  {
    setsigne(x,1);
    setsigne(u,-signe(u));
    setsigne(v,-signe(v));
  }
  *ptu = u; *ptv = v; return x;
}

/*********************************************************************/
/**                                                                 **/
/**                      CHINESE REMAINDERS                         **/
/**                                                                 **/
/*********************************************************************/

/*  P.M. & M.H.
 *
 *  Chinese Remainder Theorem.  x and y must have the same type (integermod,
 *  polymod, or polynomial/vector/matrix recursively constructed with these
 *  as coefficients). Creates (with the same type) a z in the same residue
 *  class as x and the same residue class as y, if it is possible.
 *
 *  We also allow (during recursion) two identical objects even if they are
 *  not integermod or polymod. For example, if
 *
 *    x = [1. mod(5, 11), mod(X + mod(2, 7), X^2 + 1)]
 *    y = [1, mod(7, 17), mod(X + mod(0, 3), X^2 + 1)],
 *
 *  then chinois(x, y) returns
 *
 *    [1, mod(16, 187), mod(X + mod(9, 21), X^2 + 1)]
 *
 *  Someone else may want to allow power series, complex numbers, and
 *  quadratic numbers.
 */
GEN
chinois(GEN x, GEN y)
{
  long i,lx,vx,av,tetpil, tx = typ(x);
  GEN z,p1,p2,d,u,v;

  if (gegal(x,y)) return gcopy(x);
  if (tx == typ(y)) switch(tx)
  {
    case t_POLMOD:
      if (gegal((GEN)x[1],(GEN)y[1]))  /* same modulus */
      {
	z=cgetg(3,tx);
	z[1]=lcopy((GEN)x[1]);
	z[2]=(long)chinois((GEN)x[2],(GEN)y[2]);
        return z;
      }  /* fall through */
    case t_INTMOD:
      z=cgetg(3,tx); av=avma;
      d=gbezout((GEN)x[1],(GEN)y[1],&u,&v);
      if (!gegal(gmod((GEN)x[2],d), gmod((GEN)y[2],d))) break;
      p1 = gdiv((GEN)x[1],d);
      p2 = gadd((GEN)x[2], gmul(gmul(u,p1), gadd((GEN)y[2],gneg((GEN)x[2]))));

      tetpil=avma; z[1]=lmul(p1,(GEN)y[1]); z[2]=lmod(p2,(GEN)z[1]);
      gerepilemanyvec(av,tetpil,z+1,2); return z;

    case t_POL:
      lx=lgef(x); vx=varn(x); z=cgetg(lx,tx);
      if (lx!=lgef(y) || vx!=varn(y)) break;
      z[1]=evalsigne(1)|evallgef(lx)|evalvarn(vx);
      for (i=2; i<lx; i++) z[i]=(long)chinois((GEN)x[i],(GEN)y[i]);
      return z;

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); z=cgetg(lx,tx); if (lx!=lg(y)) break;
      for (i=1; i<lx; i++) z[i]=(long)chinois((GEN)x[i],(GEN)y[i]);
      return z;
  }
  err(talker,"incompatible arguments in chinois");
  return NULL; /* not reached */
}

/* return lift(chinois(x2 mod x1, y2 mod y1))
 * assume(x1,y1)=1, xi,yi integers and z1 = x1*y1
 */
GEN
chinois_int_coprime(GEN x2, GEN y2, GEN x1, GEN y1, GEN z1)
{
  long av = avma;
  GEN ax,p1;
  (void)new_chunk((lgefint(z1)<<1)+lgefint(x1)+lgefint(y1));
  ax = mulii(mpinvmod(x1,y1), x1);
  p1 = addii(x2, mulii(ax, subii(y2,x2)));
  avma = av; return modii(p1,z1);
}

/*********************************************************************/
/**                                                                 **/
/**                      INVERSE MODULO b                           **/
/**                                                                 **/
/*********************************************************************/

GEN
mpinvmod(GEN a, GEN m)
{
  GEN res;
  if (! invmod(a,m,&res))
    err(talker,"impossible inverse modulo: %Z",gmodulcp(res,m));
  return res;
}

/*********************************************************************/
/**                                                                 **/
/**                   POWERING MODULO (A^N mod M)                   **/
/**                                                                 **/
/*********************************************************************/
GEN resiimul(GEN x, GEN y);
GEN resmod2n(GEN x, long y);
GEN _resii(GEN x, GEN y) { return resii(x,y); }

GEN
init_remainder(GEN M)
{
  GEN sM = cgetg(3, t_VEC);
  GEN Mr = cgetr(lgefint(M) + 1);
  affir(M, Mr);
  sM[1] = (long)M;
  sM[2] = (long)linv(Mr);
  return sM;
}

/* optimal on UltraSPARC */
static long RESIIMUL_LIMIT = 150;

void
setresiilimit(long n) { RESIIMUL_LIMIT = n; }

GEN
powmodulo(GEN A, GEN N, GEN M)
{
  GEN y;
  long av = avma,av1,lim,man,k,nb,s, *p;
  GEN (*mul)(GEN,GEN) = mulii;
  GEN (*res)(GEN,GEN) = _resii;

  if (typ(A) != t_INT || typ(N) != t_INT || typ(M) != t_INT) err(arither1);
  s = signe(N);
  if (!s)
  {
    k = signe(resii(A,M)); avma=av;
    return k? gun: gzero;
  }
  if (s < 0) { A = mpinvmod(A,M); N = absi(N); }
  else
  {
    A = modii(A,M);
    if (!signe(A)) { avma=av; return gzero; }
  }
  y = A;
  if (lgefint(y)==3) switch(y[2])
  {
    case 1: /* y = 1 */
      avma=av; return gun;
    case 2: /* y = 2, use shifti not mulii */
    mul = (GEN (*)(GEN,GEN))shifti; A = (GEN)1;
  }

  /* TODO: Move this out of here and use for general modular computations */
  if ((k = vali(M)) && k == expi(M))
  { /* M is a power of 2 */
    M = (GEN)k;
    res = (GEN(*)(GEN,GEN))resmod2n;
  }
  else if (lgefint(M) > RESIIMUL_LIMIT && (lgefint(N) > 3 || N[2] > 4))
  { /* compute x % M using multiplication by 1./M */
    M = init_remainder(M);
    res = (GEN(*)(GEN,GEN))resiimul;
  }

  p = N+2; man = *p; /* see puissii */
  k = 1+bfffo(man); man<<=k; k = BITS_IN_LONG-k;
  av1=avma; lim=stack_lim(av1,1);
  for (nb=lgefint(N)-2;;)
  {
    for (; k; man<<=1,k--)
    {
      y = res(sqri(y), M);
      if (man < 0) y = res(mul(y,A), M);
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"powmodulo");
        y = gerepileuptoint(av1,y);
      }
    }
    if (--nb == 0) break;
    man = *++p, k = BITS_IN_LONG;
  }
  return gerepileupto(av,y);
}

/*********************************************************************/
/**                                                                 **/
/**                NEXT / PRECEDING (PSEUDO) PRIME                  **/
/**                                                                 **/
/*********************************************************************/
GEN
gnextprime(GEN n)
{
  return garith_proto(nextprime,n,0);
}

GEN
gprecprime(GEN n)
{
  return garith_proto(precprime,n,0);
}

GEN
gisprime(GEN x, long flag)
{
  switch (flag)
  {
  case 0:
    return arith_proto(isprime,x,1);
  case 1:
    return garith_proto2gs(plisprime,x,0);
  case 2:
    return garith_proto2gs(plisprime,x,1);
  }
  err(flagerr,"gisprime");
  return 0;
}

long
isprime(GEN x)
{
  return millerrabin(x,10);
}

GEN
gispsp(GEN x)
{
  return arith_proto(ispsp,x,1);
}

long
ispsp(GEN x)
{
  return millerrabin(x,1);
}

GEN
gmillerrabin(GEN n, long k)
{
  return arith_proto2gs(millerrabin,n,k);
}

/*********************************************************************/
/**                                                                 **/
/**                    FUNDAMENTAL DISCRIMINANTS                    **/
/**                                                                 **/
/*********************************************************************/

/* gissquarefree, issquarefree moved into arith2.c with the other
   basic arithmetic functions (issquarefree is the square of the
   Moebius mu function, after all...) --GN */

GEN
gisfundamental(GEN x)
{
  return arith_proto(isfundamental,x,1);
}

long
isfundamental(GEN x)
{
  long av,r;
  GEN p1;

  if (gcmp0(x)) return 0;
  r=mod4(x);
  if (!r)
  {
    av=avma; p1=shifti(x,-2);
    r=mod4(p1); if (!r) return 0;
    if (signe(x)<0) r=4-r;
    r = (r==1)? 0: issquarefree(p1);
    avma=av; return r;
  }
  if (signe(x)<0) r=4-r;
  return (r==1) ? issquarefree(x) : 0;
}

GEN
quaddisc(GEN x)
{
  long av=avma,tetpil=avma,i,r,tx=typ(x);
  GEN p1,p2,f,s;

  if (tx != t_INT && ! is_frac_t(tx)) err(arither1);
  f=factor(x); p1=(GEN)f[1]; p2=(GEN)f[2];
  s=gun;
  for (i=1; i<lg(p1); i++)
    if ( odd(mael(p2,i,2)) ) { tetpil=avma; s=gmul(s,(GEN)p1[i]); }
  r=mod4(s); if (gsigne(x)<0) r=4-r;
  if (r>1) { tetpil=avma; s=shifti(s,2); }
  return gerepile(av,tetpil,s);
}

/*********************************************************************/
/**                                                                 **/
/**                              FACTORIAL                          **/
/**                                                                 **/
/*********************************************************************/
GEN muluu(ulong x, ulong y);

GEN
mpfact(long n)
{
  long lx, av = avma;
  ulong k,l;
  GEN x;

  if (n<2)
  {
    if (n<0) err(facter);
    return gun;
  }
  if (n < 60)
  {
    x = gdeux;
    for (k=3; k<=n; k++) x = mulsi(k,x);
    return gerepileuptoint(av,x);
  }
  lx = 1; x = cgetg(1 + n/2, t_VEC);
  for (k=2;; k++)
  {
    l = n+2-k; if (l <= k) break;
    x[lx++] = (long)muluu(k,l);
  }
  if (l == k) x[lx++] = lstoi(k);
  setlg(x, lx);
  return gerepileuptoint(av, divide_conquer_prod(x, mulii));
}

GEN
mpfactr(long n, long prec)
{
  long av = avma, lim,k;
  GEN f = cgetr(prec);

  affsr(1,f);
  if (n<2)
  {
    if (n<0) err(facter);
    return f;
  }
  lim = stack_lim(av,1);
  for (k=2; k<=n; k++)
  {
    f = mulsr(k,f);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"mpfactr k=%ld",k);
      f = gerepileuptoleaf(av,f);
    }
  }
  return gerepileuptoleaf(av,f);
}

/*******************************************************************/
/**                                                               **/
/**                      LUCAS & FIBONACCI                        **/
/**                                                               **/
/*******************************************************************/

void
lucas(long n, GEN *ln, GEN *ln1)
{
  long taille,av;
  GEN z,t;

  if (!n) { *ln=stoi(2); *ln1=stoi(1); return; }

  taille=(long)(pariC3*(1+labs(n))+3);
  *ln=cgeti(taille); *ln1=cgeti(taille);
  av=avma; lucas(n/2,&z,&t);
  switch(n % 4)
  {
    case -3:
      addsiz(2,sqri(z),*ln1);
      subiiz(addsi(1,mulii(z,t)),*ln1,*ln); break;
    case -2:
      addsiz(2,sqri(z),*ln); addsiz(1,mulii(z,t),*ln1); break;
    case -1:
      subisz(sqri(z),2,*ln1);
      subiiz(subis(mulii(z,t),1),*ln1,*ln); break;
    case  0: subisz(sqri(z),2,*ln); subisz(mulii(z,t),1,*ln1); break;
    case  1: subisz(mulii(z,t),1,*ln); addsiz(2,sqri(t),*ln1); break;
    case  2: addsiz(2,sqri(z),*ln); addsiz(1,mulii(z,t),*ln1); break;
    case  3: addsiz(1,mulii(z,t),*ln); subisz(sqri(t),2,*ln1);
  }
  avma=av;
}

GEN
fibo(long n)
{
  long av = avma;
  GEN ln,ln1;

  lucas(n-1,&ln,&ln1);
  return gerepileupto(av, divis(addii(shifti(ln,1),ln1), 5));
}

/*******************************************************************/
/*                                                                 */
/*                      CONTINUED FRACTIONS                        */
/*                                                                 */
/*******************************************************************/
static GEN sfcont2(GEN b, GEN x, long k);

GEN
gcf(GEN x)
{
  return sfcont(x,x,0);
}

GEN
gcf2(GEN b, GEN x)
{
  return contfrac0(x,b,0);
}

GEN
gboundcf(GEN x, long k)
{
  return sfcont(x,x,k);
}

GEN
contfrac0(GEN x, GEN b, long flag)
{
  long lb,tb,i;
  GEN y;

  if (!b || gcmp0(b)) return sfcont(x,x,flag);
  tb = typ(b);
  if (tb == t_INT) return sfcont(x,x,itos(b));
  if (! is_matvec_t(tb)) err(typeer,"contfrac0");

  lb=lg(b); if (lb==1) return cgetg(1,t_VEC);
  if (tb != t_MAT) return sfcont2(b,x,flag);
  if (lg(b[1])==1) return sfcont(x,x,flag);
  y = (GEN) gpmalloc(lb*sizeof(long));
  for (i=1; i<lb; i++) y[i]=coeff(b,1,i);
  x = sfcont2(y,x,flag); free(y); return x;
}

GEN
sfcont(GEN x, GEN x1, long k)
{
  long  av,lx=lg(x),tx=typ(x),e,i,j,l,l1,lx1,tetpil,f;
  GEN   y,p1,p2,p3,p4,yp;

  if (is_scalar_t(tx))
  {
    if (gcmp0(x)) { y=cgetg(2,t_VEC); y[1]=zero; return y; }
    switch(tx)
    {
      case t_INT:
        y=cgetg(2,t_VEC); y[1]=lcopy(x); return y;
      case t_REAL:
        l=avma; p1=cgetg(3,t_FRACN);
	p2 = rcopy(x); settyp(p2,t_INT); setlgefint(p2,lx);
	p1[1] = (long) p2; e = bit_accuracy(lx)-1-expo(x);
	if (e<0) err(talker,"integral part not significant in scfont");

	l1 = (e>>TWOPOTBITS_IN_LONG)+3; p2=cgeti(l1);
	p2[1]= evalsigne(1)|evallgefint(l1);
	p2[2]= (1L<<(e&(BITS_IN_LONG-1)));
	for (i=3; i<l1; i++) p2[i]=0;
	p1[2]=(long) p2; p3=cgetg(3,t_FRACN);
	p3[2]=lcopy(p2);
	p3[1]=laddsi(signe(x),(GEN)p1[1]);
	p1=sfcont(p1,p1,k); tetpil=avma;
	return gerepile(l,tetpil,sfcont(p3,p1,k));

      case t_FRAC: case t_FRACN:
        l=avma; lx1=lgefint(x[2]);
	l1 = (long) ((double) BYTES_IN_LONG/4.0*46.093443*(lx1-2)+3);
        if (k>0 && ++k > 0 && l1 > k) l1 = k; /* beware overflow */
	if (l1>LGBITS) l1=LGBITS;
	if (lgefint(x[1]) >= lx1) p1=icopy((GEN)x[1]);
	else affii((GEN)x[1],p1=cgeti(lx1));
	p2=icopy((GEN)x[2]); lx1=lg(x1);
	y=cgetg(l1,t_VEC); f=(x!=x1); i=0;
	while (!gcmp0(p2) && i<=l1-2)
	{
	  i++; y[i]=ldvmdii(p1,p2,&p3);
	  if (signe(p3)>=0) affii(p3,p1);
          else
	  {
	    p4=addii(p3,p2); affii(p4,p1); cgiv(p4);
	    y[1]=laddsi(-1,(GEN)y[1]);
	  }
	  cgiv(p3); p4=p1; p1=p2; p2=p4;
	  if (f)
          {
	    if (i>=lx1) { i--; break; }
            if (!egalii((GEN)y[i],(GEN)x1[i]))
            {
              av=avma;
              if (gcmp1(absi(subii((GEN)x1[i],(GEN)y[i]))))
              {
                if (i>=lx1-1 || !gcmp1((GEN)x1[i+1]))
                  affii((GEN)x1[i],(GEN)y[i]);
              }
              else i--;
              avma=av; break;
            }
          }
	}
	if (i>=2 && gcmp1((GEN)y[i]))
	{
	  cgiv((GEN)y[i]); --i; cgiv((GEN)y[i]);
	  y[i]=laddsi(1,(GEN)y[i]);
	}
	setlg(y,i+1); return gerepileupto(l, y);
    }
    err(typeer,"sfcont");
  }

  switch(tx)
  {
    case t_POL:
      y=cgetg(2,t_VEC); y[1]=lcopy(x); break;
    case t_SER:
      av=avma; p1=gtrunc(x); tetpil=avma;
      y=gerepile(av,tetpil,sfcont(p1,p1,k)); break;
    case t_RFRAC:
    case t_RFRACN:
      av=avma; l1=lgef(x[1]); if (lgef(x[2])>l1) l1=lgef(x[2]);
      if (k>0 && l1>k+1) l1=k+1;
      yp=cgetg(l1,t_VEC); p1=(GEN)x[1]; i=0; p2=(GEN)x[2];
      while (!gcmp0(p2) && i<=l1-2)
      {
	i++; yp[i]=ldivres(p1,p2,&p3);
	p1=p2; p2=p3;
      }
      tetpil=avma; y=cgetg(i+1,t_VEC);
      for (j=1; j<=i; j++) y[j]=lcopy((GEN)yp[j]);
      y=gerepile(av,tetpil,y); break;
    default: err(typeer,"sfcont");
      return NULL; /* not reached */
  }
  return y;
}

static GEN
sfcont2(GEN b, GEN x, long k)
{
  long l1 = lg(b), tx = typ(x), i,tetpil, av = avma;
  GEN y,p1;

  if (k)
  {
    if (k>=l1) err(typeer,"sfcont2");
    l1 = k+1;
  }
  y=cgetg(l1,t_VEC);
  if (l1==1) return y;
  if (is_scalar_t(tx))
  {
    if (!is_intreal_t(tx) && !is_frac_t(tx)) err(typeer,"sfcont2");
  }
  else if (tx == t_SER) x = gtrunc(x);

  if (!gcmp1((GEN)b[1])) x = gmul((GEN)b[1],x);
  i = 2; y[1] = lfloor(x); p1 = gsub(x,(GEN)y[1]);
  for (  ; i<l1 && !gcmp0(p1); i++)
  {
    x = gdiv((GEN)b[i],p1);
    if (tx == t_REAL)
    {
      long e = expo(x);
      if (e>0 && (e>>TWOPOTBITS_IN_LONG)+3 > lg(x)) break;
    }
    y[i] = lfloor(x);
    p1 = gsub(x,(GEN)y[i]);
  }
  setlg(y,i); tetpil=avma;
  return gerepile(av,tetpil,gcopy(y));
}

GEN
pnqn(GEN x)
{
  long av=avma,tetpil,lx,ly,tx=typ(x),i;
  GEN y,p0,p1,q0,q1,a,b,p2,q2;

  if (! is_matvec_t(tx)) err(typeer,"pnqn");
  lx=lg(x); if (lx==1) return idmat(2);
  p0=gun; q0=gzero;
  if (tx != t_MAT)
  {
    p1=(GEN)x[1]; q1=gun;
    for (i=2; i<lx; i++)
    {
      a=(GEN)x[i];
      p2=gadd(gmul(a,p1),p0); p0=p1; p1=p2;
      q2=gadd(gmul(a,q1),q0); q0=q1; q1=q2;
    }
  }
  else
  {
    ly=lg(x[1]);
    if (ly==2)
    {
      p1=cgetg(lx,t_VEC); for (i=1; i<lx; i++) p1[i]=mael(x,i,1);
      tetpil=avma; return gerepile(av,tetpil,pnqn(p1));
    }
    if (ly!=3) err(talker,"incorrect size in pnqn");
    p1=gcoeff(x,2,1); q1=gcoeff(x,1,1);
    for (i=2; i<lx; i++)
    {
      a=gcoeff(x,2,i); b=gcoeff(x,1,i);
      p2=gadd(gmul(a,p1),gmul(b,p0)); p0=p1; p1=p2;
      q2=gadd(gmul(a,q1),gmul(b,q0)); q0=q1; q1=q2;
    }
  }
  tetpil=avma; y=cgetg(3,t_MAT);
  p2=cgetg(3,t_COL); y[1]=(long)p2; p2[1]=lcopy(p1); p2[2]=lcopy(q1);
  p2=cgetg(3,t_COL); y[2]=(long)p2; p2[1]=lcopy(p0); p2[2]=lcopy(q0);
  return gerepile(av,tetpil,y);
}

GEN
bestappr(GEN x, GEN k)
{
  long av=avma,tetpil,tx,tk=typ(k),lx,i,e;
  GEN p0,p1,p,q0,q1,q,a,y;

  if (tk != t_INT)
  {
    if (tk != t_REAL && !is_frac_t(tk))
      err(talker,"incorrect bound type in bestappr");
    k = gcvtoi(k,&e);
  }
  if (cmpis(k,1) < 0) k=gun;
  tx=typ(x); if (tx == t_FRACN) x = gred(x);
  switch(tx)
  {
    case t_INT:
      if (av==avma) return icopy(x);
      tetpil=avma; return gerepile(av,tetpil,icopy(x));

    case t_FRAC:
      if (cmpii((GEN)x[2],k) <= 0)
      {
        if (av==avma) return gcopy(x);
        tetpil=avma; return gerepile(av,tetpil,gcopy(x));
      }

    case t_REAL:
      p1=gun; p0=gfloor(x); q1=gzero; q0=gun; a=p0;
      while (gcmp(q0,k)<=0)
      {
	x = gsub(x,a);
	if (gcmp0(x)) { p1=p0; q1=q0; break; }

	x = ginv(x); a = (gcmp(x,k)<0)? gfloor(x): k;
	p = addii(mulii(a,p0),p1); p1=p0; p0=p;
        q = addii(mulii(a,q0),q1); q1=q0; q0=q;
      }
      tetpil=avma; return gerepile(av,tetpil,gdiv(p1,q1));

   case t_COMPLEX: case t_POL: case t_SER: case t_RFRAC:
   case t_RFRACN: case t_VEC: case t_COL: case t_MAT:
      lx = (tx==t_POL)? lgef(x): lg(x); y=cgetg(lx,tx);
      for (i=1; i<lontyp[tx]; i++) y[i]=x[i];
      for (   ; i<lx; i++) y[i]=(long)bestappr((GEN)x[i],k);
      return y;
  }
  err(typeer,"bestappr");
  return NULL; /* not reached */
}

/***********************************************************************/
/**                                                                   **/
/**         FUNDAMENTAL UNIT AND REGULATOR (QUADRATIC FIELDS)         **/
/**                                                                   **/
/***********************************************************************/

GEN
gfundunit(GEN x)
{
  return garith_proto(fundunit,x,1);
}

static GEN
get_quad(GEN f, GEN pol, long r)
{
  GEN y, c=(GEN)f[2], p1=(GEN)c[1], q1=(GEN)c[2];
  y=cgetg(4,t_QUAD); y[1]=(long)pol;
  y[2]=r? lsubii(p1,q1): (long)p1;
  y[3]=(long)q1; return y;
}

/* replace f by f * [a,1; 1,0] */
static void
update_f(GEN f, GEN a)
{
  GEN p1;
  p1=gcoeff(f,1,1);
  coeff(f,1,1)=laddii(mulii(a,p1), gcoeff(f,1,2));
  coeff(f,1,2)=(long)p1;

  p1=gcoeff(f,2,1);
  coeff(f,2,1)=laddii(mulii(a,p1), gcoeff(f,2,2));
  coeff(f,2,2)=(long)p1;
}

GEN
fundunit(GEN x)
{
  long av = avma, av2,tetpil,lim,r,flp,flq;
  GEN pol,y,a,u,v,u1,v1,sqd,f;

  if (typ(x) != t_INT) err(arither1);
  if (signe(x)<=0) err(arither2);
  r=mod4(x); if (r==2 || r==3) err(funder2,"fundunit");

  sqd=racine(x); av2=avma; lim=stack_lim(av2,2);
  a = shifti(addsi(r,sqd),-1);
  f=cgetg(3,t_MAT); f[1]=lgetg(3,t_COL); f[2]=lgetg(3,t_COL);
  coeff(f,1,1)=(long)a; coeff(f,1,2)=un;
  coeff(f,2,1)=un;      coeff(f,2,2)=zero;
  v = gdeux; u = stoi(r);
  for(;;)
  {
    u1=subii(mulii(a,v),u);       flp=egalii(u,u1); u=u1;
    v1=divii(subii(x,sqri(u)),v); flq=egalii(v,v1); v=v1;
    if (flq) break; a = divii(addii(sqd,u),v);
    if (flp) break; update_f(f,a);
    if (low_stack(lim, stack_lim(av2,2)))
    {
      GEN *gptr[4]; gptr[0]=&a; gptr[1]=&f; gptr[2]=&u; gptr[3]=&v;
      if(DEBUGMEM>1) err(warnmem,"fundunit");
      gerepilemany(av2,gptr,4);
    }
  }
  pol = quadpoly(x); y = get_quad(f,pol,r);
  if (!flq) v1 = y; else { update_f(f,a); v1 = get_quad(f,pol,r); }

  u1=gconj(y); tetpil=avma; y=gdiv(v1,u1);
  if (signe(y[3]) < 0) { tetpil=avma; y=gneg(y); }
  return gerepile(av,tetpil,y);
}

GEN
gregula(GEN x, long prec)
{
  return garith_proto2gs(regula,x,prec);
}

GEN
regula(GEN x, long prec)
{
  long av = avma,av2,lim,r,fl,rexp;
  GEN reg,rsqd,y,u,v,u1,v1, sqd = racine(x);

  if (signe(x)<=0) err(arither2);
  r=mod4(x); if (r==2 || r==3) err(funder2,"regula");

  rsqd = gsqrt(x,prec);
  if (egalii(sqri(sqd),x)) err(talker,"square argument in regula");

  rexp=0; reg=cgetr(prec); affsr(2,reg);
  av2=avma; lim = stack_lim(av2,2);
  u = stoi(r); v = gdeux;
  for(;;)
  {
    u1 = subii(mulii(divii(addii(u,sqd),v), v), u);
    v1 = divii(subii(x,sqri(u1)),v); fl = egalii(v,v1);
    if (fl || egalii(u,u1)) break;
    reg = mulrr(reg, divri(addir(u1,rsqd),v));
    rexp += expo(reg); setexpo(reg,0);
    u = u1; v = v1;
    if (rexp & ~EXPOBITS) err(muler4);
    if (low_stack(lim, stack_lim(av2,2)))
    {
      GEN *gptr[3]; gptr[0]=&reg; gptr[1]=&u; gptr[2]=&v;
      if(DEBUGMEM>1) err(warnmem,"regula");
      gerepilemany(av2,gptr,3);
    }
  }
  reg = gsqr(reg); setexpo(reg,expo(reg)-1);
  if (fl) reg = mulrr(reg, divri(addir(u1,rsqd),v));
  y = mplog(divri(reg,v));
  if (rexp)
  {
    u1 = mulsr(rexp, glog(gdeux, prec));
    setexpo(u1, expo(u1)+1);
    y = addrr(y,u1);
  }
  return gerepileupto(av, y);
}

/*************************************************************************/
/**                                                                     **/
/**                            CLASS NUMBER                             **/
/**                                                                     **/
/*************************************************************************/

static GEN
gclassno(GEN x)
{
  return garith_proto(classno,x,1);
}

static GEN
gclassno2(GEN x)
{
  return garith_proto(classno2,x,1);
}

GEN
qfbclassno0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return gclassno(x);
    case 1: return gclassno2(x);
    default: err(flagerr,"qfbclassno");
  }
  return NULL; /* not reached */
}

/* f^h = 1, return order(f) */
static GEN
find_order(GEN f, GEN h)
{
  GEN fh, p,e;
  long i,j,lim;

  p = decomp(h);
  e =(GEN)p[2];
  p =(GEN)p[1];
  for (i=1; i<lg(p); i++)
  {
    lim = itos((GEN)e[i]);
    for (j=1; j<=lim; j++)
    {
      GEN p1 = divii(h,(GEN)p[i]);
      fh = powgi(f,p1);
      if (!is_pm1(fh[1])) break;
      h = p1;
    }
  }
  return h;
}

static GEN
end_classno(GEN h, GEN hin, GEN forms, long lform)
{
  long i,com;
  GEN a,b,p1,q,fh,fg, f = (GEN)forms[0];

  h = find_order(f,h); /* H = <f> */
  q = ground(gdiv(hin,h)); /* approximate order of G/H */
  for (i=1; i < lform; i++)
  {
    long av = avma; 
    fg = powgi((GEN)forms[i], h);
    fh = powgi(fg, q);
    a = (GEN)fh[1];
    if (is_pm1(a)) continue;
    b = (GEN)fh[2]; p1 = fg;
    for (com=1; ; com++)
    {
      if (egalii((GEN)p1[1], a) && absi_equal((GEN)p1[2], b)) break;
      p1 = gmul(p1,fg);
    }
    if (signe(p1[2]) == signe(b)) com = -com;
    /* f_i ^ h(q+com) = 1 */
    avma = av; q = addsi(com,q);
  }
  return mulii(q,h);
}

static GEN
to_form(GEN x, long f)
{
  return redimag(primeform(x, stoi(f), 0));
}

static long
two_rank(GEN x)
{
  GEN p = (GEN)decomp(absi(x))[1];
  long l = lg(p)-1;
#if 0 /* positive disc not needed */
  if (signe(x) > 0)
  {
    long i;
    for (i=1; i<=l; i++)
      if (mod4((GEN)p[i]) == 3) { l--; break; }
  }
#endif
  return l-1;
}

#define MAXFORM 11
#define _low(x) (__x=(GEN)x, __x[lgefint(__x)-1])

/* h(x) for x<0 using Baby Step/Giant Step.
 * Assumes G is not too far from being cyclic.
 * 
 * Compute G^2 instead of G so as to kill most of the non-cyclicity */
GEN
classno(GEN x)
{
  long av = avma, av2,c,lforms,k,l,i,j,j1,j2,lim,com,s, forms[MAXFORM];
  long r2;
  GEN a,b,count,index,tabla,tablb,hash,p1,p2,hin,h,f,fh,fg,ftest;
  GEN __x;
  byteptr p = diffptr;

  if (typ(x) != t_INT) err(arither1);
  s=signe(x); if (s>=0) return classno2(x);

  k=mod4(x); if (k==1 || k==2) err(funder2,"classno");
  if (gcmpgs(x,-12) >= 0) return gun;

  p2 = gsqrt(absi(x),DEFAULTPREC);
  p1 = divrr(p2,mppi(DEFAULTPREC));
  p2 = gtrunc(shiftr(gsqrt(p2,DEFAULTPREC),1));
  s = 1000;
  if (signe(p2))
  {
    if (is_bigint(p2)) err(talker,"discriminant too big in classno");
    s = itos(p2); if (s < 1000) s = 1000;
  }
  r2 = two_rank(x);
  c=lforms=0;
  while (c <= s && *p)
  {
    c += *p++; k = krogs(x,c);
    if (!k) continue;

    av2 = avma;
    if (k > 0)
    {
      divrsz(mulsr(c,p1),c-1, p1);
      if (lforms < MAXFORM && c > 2) forms[lforms++] = c; 
    }
    else divrsz(mulsr(c,p1),c+1, p1);
    avma = av2; 
  }
  h = hin = shifti(ground(p1), -r2);
  s = 2*itos(gceil(gpui(p1,ginv(stoi(4)),DEFAULTPREC)));
  if (s>=10000) s=10000;

  count = new_chunk(256); for (i=0; i<=255; i++) count[i]=0;
  index = new_chunk(257);
  tabla = new_chunk(10000);
  tablb = new_chunk(10000);
  hash  = new_chunk(10000);
  f = gsqr(to_form(x, forms[0]));
  p1 = fh = powgi(f, h);
  for (i=0; i<s; i++)
  {
    tabla[i] = _low(p1[1]);
    tablb[i] = _low(p1[2]);
    count[tabla[i]&255]++; p1=compimag(p1,f);
  }
  index[0]=0; for (i=0; i<=254; i++) index[i+1] = index[i]+count[i];
  for (i=0; i<s; i++) hash[index[tabla[i]&255]++]=i;
  index[0]=0; for (i=0; i<=255; i++) index[i+1] = index[i]+count[i];

  fg=gpuigs(f,s); av2=avma; lim=stack_lim(av2,2);
  ftest=gpuigs(p1,0);
  for (com=0; ; com++)
  {
    a = (GEN)ftest[1]; k = _low(a);
    b = (GEN)ftest[2]; l = _low(b); j = k&255;
    for (j1=index[j]; j1 < index[j+1]; j1++)
    {
      j2 = hash[j1];
      if (tabla[j2] == k && tablb[j2] == l)
      {
        p1 = gmul(gpuigs(f,j2),fh);
        if (egalii((GEN)p1[1], a) && absi_equal((GEN)p1[2], b))
        { /* p1 = ftest or ftest^(-1), we are done */
          if (signe(p1[2]) == signe(b)) com = -com;
          h = addii(addis(h,j2), mulss(s,com));
          forms[0] = (long)f;
          for (i=1; i<lforms; i++)
            forms[i] = (long)gsqr(to_form(x, forms[i]));
          h = end_classno(h,hin,forms,lforms);
          return gerepileuptoint(av, shifti(h, r2));
        }
      }
    }
    ftest = gmul(ftest,fg);
    if (is_pm1(ftest[1])) err(impl,"classno with too small order");
    if (low_stack(lim, stack_lim(av2,2))) ftest = gerepileupto(av2,ftest);
  }
}

/* use Euler products */
GEN
classno2(GEN x)
{
  long av=avma,tetpil,n,i,k,s=signe(x),fl2;
  GEN p1,p2,p3,p4,p5,p7,p8,pi4,reg,logd,d,fd;

  if (typ(x) != t_INT) err(arither1);
  if (!s) err(arither2);
  if (s<0 && gcmpgs(x,-12) >= 0) return gun;

  p1=auxdecomp(absi(x),1); p2=(GEN)p1[2]; p1=(GEN)p1[1];
  n=lg(p1); d=gun;
  for (i=1; i<n; i++)
    if (mod2((GEN)p2[i])) d=mulii(d,(GEN)p1[i]);
  fl2 = (mod4(x)==0); /* 4 | x */
  if (mod4(d) != 2-s)
  {
    if (!fl2) err(funder2,"classno2");
    d = shifti(d,2);
  }
  else fl2=0;
  p8=gun; fd = (s<0)? negi(d): d; /* d = abs(fd) */
  for (i=1; i<n; i++)
  {
    k=itos((GEN)p2[i]); p4=(GEN)p1[i];
    if (fl2 && i==1) k -= 2; /* p4 = 2 */
    if (k>=2)
    {
      p8=mulii(p8,subis(p4,kronecker(fd,p4)));
      if (k>=4) p8=mulii(p8,gpuigs(p4,(k>>1)-1));
    }
  }
  if (s<0 && lgefint(d)==3)
  {
    switch(d[2])
    {
      case 4: p8=gdivgs(p8,2); break;
      case 3: p8=gdivgs(p8,3); break;
    }
    if (d[2] < 12) /* |fd| < 12*/
      { tetpil=avma; return gerepile(av,tetpil,icopy(p8)); }
  }

  pi4 = mppi(DEFAULTPREC); logd = glog(d,DEFAULTPREC);
  p1 = gsqrt(gdiv(gmul(d,logd),gmul2n(pi4,1)),DEFAULTPREC);
  p4 = divri(pi4,d); p7 = ginv(mpsqrt(pi4));
  if (s > 0)
  {
    reg = regula(d,DEFAULTPREC);
    p2 = gsubsg(1, gmul2n(gdiv(glog(reg,DEFAULTPREC),logd),1));
    p3 = gsqrt(gdivsg(2,logd),DEFAULTPREC);
    if (gcmp(p2,p3)>=0) p1 = gmul(p2,p1);
  }
  else reg = NULL; /* for gcc -Wall */
  p1 = gtrunc(p1); n=p1[2];
  if (lgefint(p1)!=3 || n<0)
    err(talker,"discriminant too large in classno");

  p1 = gsqrt(d,DEFAULTPREC); p3 = gzero;
  if (s > 0)
  {
    for (i=1; i<=n; i++)
    {
      k=krogs(fd,i);
      if (k)
      {
	p2 = mulir(mulss(i,i),p4);
	p5 = subsr(1,mulrr(p7,incgam3(ghalf,p2,DEFAULTPREC)));
	p5 = addrr(divrs(mulrr(p1,p5),i),eint1(p2,DEFAULTPREC));
	p3 = (k>0)? addrr(p3,p5): subrr(p3,p5);
      }
    }
    p3 = shiftr(divrr(p3,reg),-1);
    if (!egalii(x,fd)) /* x != p3 */
      p8 = gdiv(p8,ground(gdiv(regula(x,DEFAULTPREC),reg)));
  }
  else
  {
    p1 = gdiv(p1,pi4);
    for (i=1; i<=n; i++)
    {
      k=krogs(fd,i);
      if (k)
      {
	p2=mulir(mulss(i,i),p4);
	p5=subsr(1,mulrr(p7,incgam3(ghalf,p2,DEFAULTPREC)));
	p5=addrr(p5,divrr(divrs(p1,i),mpexp(p2)));
	p3 = (k>0)? addrr(p3,p5): subrr(p3,p5);
      }
    }
  }
  p3=ground(p3); tetpil=avma;
  return gerepile(av,tetpil,mulii(p8,p3));
}

GEN
hclassno(GEN x)
{
  long d,a,b,h,b2,f;

  d= -itos(x); if (d>0 || (d & 3) > 1) return gzero;
  if (!d) return gdivgs(gun,-12);
  if (-d > (VERYBIGINT>>1))
    err(talker,"discriminant too big in hclassno. Use quadclassunit");
  h=0; b=d&1; b2=(b-d)>>2; f=0;
  if (!b)
  {
    for (a=1; a*a<b2; a++)
      if (b2%a == 0) h++;
    f = (a*a==b2); b=2; b2=(4-d)>>2;
  }
  while (b2*3+d<0)
  {
    if (b2%b == 0) h++;
    for (a=b+1; a*a<b2; a++)
      if (b2%a == 0) h+=2;
    if (a*a==b2) h++;
    b+=2; b2=(b*b-d)>>2;
  }
  if (b2*3+d==0)
  {
    GEN y = cgetg(3,t_FRAC);
    y[1]=lstoi(3*h+1); y[2]=lstoi(3); return y;
  }
  if (f) return gaddsg(h,ghalf);
  return stoi(h);
}
