/********************************************************************/
/**                                                                **/
/**                      GENERIC OPERATIONS                        **/
/**                         (first part)                           **/
/**                                                                **/
/********************************************************************/
/* $Id$ */
#include "pari.h"

#define swapspec(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}
GEN quickmul(GEN a, GEN b, long na, long nb);

#define cpifstack(x) isonstack(x)?gcopy(x):x
/* y is a polmod, f is gadd or gmul */
static GEN
op_polmod(GEN f(GEN,GEN), GEN x, GEN y, long tx)
{
  GEN mod,k,l, z=cgetg(3,t_POLMOD);
  long av,tetpil;

  l=(GEN)y[1];
  if (tx==t_POLMOD)
  {
    k=(GEN)x[1];
    if (gegal(k,l))
      { mod=cpifstack(k); x=(GEN)x[2]; y=(GEN)y[2]; }
    else
    {
      long vx=varn(k), vy=varn(l);
      if (vx==vy) { mod=srgcd(k,l); x=(GEN)x[2]; y=(GEN)y[2]; }
      else
        if (vx<vy) { mod=cpifstack(k); x=(GEN)x[2]; }
        else       { mod=cpifstack(l); y=(GEN)y[2]; }
    }
  }
  else
  {
    mod=cpifstack(l); y=(GEN)y[2];
    if (is_scalar_t(tx))
    {
      z[2] = (long)f(x,y);
      z[1] = (long)mod; return z;
    }
  }
  av=avma; x = f(x,y); tetpil=avma;
  z[2] = lpile(av,tetpil,gmod(x,mod));
  z[1] = (long)mod; return z;
}
#undef cpifstack

/********************************************************************/
/**                                                                **/
/**                          SUBTRACTION                           **/
/**                                                                **/
/********************************************************************/

GEN
gsub(GEN x, GEN y)
{
  long tetpil, av = avma;
  y=gneg_i(y); tetpil=avma;
  return gerepile(av,tetpil,gadd(x,y));
}

/********************************************************************/
/**                                                                **/
/**                           ADDITION                             **/
/**                                                                **/
/********************************************************************/

static GEN
addpadic(GEN x, GEN y)
{
  long c,e,r,d,r1,r2,av,tetpil;
  GEN z,p1,p2, p = (GEN)x[2];

  z=cgetg(5,t_PADIC); icopyifstack(p, z[2]); av=avma;
  e=valp(x); r=valp(y); d = r-e;
  if (d<0) { p1=x; x=y; y=p1; e=r; d = -d; }
  r1=precp(x); r2=precp(y);
  if (d)
  {
    r = d+r2;
    p1 = (d==1)? p: gclone(gpuigs(p,d));
    avma=av;
    if (r<r1) z[3]=lmulii(p1,(GEN)y[3]);
    else
    {
      r=r1; z[3]=licopy((GEN)x[3]);
    }
    av=avma; p2=mulii(p1,(GEN)y[4]);
    if (d!=1) gunclone(p1);
    p1=addii(p2,(GEN)x[4]); tetpil=avma;
    z[4]=lpile(av,tetpil, modii(p1,(GEN)z[3]));
    z[1]=evalprecp(r) | evalvalp(e); return z;
  }
  if (r2<r1) { r=r2; p1=x; x=y; y=p1; } else r=r1;
  p1 = addii((GEN)x[4],(GEN)y[4]);
  if (!signe(p1) || (c = pvaluation(p1,p,&p2)) >=r)
  {
    avma=av; z[4]=zero; z[3]=un;
    z[1]=evalvalp(e+r); return z;
  }
  if (c)
  {
    p2=gclone(p2); avma=av;
    if (c==1)
      z[3] = ldivii((GEN)x[3], p);
    else
    {
      p1 = gpuigs(p,c); tetpil=avma;
      z[3] = lpile(av,tetpil, divii((GEN)x[3], p1));
    }
    z[4]=lmodii(p2,(GEN)z[3]); gunclone(p2);
    z[1]=evalprecp(r-c) | evalvalp(e+c); return z;
  }
  tetpil=avma;
  z[4]=lpile(av,tetpil,modii(p1,(GEN)x[3]));
  z[3]=licopy((GEN)x[3]);
  z[1]=evalprecp(r) | evalvalp(e); return z;
}

/* return x + y, where x is t_INT or t_FRAC(N), y t_PADIC */
static GEN
gaddpex(GEN x, GEN y)
{
  long tx,e1,e2,e3,av,tetpil;
  GEN z,p,p1,p2;

  if (gcmp0(x)) return gcopy(y);

  av=avma; p=(GEN)y[2]; tx=typ(x);
  z=cgetg(5,t_PADIC); z[2]=(long)p;
  e3 = (tx == t_INT)? pvaluation(x,p,&p1)
                    : pvaluation((GEN)x[1],p,&p1) -
                      pvaluation((GEN)x[2],p,&p2);
  e1 = valp(y)-e3; e2 = signe(y[4])? e1+precp(y): e1;
  if (e2<=0)
  {
    z[1] = evalprecp(0) | evalvalp(e3);
    z[3] = un;
    z[4] = zero;
  }
  else
  {
    if (tx != t_INT && !is_pm1(p2)) p1 = gdiv(p1,p2);
    z[1] = evalprecp(e2) | evalvalp(e3);
    z[3] = e1? lmul((GEN)y[3], gpuigs(p,e1)): y[3];
    z[4] = lmod(p1,(GEN)z[3]);
  }
  tetpil=avma; return gerepile(av,tetpil,addpadic(z,y));
}

static long
kro_quad(GEN x, GEN y)
{
  long k, av=avma;

  x = subii(sqri((GEN)x[3]), shifti((GEN)x[2],2));
  k = kronecker(x,y); avma=av; return k;
}

static GEN
addfrac(GEN x, GEN y)
{
  GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
  GEN y1 = (GEN)y[1], y2 = (GEN)y[2], p1,p2,n,d,delta,z;

  z = cgetg(3,t_FRAC);
  (void)new_chunk((lgefint(x1) + lgefint(x2) +
                   lgefint(y1) + lgefint(y2)) << 1);
  delta = mppgcd(x2,y2);
  if (is_pm1(delta))
  {
    p1 = mulii(x1,y2);
    p2 = mulii(y1,x2); avma = (long)z;
    z[1] = laddii(p1,p2);
    z[2] = lmulii(x2,y2); return z;
  }
  x2 = divii(x2,delta);
  y2 = divii(y2,delta);
  n = addii(mulii(x1,y2), mulii(y1,x2));
  if (!signe(n)) { avma = (long)(z+3); return gzero; }
  d = mulii(x2, y2);
  p1 = dvmdii(n, delta, &p2);
  if (p2 == gzero)
  {
    if (is_pm1(d)) { avma = (long)(z+3); return icopy(p1); }
    avma = (long)z;
    z[1] = licopy(p1);
    z[2] = licopy(d); return z;
  }
  p1 = mppgcd(delta, p2);
  if (is_pm1(p1))
  {
    avma = (long)z;
    z[1] = licopy(n);
  }
  else
  {
    delta = divii(delta, p1);
    avma = (long)z;
    z[1] = ldivii(n,p1);
  }
  z[2] = lmulii(d,delta); return z;
}

static GEN
addrfrac(GEN x, GEN y)
{
  GEN z = cgetg(3,t_RFRAC);
  GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
  GEN y1 = (GEN)y[1], y2 = (GEN)y[2], p1,p2,n,d,delta;
  long tetpil;

  delta = ggcd(x2,y2);
  if (gcmp1(delta))
  {
    p1 = gmul(x1,y2);
    p2 = gmul(y1,x2);
    tetpil = avma; /* numerator is non-zero */
    z[1] = lpile((long)z,tetpil, gadd(p1,p2));
    z[2] = lmul(x2, y2); return z;
  }
  x2 = gdeuc(x2,delta);
  y2 = gdeuc(y2,delta);
  n = gadd(gmul(x1,y2), gmul(y1,x2));
  if (!signe(n)) return gerepileupto((long)(z+3), n);
  tetpil = avma; d = gmul(x2, y2);
  p1 = poldivres(n, delta, &p2);
  if (!signe(p2))
  {
    if (gcmp1(d)) return gerepileupto((long)(z+3), p1);
    z[1]=(long)p1; z[2]=(long)d;
    gerepilemanyvec((long)z,tetpil,z+1,2); return z;
  }
  p1 = ggcd(delta, p2);
  if (gcmp1(p1))
  {
    tetpil = avma;
    z[1] = lcopy(n);
  }
  else
  {
    delta = gdeuc(delta, p1);
    tetpil = avma;
    z[1] = ldeuc(n,p1);
  }
  z[2] = lmul(d,delta);
  gerepilemanyvec((long)z,tetpil,z+1,2); return z;
}

static GEN
addscalrfrac(GEN x, GEN y)
{
  GEN p1,num, z = cgetg(3,t_RFRAC);
  long tetpil, av;

  p1 = gmul(x,(GEN)y[2]); tetpil = avma;
  num = gadd(p1,(GEN)y[1]);
  av = avma;
  p1 = content((GEN)y[2]);
  if (!gcmp1(p1))
  {
    p1 = ggcd(p1, content(num));
    if (!gcmp1(p1))
    {
      tetpil = avma;
      z[1] = ldiv(num, p1);
      z[2] = ldiv((GEN)y[2], p1);
      gerepilemanyvec((long)z,tetpil,z+1,2); return z;
    }
  }
  avma = av;
  z[1]=lpile((long)z,tetpil, num);
  z[2]=lcopy((GEN)y[2]); return z;
}

/* assume gvar(x) = varn(mod) */
static GEN
to_polmod(GEN x, GEN mod)
{
  long tx = typ(x);
  GEN z = cgetg(3, t_POLMOD);

  if (tx == t_RFRACN) { x = gred_rfrac(x); tx = t_RFRAC; }
  if (tx == t_RFRAC) x = gmul((GEN)x[1], ginvmod((GEN)x[2],mod));
  z[1] = (long)mod;
  z[2] = (long)x;
  return z;
}

GEN
gadd(GEN x, GEN y)
{
  long vx,vy,lx,ly,tx,ty,i,j,k,l,av,tetpil;
  GEN z,p1,p2;

  tx=typ(x); ty=typ(y);
  if (is_const_t(tx) && is_const_t(ty))
  {
    if (tx>ty) { p1=x; x=y; y=p1; i=tx; tx=ty; ty=i; }
  }
  else
  {
    vx=gvar(x); vy=gvar(y);
    if (vx<vy || (vx==vy && tx>ty))
    {
      p1=x; x=y; y=p1;
      i=tx; tx=ty; ty=i;
      i=vx; vx=vy; vy=i;
    }
    if (ty==t_POLMOD) return op_polmod(gadd,x,y,tx);
  }

  /* here vx >= vy */
  if (is_scalar_t(ty))
  {
    switch(tx)
    {
      case t_INT:
        switch(ty)
	{
	  case t_INT:  return addii(x,y);
          case t_REAL: return addir(x,y);
	
	  case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)y[1];
	    (void)new_chunk(lgefint(p2)+1);
            p1 = addii(modii(x,p2),(GEN)y[2]); avma = (long)z;
            z[2] = (cmpii(p1,p2) >=0)? lsubii(p1,p2): licopy(p1);
	    icopyifstack(p2,z[1]); return z;

	  case t_FRAC: case t_FRACN: z=cgetg(3,ty);
            (void)new_chunk(lgefint(x) + lgefint(y[1]) + lgefint(y[2]) + 1);
            p1 = mulii((GEN)y[2],x); avma = (long)z;
	    z[1] = laddii((GEN)y[1], p1);
	    z[2] = licopy((GEN)y[2]); return z;

	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=ladd(x,(GEN)y[1]);
	    z[2]=lcopy((GEN)y[2]); return z;
	
	  case t_PADIC:
	    return gaddpex(x,y);
	
	  case t_QUAD: z=cgetg(4,t_QUAD);
	    copyifstack(y[1], z[1]);
	    z[2]=ladd(x,(GEN)y[2]);
	    z[3]=lcopy((GEN)y[3]); return z;
	}
	
      case t_REAL:
        switch(ty)
	{
	  case t_REAL: return addrr(x,y);
	
	  case t_FRAC: case t_FRACN:
	    if (!signe(y[1])) return rcopy(x);
            if (!signe(x))
            {
              lx = expi((GEN)y[1]) - expi((GEN)y[2]) - expo(x);
              if (lx < 0) return rcopy(x);
              lx >>= TWOPOTBITS_IN_LONG;
              z=cgetr(lx+3); diviiz((GEN)y[1],(GEN)y[2],z);
              return z;
            }
            av=avma; z=addir((GEN)y[1],mulir((GEN)y[2],x)); tetpil=avma;
            return gerepile(av,tetpil,divri(z,(GEN)y[2]));
	
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=ladd(x,(GEN)y[1]);
	    z[2]=lcopy((GEN)y[2]); return z;

	  case t_QUAD:
	    if (gcmp0(y)) return rcopy(x);

	    av=avma; i=gexpo(y)-expo(x);
	    if (i<=0) i=0; else i >>= TWOPOTBITS_IN_LONG;
	    p1=co8(y,lg(x)+i); tetpil=avma;
	    return gerepile(av,tetpil,gadd(p1,x));
	
	  case t_INTMOD: case t_PADIC: err(operf,"+",tx,ty);
	}
	
      case t_INTMOD:
        switch(ty)
	{
	  case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)x[1]; p1=(GEN)y[1];
	    if (p1==p2 || egalii(p1,p2))
            {
              icopyifstack(p2,z[1]);
              if (!is_bigint(p2))
              {
                z[2] = lstoi(addssmod(itos((GEN)x[2]),itos((GEN)y[2]), p2[2]));
                return z;
              }
            }
            else
            { p2 = mppgcd(p1,p2); z[1] = (long)p2; }
	    av=avma; (void)new_chunk((lgefint(p1)<<1) + lgefint(x[1]));
            p1=addii((GEN)x[2],(GEN)y[2]); avma=av;
	    z[2]=lmodii(p1,p2); return z;
	
	  case t_FRAC: case t_FRACN: z=cgetg(3,t_INTMOD); p2=(GEN)x[1];
	    (void)new_chunk(lgefint(p2)<<2);
            p1 = mulii((GEN)y[1], mpinvmod((GEN)y[2],p2));
            p1 = addii(modii(p1,p2), (GEN)x[2]); avma=(long)z;
            z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;
	
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=ladd(x,(GEN)y[1]);
            z[2]=lcopy((GEN)y[2]); return z;
	
	  case t_PADIC:
	    l=avma; p1=cgetg(3,t_INTMOD);
	    p1[1]=x[1]; p1[2]=lgeti(lgefint(x[1]));
	    gaffect(y,p1); tetpil=avma;
	    return gerepile(l,tetpil,gadd(p1,x));
	
	  case t_QUAD: z=cgetg(4,t_QUAD);
            copyifstack(y[1], z[1]);
	    z[2]=ladd(x,(GEN)y[2]);
            z[3]=lcopy((GEN)y[3]); return z;
	}
	
      case t_FRAC: case t_FRACN:
        switch (ty)
	{
	  case t_FRAC: return addfrac(x,y);
	  case t_FRACN: z=cgetg(3,t_FRACN); l=avma;
	    p1=mulii((GEN)x[1],(GEN)y[2]);
	    p2=mulii((GEN)x[2],(GEN)y[1]);
	    tetpil=avma; z[1]=lpile(l,tetpil,addii(p1,p2));
	    z[2]=lmulii((GEN)x[2],(GEN)y[2]);
	    return z;

	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=ladd((GEN)y[1],x);
	    z[2]=lcopy((GEN)y[2]); return z;

	  case t_PADIC:
	    return gaddpex(x,y);

	  case t_QUAD: z=cgetg(4,t_QUAD);
	    z[1]=lcopy((GEN)y[1]);
	    z[2]=ladd((GEN)y[2],x);
	    z[3]=lcopy((GEN)y[3]); return z;
	}
	
      case t_COMPLEX:
        switch(ty)
	{
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=ladd((GEN)x[1],(GEN)y[1]);
	    z[2]=ladd((GEN)x[2],(GEN)y[2]); return z;

	  case t_PADIC:
	    if (krosg(-1,(GEN)y[2])== -1)
	    {
	      z=cgetg(3,t_COMPLEX);
              z[1]=ladd((GEN)x[1],y);
	      z[2]=lcopy((GEN)x[2]); return z;
	    }
	    av=avma; l = signe(y[4])? precp(y): 1;
	    p1=cvtop(x,(GEN)y[2], l + valp(y)); tetpil=avma;
            return gerepile(av,tetpil,gadd(p1,y));

	  case t_QUAD:
	    lx=precision(x); if (!lx) err(operi,"+",tx,ty);
	    if (gcmp0(y)) return gcopy(x);

	    av=avma; i=gexpo(y)-gexpo(x);
	    if (i<=0) i=0; else i >>= TWOPOTBITS_IN_LONG;
	    p1=co8(y,lx+i); tetpil=avma;
	    return gerepile(av,tetpil,gadd(p1,x));
	}
	
      case t_PADIC:
        switch(ty)
	{
	  case t_PADIC:
            if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"+",tx,ty);
            return addpadic(x,y);

	  case t_QUAD:
	    if (kro_quad((GEN)y[1],(GEN)x[2]) == -1)
	    {
	      z=cgetg(4,t_QUAD);
	      copyifstack(y[1], z[1]);
	      z[2]=ladd((GEN)y[2],x);
	      z[3]=lcopy((GEN)y[3]); return z;
	    }
	    av=avma; l = signe(x[4])? precp(x): 1;
	    p1=cvtop(y,(GEN)x[2],valp(x)+l); tetpil=avma;
	    return gerepile(av,tetpil,gadd(p1,x));
	}

      case t_QUAD: z=cgetg(4,t_QUAD); k=x[1]; l=y[1];
        if (!gegal((GEN)k,(GEN)l)) err(operi,"+",tx,ty);
        copyifstack(l, z[1]);
        z[2]=ladd((GEN)x[2],(GEN)y[2]);
        z[3]=ladd((GEN)x[3],(GEN)y[3]); return z;
    }
    err(bugparier,"gadd");
  }

  /* here !isscalar(y) */
  if ( (vx>vy && (!is_matvec_t(tx) || !is_matvec_t(ty)))
    || (vx==vy && is_scalar_t(tx)) )
  {
    if (tx == t_POLMOD && vx == vy && ty != t_SER)
    {
      av = avma;
      return gerepileupto(av, op_polmod(gadd, x, to_polmod(y,(GEN)x[1]), tx));
    }

    switch(ty)
    {
      case t_POL: ly=lgef(y);
	if (ly==2) return isexactzero(x)? zeropol(vy): scalarpol(x,vy);

	z = cgetg(ly,t_POL); z[1] = y[1];
        z[2] = ladd(x,(GEN)y[2]);
        for (i=3; i<ly; i++) z[i]=lcopy((GEN)y[i]);
	return normalizepol_i(z, ly);

      case t_SER: l=valp(y); ly=lg(y);
        if (l<3-ly) return gcopy(y);
	if (l<0)
	{
	  z=cgetg(ly,t_SER); z[1]=y[1];
	  for (i=2; i<=1-l; i++) z[i]=lcopy((GEN)y[i]);
	  for (i=3-l; i<ly; i++) z[i]=lcopy((GEN)y[i]);
	  z[2-l]=ladd(x,(GEN)y[2-l]); return z;
	}
	if (l>0)
	{
	  if (gcmp0(x)) return gcopy(y);
	  if (gcmp0(y)) ly=2;

          ly += l; z=cgetg(ly,t_SER);
	  z[1]=evalsigne(1) | evalvalp(0) | evalvarn(vy);
	  for (i=3; i<=l+1; i++) z[i]=zero;
	  for (   ; i<ly; i++) z[i]=lcopy((GEN)y[i-l]);
	  z[2]=lcopy(x); return z;
	}
	av=avma; z=cgetg(ly,t_SER);
	p1=signe(y)? gadd(x,(GEN)y[2]): x;
	if (!isexactzero(p1))
        {
          z[1] = evalvalp(0) | evalvarn(vy);
          if (signe(y))
          {
            z[1] |= evalsigne(1); z[2]=(long)p1;
            for (i=3; i<ly; i++) z[i]=lcopy((GEN)y[i]);
          }
          return z;
        }
        avma=av; /* first coeff is 0 */
        i=3; while (i<ly && gcmp0((GEN)y[i])) i++;
        if (i==ly) return zeroser(vy,i-2);

        z=cgetg(ly-i+2,t_SER); z[1]=evalvalp(i-2)|evalvarn(vy)|evalsigne(1);
        for (j=2; j<=ly-i+1; j++) z[j]=lcopy((GEN)y[j+i-2]);
        return z;

      case t_RFRAC: return addscalrfrac(x,y);
      case t_RFRACN: z=cgetg(3,t_RFRACN);
        av=avma; p1=gmul(x,(GEN)y[2]); tetpil=avma;
        z[1]=lpile(av,tetpil, gadd(p1,(GEN)y[1]));
        z[2]=lcopy((GEN)y[2]); return z;

      case t_VEC: case t_COL: case t_MAT:
	if (isexactzero(x)) return gcopy(y);
	if (ty == t_MAT) return gaddmat(x,y);
        /* fall through */
      case t_QFR: case t_QFI: err(operf,"+",tx,ty);
    }
    err(operf,"+",tx,ty);
  }

  /* here !isscalar(x) && isscalar(y) && (vx=vy || ismatvec(x and y)) */
  if (tx>ty) { p1=x; x=y; y=p1; i=tx; tx=ty; ty=i; }
  switch(tx)
  {
    case t_POL:
      switch (ty)
      {
	case t_POL:
          lx = lgef(x); ly = lgef(y); if (lx < ly) swapspec(x,y, lx,ly);
          z = cgetg(lx,t_POL); z[1] = x[1];
          for (i=2; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
          for (   ; i<lx; i++) z[i]=lcopy((GEN)x[i]);
          (void)normalizepol_i(z, lx);
          if (lgef(z) == 2) { avma = (long)(z + lx); z = zeropol(vx); }
          return z;

	case t_SER:
	  if (gcmp0(x)) return gcopy(y);
          ly = signe(y)? lg(y): 3;
	  i = ly+valp(y)-gval(x,vx);
	  if (i<3) return gcopy(y);

	  p1=greffe(x,i,0); y=gadd(p1,y);
          free(p1); return y;
	
        case t_RFRAC: return addscalrfrac(x,y);
        case t_RFRACN: z=cgetg(3,t_RFRACN);
          av=avma; p1=gmul(x,(GEN)y[2]); tetpil=avma;
          z[1]=lpile(av,tetpil, gadd(p1,(GEN)y[1]));
          z[2]=lcopy((GEN)y[2]); return z;

	default: err(operf,"+",tx,ty);
      }

    case t_SER:
      switch(ty)
      {
	case t_SER:
	  l=valp(y)-valp(x);
	  if (l<0) { l= -l; p1=x; x=y; y=p1; }
	  if (gcmp0(x)) return gcopy(x);
          lx = lg(x);
          ly = signe(y)? lg(y): 2;
	  ly += l; if (lx<ly) ly=lx;
	  av = avma;
          z=cgetg(ly,t_SER);
	  if (l)
	  {
	    if (l>=ly-2)
	      for (i=2; i<ly; i++) z[i]=lcopy((GEN)x[i]);
            else
	    {
	      for (i=2; i<=l+1; i++) z[i]=lcopy((GEN)x[i]);
	      for (   ; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i-l]);
	    }
	    z[1]=x[1]; return z;
	  }
          if (ly>2)
          {
            tetpil = avma;
            for (i=2; i<ly; i++)
            {
              p1 = gadd((GEN)x[i],(GEN)y[i]);
              if (!isexactzero(p1))
              {
                l = i-2; stackdummy(z,l); z += l;
                z[0]=evaltyp(t_SER) | evallg(ly-l);
                z[1]=evalvalp(valp(x)+i-2) | evalsigne(1) | evalvarn(vx);
                for (j=i+1; j<ly; j++)
                  z[j-l]=ladd((GEN)x[j],(GEN)y[j]);
                z[2]=(long)p1; return z;
              }
              avma = tetpil;
            }
          }
          avma = av;
          return zeroser(vx,ly-2+valp(y));
	
	case t_RFRAC: case t_RFRACN:
	  if (gcmp0(y)) return gcopy(x);

	  l = valp(x)-gval(y,vy); l += gcmp0(x)? 3: lg(x);
	  if (l<3) return gcopy(x);

	  av=avma; ty=typ(y[2]);
          p1 = is_scalar_t(ty)? (GEN)y[2]: greffe((GEN)y[2],l,1);
          p1 = gdiv((GEN)y[1], p1); tetpil=avma;
          return gerepile(av,tetpil,gadd(p1,x));

	default: err(operf,"+",tx,ty);
      }

    case t_RFRAC:
      if (!is_rfrac_t(ty)) err(operi,"+",tx,ty);
      return addrfrac(x,y);
    case t_RFRACN:
      if (!is_rfrac_t(ty)) err(operi,"+",tx,ty);
      z=cgetg(3,t_RFRACN); av=avma;
      p1=gmul((GEN)x[1],(GEN)y[2]);
      p2=gmul((GEN)x[2],(GEN)y[1]); tetpil=avma;
      z[1]=lpile(av,tetpil, gadd(p1,p2));
      z[2]=lmul((GEN)x[2],(GEN)y[2]); return z;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); ly = lg(y);
      if (lx!=ly || tx!=ty) err(operi,"+",tx,ty);
      z=cgetg(ly,ty);
      for (i=1; i<ly; i++)
	z[i]=ladd((GEN)x[i],(GEN)y[i]);
      return z;
  }
  err(operf,"+",tx,ty);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                        MULTIPLICATION                          **/
/**                                                                **/
/********************************************************************/
#define fix_frac(z) if (signe(z[2])<0)\
{\
  setsigne(z[1],-signe(z[1]));\
  setsigne(z[2],1);\
}

/* assume z[1] was created last */
#define fix_frac_if_int(z) if (is_pm1(z[2]))\
  z = gerepileupto((long)(z+3), (GEN)z[1]);

/* assume z[1] was created last */
#define fix_frac_if_int_GC(z,tetpil) { if (is_pm1(z[2]))\
  z = gerepileupto((long)(z+3), (GEN)z[1]);\
else\
  gerepilemanyvec((long)z, tetpil, z+1, 2); }

GEN
fix_rfrac_if_pol(GEN x, GEN y)
{
  if (gcmp1(y)) return x;
  if (typ(y) != t_POL)
  {
    if (typ(x) != t_POL || gvar2(y) > varn(x))
      return gdiv(x,y);
  }
  else if (varn(y) > varn(x)) return gdiv(x,y);
  return NULL;
}

static long
mingvar(GEN x, GEN y)
{
  long i = gvar(x);
  long j = gvar(y);
  return min(i,j);
}

GEN
mulscalrfrac(GEN x, GEN y)
{
  GEN p1,z,y1,y2,cx,cy1,cy2;
  long tetpil,tx;

  if (gcmp0(x)) return gcopy(x);

  y1=(GEN)y[1]; if (gcmp0(y1)) return gcopy(y1);
  y2=(GEN)y[2]; tx = typ(x);
  z = cgetg(3, t_RFRAC);
  if (is_const_t(tx) || varn(x) > mingvar(y1,y2)) { cx = x; x = gun; }
  else
  {
    p1 = ggcd(x,y2); if (isnonscalar(p1)) { x=gdeuc(x,p1); y2=gdeuc(y2,p1); }
    cx = content(x); if (!gcmp1(cx)) x = gdiv(x,cx);
  }
  cy1 = content(y1); if (!gcmp1(cy1)) y1 = gdiv(y1,cy1);
  cy2 = content(y2); if (!gcmp1(cy2)) y2 = gdiv(y2,cy2);
  if (x != gun) y1 = gmul(y1,x);
  x = gdiv(gmul(cx,cy1), cy2);
  cy1 = numer(x);
  cy2 = denom(x); tetpil = avma;
  z[2] = lmul(y2, cy2);
  z[1] = lmul(y1, cy1);
  p1 = fix_rfrac_if_pol((GEN)z[1],(GEN)z[2]);
  if (p1) return gerepileupto((long)(z+3), p1);
  gerepilemanyvec((long)z,tetpil,z+1,2); return z;
}

static GEN
mulrfrac(GEN x, GEN y)
{
  GEN z = cgetg(3,t_RFRAC), p1;
  GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
  GEN y1 = (GEN)y[1], y2 = (GEN)y[2];
  long tetpil;

  p1 = ggcd(x1, y2); if (!gcmp1(p1)) { x1 = gdiv(x1,p1); y2 = gdiv(y2,p1); }
  p1 = ggcd(x2, y1); if (!gcmp1(p1)) { x2 = gdiv(x2,p1); y1 = gdiv(y1,p1); }
  tetpil = avma;
  z[2] = lmul(x2,y2);
  z[1] = lmul(x1,y1);
  p1 = fix_rfrac_if_pol((GEN)z[1],(GEN)z[2]);
  if (p1) return gerepileupto((long)(z+3), p1);
  gerepilemanyvec((long)z,tetpil,z+1,2); return z;
}

GEN
to_Kronecker(GEN P, GEN Q)
{
  /* P(X) = sum Mod(.,Q(Y)) * X^i, lift then set X := Y^(2n-1) */
  long i,j,k,l, lx = lgef(P), N = ((lgef(Q)-3)<<1) + 1, vQ = varn(Q);
  GEN p1, y = cgetg((N-2)*(lx-2) + 2, t_POL);
  for (k=i=2; i<lx; i++)
  {
    p1 = (GEN)P[i];
    if ((l=typ(p1)) == t_POLMOD) { p1 = (GEN)p1[2]; l = typ(p1); }
    if (is_scalar_t(l) || varn(p1)<vQ) { y[k++] = (long)p1; j = 3; }
    else
    {
      l = lgef(p1);
      for (j=2; j < l; j++) y[k++] = p1[j];
    }
    if (i == lx-1) break;
    for (   ; j < N; j++) y[k++] = zero;
  }
  y[1] = evalsigne(1)|evalvarn(vQ)|evallgef(k);
  return y;
}

int
ff_poltype(GEN *x, GEN *p, GEN *pol)
{
  GEN Q, P = *x, pr,p1,p2,y;
  long i, lx;

  if (!signe(P)) return 0;
  lx = lgef(P); Q = *pol;
  for (i=2; i<lx; i++)
  {
    p1 = (GEN)P[i]; if (typ(p1) != t_POLMOD) {Q=NULL;break;}
    p2 = (GEN)p1[1];
    if (Q==NULL) Q = p2;
    else if (p2 != Q)
    {
      if (!gegal(p2, Q))
      {
        if (DEBUGMEM) err(warner,"different modulus in ff_poltype");
        return 0;
      }
      if (DEBUGMEM > 2) err(warner,"different pointers in ff_poltype");
    }
  }
  if (Q) {
    *x = P = to_Kronecker(P, Q);
    *pol = Q; lx = lgef(P);
  }
  pr = *p; y = cgetg(lx, t_POL);
  for (i=lx-1; i>1; i--)
  {
    p1 = (GEN)P[i];
    switch(typ(p1))
    {
      case t_INTMOD: break;
      case t_INT:
        if (*p) p1 = modii(p1, *p);
        y[i] = (long)p1; continue;
      default:
        return (Q && !pr)? 1: 0;
    }
    p2 = (GEN)p1[1];
    if (pr==NULL) pr = p2;
    else if (p2 != pr)
    {
      if (!egalii(p2, pr))
      {
        if (DEBUGMEM) err(warner,"different modulus in ff_poltype");
        return 0;
      }
      if (DEBUGMEM > 2) err(warner,"different pointers in ff_poltype");
    }
    y[i] = p1[2];
  }
  y[1] = evalsigne(1)|evalvarn(varn(P))|evallgef(lx);
  *x = y; *p = pr; return (Q || pr);
}

GEN
gmul(GEN x, GEN y)
{
  long tx,ty,lx,ly,vx,vy,i,j,k,l,av,tetpil;
  GEN z,p1,p2,p3,p4;

  if (x == y) return gsqr(x);
  tx=typ(x); ty=typ(y);
  if (is_const_t(tx) && is_const_t(ty))
  {
    if (tx>ty) { p1=x; x=y; y=p1; i=tx; tx=ty; ty=i; }
  }
  else
  {
    vx=gvar(x); vy=gvar(y);
    if (!is_matvec_t(ty))
      if (is_matvec_t(tx) || vx<vy || (vx==vy && tx>ty))
      {
	p1=x; x=y; y=p1;
        i=tx; tx=ty; ty=i;
	i=vx; vx=vy; vy=i;
      }
    if (ty==t_POLMOD) return op_polmod(gmul,x,y,tx);
  }

  if (is_scalar_t(ty))
  {
    switch(tx)
    {
      case t_INT:
        switch(ty)
	{
	  case t_INT:  return mulii(x,y);
	  case t_REAL: return mulir(x,y);

	  case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)y[1];
	    (void)new_chunk(lgefint(p2)<<2);
            p1=mulii(modii(x,p2),(GEN)y[2]); avma=(long)z;
	    z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;

	  case t_FRAC:
            if (!signe(x)) return gzero;
            z=cgetg(3,t_FRAC);
            p1 = mppgcd(x,(GEN)y[2]);
            if (is_pm1(p1))
            {
              avma = (long)z;
              z[2] = licopy((GEN)y[2]);
              z[1] = lmulii((GEN)y[1], x);
            }
            else
            {
              x = divii(x,p1); tetpil = avma;
              z[2] = ldivii((GEN)y[2], p1);
              z[1] = lmulii((GEN)y[1], x);
              fix_frac_if_int_GC(z,tetpil);
            }
            return z;

          case t_FRACN: z=cgetg(3,t_FRACN);
	    z[1]=lmulii(x,(GEN)y[1]);
	    z[2]=licopy((GEN)y[2]); return z;
	
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=lmul(x,(GEN)y[1]);
	    z[2]=lmul(x,(GEN)y[2]); return z;
	
	  case t_PADIC:
	    if (!signe(x)) return gzero;
	    l=avma; p1=cgetp(y); gaffect(x,p1); tetpil=avma;
	    return gerepile(l,tetpil,gmul(p1,y));
	
	  case t_QUAD: z=cgetg(4,t_QUAD);
	    copyifstack(y[1], z[1]);
	    z[2]=lmul(x,(GEN)y[2]);
	    z[3]=lmul(x,(GEN)y[3]); return z;
	}
	
      case t_REAL:
        switch(ty)
	{
	  case t_REAL: return mulrr(x,y);

	  case t_FRAC: case t_FRACN:
	    l=avma; p1=cgetr(lg(x)); tetpil=avma; gaffect(y,p1);
	    p2=mulrr(p1,x); return gerepile(l,tetpil,p2);
	
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=lmul(x,(GEN)y[1]);
	    z[2]=lmul(x,(GEN)y[2]); return z;
	
	  case t_QUAD:
	    l=avma; p1=co8(y,lg(x)); tetpil=avma;
	    return gerepile(l,tetpil,gmul(p1,x));
	
	  default: err(operf,"*",tx,ty);
	}
	
      case t_INTMOD:
        switch(ty)
	{
	  case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)x[1]; p1=(GEN)y[1];
	    if (p1==p2 || egalii(p1,p2))
            {
              icopyifstack(p2,z[1]);
              if (!is_bigint(p2))
              {
                z[2] = lstoi(mulssmod(itos((GEN)x[2]),itos((GEN)y[2]), p2[2]));
                return z;
              }
            }
            else
            { p2 = mppgcd(p1,p2); z[1] = (long)p2; }
            av=avma;
            (void)new_chunk(lgefint(x[1]) + (lgefint(p1)<<1));
	    p1=mulii((GEN)x[2],(GEN)y[2]); avma=av;
	    z[2]=lmodii(p1,p2); return z;
	
	  case t_FRAC: case t_FRACN: z=cgetg(3,t_INTMOD); p2=(GEN)x[1];
            (void)new_chunk(lgefint(p2)<<2);
            p1 = mulii((GEN)y[1], mpinvmod((GEN)y[2],p2));
            p1 = mulii(modii(p1,p2),(GEN)x[2]); avma=(long)z;
            z[2] = lmodii(p1,p2); icopyifstack(p2,z[1]); return z;
	
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=lmul(x,(GEN)y[1]);
	    z[2]=lmul(x,(GEN)y[2]); return z;
	
	  case t_PADIC:
	    l=avma; p1=cgetg(3,t_INTMOD);
	    p1[1]=x[1]; p1[2]=lgeti(lg(x[1]));
	    gaffect(y,p1); tetpil=avma;
	    return gerepile(l,tetpil,gmul(x,p1));

	  case t_QUAD: z=cgetg(4,t_QUAD);
            copyifstack(y[1], z[1]);
	    z[2]=lmul(x,(GEN)y[2]);
            z[3]=lmul(x,(GEN)y[3]); return z;
	}
	
      case t_FRAC: case t_FRACN:
        switch(ty)
	{
	  case t_FRAC:
          {
            GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
            GEN y1 = (GEN)y[1], y2 = (GEN)y[2];
            z=cgetg(3,t_FRAC);
            p1 = mppgcd(x1, y2);
            if (!is_pm1(p1)) { x1 = divii(x1,p1); y2 = divii(y2,p1); }
            p1 = mppgcd(x2, y1);
            if (!is_pm1(p1)) { x2 = divii(x2,p1); y1 = divii(y1,p1); }
            tetpil = avma;
            z[2] = lmulii(x2,y2);
            z[1] = lmulii(x1,y1);
            fix_frac_if_int_GC(z,tetpil); return z;
          }
	  case t_FRACN: z=cgetg(3,t_FRACN);
	    z[1]=lmulii((GEN)x[1],(GEN)y[1]);
	    z[2]=lmulii((GEN)x[2],(GEN)y[2]); return z;
	
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
	    z[1]=lmul((GEN)y[1],x);
	    z[2]=lmul((GEN)y[2],x); return z;
	
	  case t_PADIC:
	    if (!signe(x[1])) return gzero;
	    l=avma; p1=cgetp(y); gaffect(x,p1); tetpil=avma;
            return gerepile(l,tetpil,gmul(p1,y));
	
	  case t_QUAD: z=cgetg(4,t_QUAD);
	    copyifstack(y[1], z[1]);
	    z[2]=lmul((GEN)y[2],x);
	    z[3]=lmul((GEN)y[3],x); return z;
	}
	
      case t_COMPLEX:
        switch(ty)
	{
	  case t_COMPLEX: z=cgetg(3,t_COMPLEX); l=avma;
            p1=gmul((GEN)x[1],(GEN)y[1]);
            p2=gmul((GEN)x[2],(GEN)y[2]);
	    x=gadd((GEN)x[1],(GEN)x[2]);
            y=gadd((GEN)y[1],(GEN)y[2]);
	    y=gmul(x,y); x=gadd(p1,p2);
	    tetpil=avma; z[1]=lsub(p1,p2); z[2]=lsub(y,x);
	    gerepilemanyvec(l,tetpil,z+1,2); return z;
	
	  case t_PADIC:
	    if (krosg(-1,(GEN)y[2]))
	    {
	      z=cgetg(3,t_COMPLEX);
	      z[1]=lmul((GEN)x[1],y);
	      z[2]=lmul((GEN)x[2],y); return z;
	    }
	    av=avma;
            if (signe(y[4])) l=precp(y);
            else
            {
              l=valp(y)+1; if (l<=0) l=1;
            }
            p1=cvtop(x,(GEN)y[2],l); tetpil=avma;
            return gerepile(av,tetpil,gmul(p1,y));
	
	  case t_QUAD:
	    lx=precision(x); if (!lx) err(operi,"*",tx,ty);
	    l=avma; p1=co8(y,lx); tetpil=avma;
	    return gerepile(l,tetpil,gmul(p1,x));
	}
	
      case t_PADIC:
        switch(ty)
	{
	  case t_PADIC:
	    if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"*",tx,ty);
            l = valp(x)+valp(y);
	    if (!signe(x[4])) { z=gcopy(x); setvalp(z,l); return z; }
	    if (!signe(y[4])) { z=gcopy(y); setvalp(z,l); return z; }

	    p1 = (precp(x) > precp(y))? y: x;
	    z=cgetp(p1); setvalp(z,l); av=avma;
	    modiiz(mulii((GEN)x[4],(GEN)y[4]),(GEN)p1[3],(GEN)z[4]);
	    avma=av; return z;
	
	  case t_QUAD:
	    if (kro_quad((GEN)y[1],(GEN)x[2])== -1)
	    {
	      z=cgetg(4,t_QUAD);
	      copyifstack(y[1], z[1]);
	      z[2]=lmul((GEN)y[2],x);
	      z[3]=lmul((GEN)y[3],x); return z;
	    }
            l = signe(x[4])? precp(x): valp(x)+1;
	    av=avma; p1=cvtop(y,(GEN)x[2],l); tetpil=avma;
            return gerepile(av,tetpil,gmul(p1,x));
	}
	
      case t_QUAD: z=cgetg(4,t_QUAD);
        p1=(GEN)x[1]; p2=(GEN)y[1];
        if (!gegal(p1,p2)) err(operi,"*",tx,ty);

        copyifstack(p2, z[1]); l=avma;
        p2=gmul((GEN)x[2],(GEN)y[2]);
        p3=gmul((GEN)x[3],(GEN)y[3]);
        p4=gmul(gneg_i((GEN)p1[2]),p3);

        if (gcmp0((GEN)p1[3]))
        {
          tetpil=avma;
          z[2]=lpile(l,tetpil,gadd(p4,p2)); l=avma;
          p2=gmul((GEN)x[2],(GEN)y[3]);
          p3=gmul((GEN)x[3],(GEN)y[2]); tetpil=avma;
          z[3]=lpile(l,tetpil,gadd(p2,p3)); return z;
        }

        p1 = gadd(gmul((GEN)x[2],(GEN)y[3]), gmul((GEN)x[3],(GEN)y[2]));
        tetpil=avma;
        z[2]=ladd(p2,p4);
        z[3]=ladd(p1,p3);
        gerepilemanyvec(l,tetpil,z+2,2); return z;
    }
    err(bugparier,"multiplication");
  }
  if (is_noncalc_t(tx) || is_noncalc_t(ty)) err(operf,"*",tx,ty);

  /* here !isscalar(y) */
  if (is_matvec_t(ty))
  {
    ly=lg(y);
    if (!is_matvec_t(tx))
    {
      z=cgetg(ly,ty);
      for (i=1; i<ly; i++) z[i]=lmul(x,(GEN)y[i]);
      return z;
    }
    lx=lg(x);

    switch(tx)
    {
      case t_VEC:
        switch(ty)
        {
          case t_COL:
            if (lx!=ly) err(operi,"*",tx,ty);
            z=gzero; l=avma;
            for (i=1; i<lx; i++)
            {
              p1=gmul((GEN)x[i],(GEN)y[i]);
              tetpil=avma; z=gadd(z,p1);
            }
            return gerepile(l,tetpil,z);

          case t_MAT:
            if (ly==1) return cgetg(1,t_VEC);
            l=lg(y[1]); if (lx!=l) err(operi,"*",tx,ty);

            z=cgetg(ly,tx);
            for (i=1; i<ly; i++)
            {
              p1=gzero; av=avma;
              for (j=1; j<lx; j++)
              {
                p2=gmul((GEN)x[j],gcoeff(y,j,i));
                tetpil=avma; p1=gadd(p1,p2);
              }
              z[i]=lpile(av,tetpil,p1);
            }
            return z;

          default: err(operf,"*",tx,ty);
        }

      case t_COL:
        switch(ty)
        {
          case t_VEC:
            z=cgetg(ly,t_MAT);
            for (i=1; i<ly; i++)
            {
              p1 = gmul((GEN)y[i],x);
              if (typ(p1) != t_COL) err(operi,"*",tx,ty);
              z[i]=(long)p1;
            }
            return z;

          case t_MAT:
            if (ly!=1 && lg(y[1])!=2) err(operi,"*",tx,ty);

            z=cgetg(ly,t_MAT);
            for (i=1; i<ly; i++) z[i]=lmul(gcoeff(y,1,i),x);
            return z;

          default: err(operf,"*",tx,ty);
        }

      case t_MAT:
        switch(ty)
        {
          case t_VEC:
            if (lx!=2) err(operi,"*",tx,ty);
            z=cgetg(ly,t_MAT);
            for (i=1; i<ly; i++) z[i]=lmul((GEN)y[i],(GEN)x[1]);
            return z;

          case t_COL:
            if (lx!=ly) err(operi,"*",tx,ty);
            if (lx==1) return gcopy(y);

            lx=lg(x[1]); z=cgetg(lx,t_COL);
            for (i=1; i<lx; i++)
            {
              p1=gzero; l=avma;
              for (j=1; j<ly; j++)
              {
                p2=gmul(gcoeff(x,i,j),(GEN)y[j]);
                tetpil=avma; p1=gadd(p1,p2);
              }
              z[i]=lpile(l,tetpil,p1);
            }
            return z;

          case t_MAT:
            if (ly==1) return cgetg(ly,t_MAT);
            if (lx != lg(y[1])) err(operi,"*",tx,ty);
            z=cgetg(ly,t_MAT);
            if (lx==1)
            {
              for (i=1; i<ly; i++) z[i]=lgetg(1,t_COL);
              return z;
            }
            l=lg(x[1]);
            for (j=1; j<ly; j++)
            {
              z[j] = lgetg(l,t_COL);
              for (i=1; i<l; i++)
              {
                p1=gzero; av=avma;
                for (k=1; k<lx; k++)
                {
                  p2=gmul(gcoeff(x,i,k),gcoeff(y,k,j));
                  tetpil=avma; p1=gadd(p1,p2);
                }
                coeff(z,i,j)=lpile(av,tetpil,p1);
              }
            }
            return z;
        }
    }
    err(bugparier,"multiplication");
  }
  /* now !ismatvec(x and y) */

  if (vx>vy || (vx==vy && is_scalar_t(tx)))
  {
    if (isexactzero(x)) 
    {
      if (vy == BIGINT) err(operf,"*",tx,ty);
      return zeropol(vy);
    }
    if (tx == t_INT && is_pm1(x))
      return (signe(x)>0) ? gcopy(y): gneg(y);
    if (tx == t_POLMOD && vx == vy && ty != t_SER)
    {
      av = avma;
      return gerepileupto(av, op_polmod(gmul, x, to_polmod(y,(GEN)x[1]), tx));
    }
    switch(ty)
    {
      case t_POL:
	if (isexactzero(y)) return zeropol(vy);
        ly = lgef(y); z = cgetg(ly,t_POL); z[1]=y[1];
        for (i=2; i<ly; i++) z[i]=lmul(x,(GEN)y[i]);
        return normalizepol_i(z,ly);
	
      case t_SER:
	if (!signe(y)) return gcopy(y);
	ly=lg(y); z=cgetg(ly,t_SER);
	for (i=2; i<ly; i++) z[i]=lmul(x,(GEN)y[i]);
	z[1]=y[1]; return normalize(z);
	
      case t_RFRAC: return mulscalrfrac(x,y);
      case t_RFRACN: av=avma; z=cgetg(3,t_RFRACN);
        z[1]=lmul(x,(GEN)y[1]);
        z[2]=lcopy((GEN)y[2]); return z;
      default: err(operf,"*",tx,ty);
    }
  }

  if (tx>ty) { p1=x; x=y; y=p1; i=tx; tx=ty; ty=i; }
  switch(tx)
  {
    case t_POL:
      switch (ty)
      {
	case t_POL:
        {
#if 0
/* Too dangerous / cumbersome to correct here. Don't use t_POLMODS of 
 * t_INTMODs to represent elements of finite fields. Implement a finite
 * field type instead and compute with polynomials with integer coeffs in
 * Kronecker form...
 * For gsqr, it's still idiotic to let ff_poltype correct bad implementations,
 * but less dangerous.
 */
          GEN a = x,b = y
          GEN p = NULL, pol = NULL;
          long av = avma;
          if (ff_poltype(&x,&p,&pol) && ff_poltype(&y,&p,&pol))
          {
            /* fprintferr("HUM"); */
            if (pol && varn(x) != varn(y))
              x = to_Kronecker(x,pol);
            z = quickmul(x+2, y+2, lgef(x)-2, lgef(y)-2);
            if (p) z = Fp_pol(z,p);
            if (pol) z = from_Kronecker(z,pol);
            z = gerepileupto(av, z);
          }
          else
          {
            avma = av;
            z = quickmul(a+2, b+2, lgef(a)-2, lgef(b)-2);
          }
#else
          z = quickmul(x+2, y+2, lgef(x)-2, lgef(y)-2);
#endif
          setvarn(z,vx); return z;
        }
	case t_SER:
	  if (gcmp0(x)) return zeropol(vx);
	  if (gcmp0(y)) return zeroser(vx, valp(y)+gval(x,vx));
	  p1=greffe(x,lg(y),0); p2=gmul(p1,y);
          free(p1); return p2;
	
        case t_RFRAC: return mulscalrfrac(x,y);
        case t_RFRACN: av=avma; z=cgetg(3,t_RFRACN);
          z[1]=lmul(x,(GEN)y[1]);
          z[2]=lcopy((GEN)y[2]); return z;
	
	default: err(operf,"*",tx,ty);
      }
	
    case t_SER:
      switch (ty)
      {
	case t_SER:
	  if (gcmp0(x) || gcmp0(y)) return zeroser(vx, valp(x)+valp(y));
          lx=lg(x); ly=lg(y);
	  if (lx>ly) { k=ly; ly=lx; lx=k; p1=y; y=x; x=p1; }
          z = cgetg(lx,t_SER);
	  z[1] = evalvalp(valp(x)+valp(y)) | evalvarn(vx) | evalsigne(1);
          x += 2; y += 2; z += 2; lx -= 3;
          p2 = (GEN)gpmalloc((lx+1)*sizeof(long));
	  for (i=0; i<=lx; i++)
          {
	    p2[i] = !isexactzero((GEN)y[i]);
            p1 = gzero; av = avma;
            for (j=0; j<=i; j++)
              if (p2[j])
                p1 = gadd(p1, gmul((GEN)y[j],(GEN)x[i-j]));
            z[i] = lpileupto(av,p1);
          }
          z -= 2; /* back to normalcy */
          free(p2); return normalize(z);

	case t_RFRAC: case t_RFRACN:
	  if (gcmp0(y)) return zeropol(vx);
	  if (gcmp0(x)) return zeroser(vx, valp(x)+gval(y,vx));
	  l=avma; p1=gmul((GEN)y[1],x); tetpil=avma;
          return gerepile(l,tetpil,gdiv(p1,(GEN)y[2]));
	
	default: err(operf,"*",tx,ty);
      }
	
    /* (tx,ty) == t_RFRAC <==> ty == t_RFRAC */
    case t_RFRAC: return mulrfrac(x,y);
    case t_RFRACN:
      if (!is_rfrac_t(ty)) err(operf,"*",tx,ty);
      av=avma; z=cgetg(3,ty);
      z[1]=lmul((GEN)x[1],(GEN)y[1]);
      z[2]=lmul((GEN)x[2],(GEN)y[2]); return z;
  }
  if (tx==ty)
    switch(tx)
    {
      case t_QFI: return compimag(x,y);
      case t_QFR: return compreal(x,y);
    }
  err(operf,"*",tx,ty);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                           DIVISION                             **/
/**                                                                **/
/********************************************************************/

static
GEN divrfracscal(GEN x, GEN y)
{
  long Y[3]; Y[1]=un; Y[2]=(long)y;
  return mulrfrac(x,Y);
}

static
GEN divscalrfrac(GEN x, GEN y)
{
  long Y[3]; Y[1]=y[2]; Y[2]=y[1];
  return mulscalrfrac(x,Y);
}

static
GEN divrfrac(GEN x, GEN y)
{
  long Y[3]; Y[1]=y[2]; Y[2]=y[1];
  return mulrfrac(x,Y);
}

GEN
gdiv(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), lx,ly,vx,vy,i,j,k,l,av,tetpil;
  GEN z,p1,p2,p3;

  if (y == gun) return gcopy(x);
  if (tx==t_INT && is_const_t(ty))
  {
    switch (signe(x))
    {
      case 0:
        if (gcmp0(y)) err(gdiver2);
        if (ty != t_INTMOD) return gzero;
        z = cgetg(3,t_INTMOD); icopyifstack(y[1],z[1]); z[2]=zero;
        return z;
      case  1:
        if (is_pm1(x)) return ginv(y);
        break;
      case -1: 
        if (is_pm1(x)) { av = avma; return gerepileupto(av, ginv(gneg(y))); }
    }
    switch(ty)
    {
      case t_INT:
        av=avma; z=dvmdii(x,y,&p1);
        if (p1==gzero) return z;
        (void)new_chunk((lgefint(x) + lgefint(y)) << 2);
        p1 = mppgcd(y,p1);
        avma=av; z=cgetg(3,t_FRAC);
        if (is_pm1(p1)) {
          z[1]=licopy(x);
          z[2]=licopy(y);
        }
        else {
          z[1]=ldivii(x,p1);
          z[2]=ldivii(y,p1);
        }
        fix_frac(z); return z;
            
      case t_REAL:
        return divir(x,y);
            
      case t_INTMOD:
        z=cgetg(3,t_INTMOD); p2=(GEN)y[1];
        (void)new_chunk(lgefint(p2)<<2);
        p1=mulii(modii(x,p2), mpinvmod((GEN)y[2],p2)); avma=(long)z;
        z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;

      case t_FRAC:
        z=cgetg(3,t_FRAC);
        p1 = mppgcd(x,(GEN)y[1]);
        if (is_pm1(p1))
        {
          avma = (long)z; tetpil = 0;
          z[2] = licopy((GEN)y[1]);
        }
        else
        {
          x = divii(x,p1); tetpil = avma;
          z[2] = ldivii((GEN)y[1], p1);
        }
        z[1] = lmulii((GEN)y[2], x);
        fix_frac(z);
        if (tetpil)
        { fix_frac_if_int_GC(z,tetpil); }
        else
          fix_frac_if_int(z);
        return z;
            
      case t_FRACN:
        z=cgetg(3,t_FRACN);
        z[1]=lmulii((GEN)y[2], x);
        z[2]=licopy((GEN)y[1]);
        fix_frac(z); return z;

      case t_PADIC:
        l=avma; p1=cgetp(y); gaffect(x,p1); tetpil=avma;
        return gerepile(l,tetpil,gdiv(p1,y));
            
      case t_COMPLEX: case t_QUAD:
        l=avma; p1=gnorm(y); p2=gmul(x,gconj(y)); tetpil=avma;
        return gerepile(l,tetpil,gdiv(p2,p1));
    }
  }
  if (gcmp0(y)) err(gdiver2);

  if (is_const_t(tx) && is_const_t(ty))
  {
    switch(tx)
    {
      case t_REAL:
	switch(ty)
	{
	  case t_INT:
	    return divri(x,y);

	  case t_REAL:
	    return divrr(x,y);

	  case t_FRAC: case t_FRACN:
	    l=avma; p1=cgetg(lg(x),t_REAL); gaffect(y,p1);
	    return gerepile(l,(long)p1,divrr(x,p1));

	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
            l=avma; p1=gnorm(y);
	    p2=gmul(x,(GEN)y[1]);
            p3=gmul(x,(GEN)y[2]);
	    if (!gcmp0(p3)) p3 = gneg_i(p3);
            tetpil=avma;
	    z[1]=ldiv(p2,p1);
            z[2]=ldiv(p3,p1);
	    gerepilemanyvec(l,tetpil,z+1,2); return z;

	  case t_QUAD:
	    l=avma; p1=co8(y,lg(x)); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(x,p1));

	  case t_INTMOD: case t_PADIC: err(operf,"/",tx,ty);
	}

      case t_INTMOD:
	switch(ty)
	{
	  case t_INT: z=cgetg(3,t_INTMOD); p2=(GEN)x[1];
	    (void)new_chunk(lgefint(p2)<<2);
	    p1=mulii((GEN)x[2], mpinvmod(y,p2)); avma=(long)z;
            z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;

	  case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)x[1]; p1=(GEN)y[1];
	    if (p1==p2 || egalii(p1,p2))
            { icopyifstack(p2,z[1]); }
            else
            { p2 = mppgcd(p1,p2); z[1] = (long)p2; }
            av=avma; (void)new_chunk(lgefint(x[1]) + (lgefint(p1) << 1));
	    p1=mulii((GEN)x[2], mpinvmod((GEN)y[2],p2)); avma=av;
            z[2]=lmodii(p1,p2); return z;

	  case t_FRAC: z=cgetg(3,t_INTMOD); p2=(GEN)x[1];
            (void)new_chunk(lgefint(p2)<<2);
            p1=mulii((GEN)y[2], mpinvmod((GEN)y[1],p2));
            p1=mulii(modii(p1,p2),(GEN)x[2]); avma=(long)z;
            z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;

	  case t_FRACN:
	    l=avma; p1=gred(y); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(x,p1));

	  case t_COMPLEX: case t_QUAD:
	    l=avma; p1=gnorm(y); p2=gmul(x,gconj(y)); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p2,p1));

	  case t_PADIC:
	    l=avma; p1=cgetg(3,t_INTMOD); p1[1]=x[1]; p1[2]=lgeti(lg(x[1]));
	    gaffect(y,p1); tetpil=avma; return gerepile(l,tetpil,gdiv(x,p1));

	  case t_REAL: err(operf,"/",tx,ty);
	}

      case t_FRAC: case t_FRACN:
	switch(ty)
	{
	  case t_INT:
          z = cgetg(3, tx);
	  if (tx == t_FRAC)
          {
            p1 = mppgcd(y,(GEN)x[1]);
            if (is_pm1(p1))
            {
              avma = (long)z; tetpil = 0;
              z[1] = licopy((GEN)x[1]);
            }
            else
            {
              y = divii(y,p1); tetpil = avma;
              z[1] = ldivii((GEN)x[1], p1);
            }
          }
          else
          {
            tetpil = 0;
            z[1] = licopy((GEN)x[1]);
          }
          z[2] = lmulii((GEN)x[2],y);
          fix_frac(z); 
          if (tetpil) fix_frac_if_int_GC(z,tetpil);
          return z;

	  case t_REAL:
	    l=avma; p1=cgetg(lg(y),t_REAL); gaffect(x,p1);
	    p2=divrr(p1,y); return gerepile(l,(long)p1,p2);

	  case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)y[1];
            (void)new_chunk(lgefint(p2)<<2);
	    p1=mulii((GEN)y[2],(GEN)x[2]);
	    p1=mulii(mpinvmod(p1,p2), modii((GEN)x[1],p2)); avma=(long)z;
	    z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;

	  case t_FRAC: if (tx == t_FRACN) ty=t_FRACN;
          case t_FRACN:
	    z = cgetg(3,ty);
            if (ty == t_FRAC)
            {
              GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
              GEN y1 = (GEN)y[1], y2 = (GEN)y[2];
              p1 = mppgcd(x1, y1);
              if (!is_pm1(p1)) { x1 = divii(x1,p1); y1 = divii(y1,p1); }
              p1 = mppgcd(x2, y2);
              if (!is_pm1(p1)) { x2 = divii(x2,p1); y2 = divii(y2,p1); }
              tetpil = avma;
              z[2] = lmulii(x2,y1);
              z[1] = lmulii(x1,y2);
              fix_frac(z);
              fix_frac_if_int_GC(z,tetpil);
            }
            else
            {
              z[1]=lmulii((GEN)x[1],(GEN)y[2]);
              z[2]=lmulii((GEN)x[2],(GEN)y[1]);
              fix_frac(z);
            }
            return z;

	  case t_COMPLEX: z=cgetg(3,t_COMPLEX);
            l=avma; p1=gnorm(y);
	    p2=gmul(x,(GEN)y[1]);
	    p3=gmul(x,(GEN)y[2]);
            if(!gcmp0(p3)) p3 = gneg_i(p3);
	    tetpil=avma;
	    z[1]=ldiv(p2,p1); z[2]=ldiv(p3,p1);
	    gerepilemanyvec(l,tetpil,z+1,2); return z;

	  case t_PADIC:
	    if (!signe(x[1])) return gzero;

	    l=avma; p1=cgetp(y); gaffect(x,p1);
	    tetpil=avma; return gerepile(l,tetpil,gdiv(p1,y));

	  case t_QUAD:
	    l=avma; p1=gnorm(y); p2=gmul(x,gconj(y)); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p2,p1));
	}

      case t_COMPLEX:
	switch(ty)
	{
	  case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_FRACN:
	    z=cgetg(3,t_COMPLEX);
	    z[1]=ldiv((GEN)x[1],y);
	    z[2]=ldiv((GEN)x[2],y); return z;

	  case t_COMPLEX:
	    l=avma; p1=gnorm(y); p2=gconj(y); p2=gmul(x,p2); tetpil=avma;
	    return gerepile(l,tetpil, gdiv(p2,p1));

	  case t_PADIC:
	    if (krosg(-1,(GEN)y[2])== -1)
	    {
	      z=cgetg(3,t_COMPLEX);
	      z[1]=ldiv((GEN)x[1],y);
	      z[2]=ldiv((GEN)x[2],y); return z;
	    }
	    av=avma; p1=cvtop(x,(GEN)y[2],precp(y)); tetpil=avma;
	    return gerepile(av,tetpil,gdiv(p1,y));

	  case t_QUAD:
	    lx=precision(x); if (!lx) err(operi,"/",tx,ty);
	    l=avma; p1=co8(y,lx); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(x,p1));
	}

      case t_PADIC:
	switch(ty)
	{
	  case t_INT: case t_FRAC: case t_FRACN:
	    l=avma;
	    if (signe(x[4])) { p1=cgetp(x); gaffect(y,p1); }
	    else p1=cvtop(y,(GEN)x[2],(valp(x)>0)?valp(x):1);
	    tetpil=avma; return gerepile(l,tetpil,gdiv(x,p1));

	  case t_INTMOD:
	    l=avma; p1=cgetg(3,t_INTMOD);
	    p1[1]=y[1]; p1[2]=lgeti(lg(y[1]));
	    gaffect(x,p1); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p1,y));

	  case t_PADIC:
	    if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"/",tx,ty);
	    if (!signe(x[4]))
	    {
	      z=gcopy(x); setvalp(z,valp(x)-valp(y));
	      return z;
	    }

	    p1=(precp(x)>precp(y)) ? y : x;
	    z=cgetp(p1); l=avma;
	    setvalp(z,valp(x)-valp(y));
	    p2=mpinvmod((GEN)y[4],(GEN)p1[3]);
	    modiiz(mulii((GEN)x[4],p2),(GEN)p1[3],(GEN)z[4]);
	    avma=l; return z;

	  case t_COMPLEX: case t_QUAD:
	    l=avma; p1=gmul(x,gconj(y)); p2=gnorm(y); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p1,p2));

	  case t_REAL:
	    err(operf,"/",tx,ty);
	}

      case t_QUAD:
	switch (ty)
	{
	  case t_INT: case t_INTMOD: case t_FRAC: case t_FRACN:
	    z=cgetg(4,t_QUAD);
	    copyifstack(x[1], z[1]);
	    for (i=2; i<4; i++) z[i]=ldiv((GEN)x[i],y);
	    return z;

	  case t_REAL:
	    l=avma; p1=co8(x,lg(y)); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p1,y));

	  case t_PADIC:
	    l=avma; p1=cvtop(x,(GEN)y[2],precp(y));
	    tetpil=avma; return gerepile(l,tetpil,gdiv(p1,y));

	  case t_COMPLEX:
	    ly=precision(y); if (!ly) err(operi,"/",tx,ty);
	    l=avma; p1=co8(x,ly); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p1,y));

	  case t_QUAD:
	    k=x[1]; l=y[1];
	    if (!gegal((GEN)k,(GEN)l)) err(operi,"/",tx,ty);
	    l=avma; p1=gnorm(y); p2=gmul(x,gconj(y)); tetpil=avma;
	    return gerepile(l,tetpil,gdiv(p2,p1));
	}
    }
    err(bugparier,"division");
  }

  vx=gvar(x); vy=gvar(y);
  if (ty==t_POLMOD && (tx==t_POLMOD || vy<vx))
  {
    z=cgetg(3,t_POLMOD);
    if (tx==t_POLMOD)
    {
      k=x[1]; l=y[1];
      if (gegal((GEN)k,(GEN)l))
      {
        copyifstack(k, z[1]); av=avma;
        p1 = ginvmod((GEN)y[2],(GEN)z[1]);
        p2 = gmul((GEN)x[2],p1);
      }
      else
      {
        vx=varn(x[1]); vy=varn(y[1]);
        if (vx==vy)
        {
          z[1]=lgcd((GEN)k,(GEN)l); av=avma;
          p1=ginvmod((GEN)y[2],(GEN)z[1]);
          p2=gmul((GEN)x[2],p1);
        }
        else
        {
          if (vx<vy)
          { copyifstack(k,z[1]); av=avma; p2=gdiv((GEN)x[2],y); }
          else
          { 
            copyifstack(l,z[1]); av=avma;
            p1 = ginvmod((GEN)y[2],(GEN)z[1]);
            p2 = gmul(x, p1);
          }
        }
      }
      p2 = gmod(p2,(GEN)z[1]);
    }
    else
    {
      copyifstack(y[1],z[1]); av=avma;
      p1 = ginvmod((GEN)y[2],(GEN)y[1]);
      p2 = gmul(x,p1);
    }
    z[2]=lpileupto(av, p2); return z;
  }
  if (tx == t_POLMOD && vx<vy)
  {
    z=cgetg(3,t_POLMOD);
    copyifstack(x[1],z[1]);
    z[2]=ldiv((GEN)x[2],y); return z;
  }
  if (vx == vy)
  {
    av = avma;
    if (tx == t_POLMOD)
      return gerepileupto(av, gdiv(x, to_polmod(y,(GEN)x[1])));
    if (ty == t_POLMOD)
      return gerepileupto(av, gdiv(to_polmod(x,(GEN)y[1]), y));
  }
  if (is_noncalc_t(tx) || is_noncalc_t(ty)) err(operf,"/",tx, ty);
  /* now x and y are not both is_scalar_t */

  lx = lg(x);
  if ((vx<vy && (!is_matvec_t(tx) || !is_matvec_t(ty)))
     || (vx==vy && is_scalar_t(ty)) || (is_matvec_t(tx) && !is_matvec_t(ty)))
  {
    if (tx == t_RFRAC) return divrfracscal(x,y);
    z = cgetg(lx,tx);
    if (tx == t_RFRACN)
    {
      z[2]=lmul((GEN)x[2],y);
      z[1]=lcopy((GEN)x[1]); return z;
    }
    switch(tx)
    {
      case t_POL: lx = lgef(x);
      case t_SER: z[1] = x[1];
      case t_VEC: case t_COL: case t_MAT:
        if (ty == t_POLMOD || ty == t_INTMOD)
        {
          if (!gcmp1(y)) y = ginv(y); /* garbage, left alone */
          for (i=lontyp[tx]; i<lx; i++) z[i]=lmul((GEN)x[i],y);
          return z;
        }
        else
          for (i=lontyp[tx]; i<lx; i++) z[i]=ldiv((GEN)x[i],y);
        return z;
    }
    err(operf,"/",tx,ty);
  }

  ly=lg(y); 
  if (vy<vx || (vy==vx && is_scalar_t(tx)))
  {
    switch(ty)
    {
      case t_POL:
	if (lgef(y)==3) return gdiv(x,(GEN)y[2]);
        if (isexactzero(x)) return zeropol(vy);
        av=avma; z=cgetg(3,t_RFRAC); z[1]=(long)x; z[2]=(long)y;
        return gerepileupto(av,gred_rfrac(z));

      case t_SER:
	if (gcmp0(x))
	{
          l=avma; p1=ginv(y); tetpil=avma; /* a ameliorer !!!! */
	  return gerepile(l,tetpil,gmul(x,p1));
	}
        p1 = (GEN)gpmalloc(ly*sizeof(long));
        p1[0] = evaltyp(t_SER) | evallg(ly);
	p1[1] = evalsigne(1) | evalvalp(0) | evalvarn(vy);
        p1[2] = (long)x; for (i=3; i<ly; i++) p1[i]=zero;
        y = gdiv(p1,y); free(p1); return y;

      case t_RFRAC: return divscalrfrac(x,y);
      case t_RFRACN: z=cgetg(ly,t_RFRACN);
        z[1]=lmul(x,(GEN)y[2]);
        z[2]=lcopy((GEN)y[1]); return z;

      case t_MAT:
	if (ly==1 || lg(y[1])!=ly) err(operi,"/",tx,ty);
	l=avma; p1=invmat(y); tetpil=avma;
	return gerepile(l,tetpil,gmul(x,p1));

      case t_VEC: case t_COL: err(operf,"/",tx,ty);
    }
    err(operf,"/",tx,ty);
  }

  /* ici vx=vy et tx>=10 et ty>=10*/
  switch(tx)
  {
    case t_POL:
      switch(ty)
      {
	case t_POL:
          if (lgef(y)==3) return gdiv(x,(GEN)y[2]);
          if (isexactzero(x)) return zeropol(vy);
          av=avma; z=cgetg(3,t_RFRAC); z[1]=(long)x; z[2]=(long)y;
          return gerepileupto(av,gred_rfrac(z));

	case t_SER:
	  if (gcmp0(x)) return zeropol(vx);
	  p1=greffe(x,ly,0); p2=gdiv(p1,y);
          free(p1); return p2;

        case t_RFRAC: return divscalrfrac(x,y);
        case t_RFRACN: z=cgetg(ly,t_RFRACN);
	  z[1]=lmul(x,(GEN)y[2]);
	  z[2]=lcopy((GEN)y[1]); return z;

	default: err(operf,"/",tx,ty);
      }

    case t_SER:
      switch(ty)
      {
	case t_POL:
	  p1=greffe(y,lx,0); p2=gdiv(x,p1);
          free(p1); return p2;

	case t_SER:
        {
          GEN y_lead;

          l = valp(x) - valp(y);
	  if (gcmp0(x)) return zeroser(vx,l);
          y_lead = (GEN)y[2];
          if (gcmp0(y_lead)) /* normalize denominator if leading term is 0 */
          {
            err(warner,"normalizing a series with 0 leading term");
            for (i=3,y++; i<ly; i++,y++)
            {
              y_lead = (GEN)y[2]; ly--; l--;
              if (!gcmp0(y_lead)) break;
            }
            if (i==ly) err(gdiver2);
          }
	  if (ly < lx) lx = ly;
	  p2 = (GEN)gpmalloc(lx*sizeof(long));
	  for (i=3; i<lx; i++)
          {
            p1 = (GEN)y[i];
            if (isexactzero(p1)) p2[i] = 0;
            else
            {
              av = avma; p2[i] = lclone(gneg_i(p1));
              avma = av;
            }
          }
	  z = cgetg(lx,t_SER);
          z[1] = evalvalp(l) | evalvarn(vx) | evalsigne(1);
	  z[2] = ldiv((GEN)x[2], y_lead);
	  for (i=3; i<lx; i++)
	  {
	    av=avma; p1 = (GEN)x[i];
	    for (j=2; j<i; j++)
            {
              l = i-j+2;
              if (p2[l])
                p1 = gadd(p1, gmul((GEN)z[j], (GEN)p2[l]));
            }
            p1 = gdiv(p1, y_lead);
	    tetpil=avma; z[i]=lpile(av,tetpil, forcecopy(p1));
	  }
          for (i=3; i<lx; i++)
            if (p2[i]) gunclone((GEN)p2[i]);
          free(p2); return z;
        }

	case t_RFRAC: case t_RFRACN:
	  l=avma; p2=gmul(x,(GEN)y[2]); tetpil=avma;
	  return gerepile(l,tetpil,gdiv(p2,(GEN)y[1]));

	default: err(operf,"/",tx,ty);
      }

    case t_RFRAC: case t_RFRACN:
      switch(ty)
      {
	case t_POL:
          if (tx==t_RFRAC) return  divrfracscal(x,y);
          z=cgetg(3,t_RFRACN);
          z[2]=lmul((GEN)x[2],y);
	  z[1]=lcopy((GEN)x[1]); return z;

	case t_SER:
	  l=avma; p2=gmul((GEN)x[2],y); tetpil=avma;
	  return gerepile(l,tetpil, gdiv((GEN)x[1],p2));

	case t_RFRAC: case t_RFRACN:
	  if (tx == t_RFRACN) ty=t_RFRACN;
          if (ty != t_RFRACN) return divrfrac(x,y);
	  z=cgetg(3,t_RFRACN);
	  z[1]=lmul((GEN)x[1],(GEN)y[2]);
          z[2]=lmul((GEN)x[2],(GEN)y[1]); return z;

	default: err(operf,"/",tx,ty);
      }

    case t_VEC: case t_COL: case t_MAT:
      if (!is_matvec_t(ty))
      {
	z=cgetg(lx,tx);
	for (i=1; i<lx; i++) z[i]=ldiv((GEN)x[i],y);
	return z;
      }
      if (ty!=t_MAT || ly==1 || lg(y[1])!=ly) err(operi,"/",tx,ty);
      l=avma; p1=invmat(y); tetpil=avma;
      return gerepile(l,tetpil,gmul(x,p1));
     case t_QFI:case t_QFR:
       break;
     default: err(operf,"/",tx,ty);
  }
  /*Here tx==t_QFI || tx==t_QFR*/
  if (tx==ty)
  {
    l=signe(y[2]); setsigne(y[2],-l);
    switch(tx)
    {
      case t_QFI: z = compimag(x,y);
        setsigne(y[2],l); return z;
      case t_QFR:
        k=signe(y[4]); setsigne(y[4],-k); z=compreal(x,y);
        setsigne(y[2],l); setsigne(y[4],k); return z;
    }
  }
  err(operf,"/",tx,ty);
  return NULL; /* not reached */
}
