/********************************************************************/
/**                                                                **/
/**                   TRANSCENDENTAL FONCTIONS                     **/
/**                                                                **/
/********************************************************************/
/* $Id$ */
#include "pari.h"

#ifdef LONG_IS_64BIT
# define C31 (9223372036854775808.0) /* VERYBIGINT * 1.0 */
# define SQRTVERYBIGINT 3037000500   /* ceil(sqrt(VERYBIGINT)) */
# define CBRTVERYBIGINT 2097152      /* ceil(cbrt(VERYBIGINT)) */
#else
# define C31 (2147483648.0)
# define SQRTVERYBIGINT 46341
# define CBRTVERYBIGINT  1291
#endif


/********************************************************************/
/**                                                                **/
/**                        FONCTION PI                             **/
/**                                                                **/
/********************************************************************/

void
constpi(long prec)
{
  GEN p1,p2,p3,tmppi;
  long l,n,n1,av1,av2;
  double alpha;

#define k1  545140134
#define k2  13591409
#define k3  640320
#define alpha2 (1.4722004/(BYTES_IN_LONG/4))  /* 3*log(k3/12)/(32*log(2)) */

  if (gpi && lg(gpi) >= prec) return;

  av1 = avma; tmppi = newbloc(prec);
  *tmppi = evaltyp(t_REAL) | evallg(prec);

  n=(long)(1+(prec-2)/alpha2);
  n1=6*n-1; p1=cgetr(prec);
  p2=addsi(k2,mulss(n,k1));
  affir(p2,p1);

  /* initialisation longueur mantisse */
  if (prec>=4) l=4; else l=prec;
  setlg(p1,l); alpha=l;

  av2 = avma;
  while (n)
  {
    if (n < CBRTVERYBIGINT)
      p3 = divrs(mulsr(n1-4,mulsr(n1*(n1-2),p1)),n*n*n);
    else
    {
      if (n1 < SQRTVERYBIGINT)
	p3 = divrs(divrs(mulsr(n1-4,mulsr(n1*(n1-2),p1)),n*n),n);
      else
	p3 = divrs(divrs(mulsr(n1-4,mulsr(n1,mulsr(n1-2,p1))),n*n),n);
    }
    p3 = divrs(divrs(p3,100100025), 327843840);
    subisz(p2,k1,p2); subirz(p2,p3,p1);
    alpha += alpha2; l = (long)(1+alpha); /* nouvelle longueur mantisse */
    if (l>prec) l=prec;
    setlg(p1,l); avma = av2;
    n--; n1-=6;
  }
  p1 = divsr(53360,p1);
  mulrrz(p1,gsqrt(stoi(k3),prec), tmppi);
  gunclone(gpi); avma = av1;  gpi = tmppi;
}

GEN
mppi(long prec)
{
  GEN x = cgetr(prec);
  constpi(prec+1); affrr(gpi,x); return x;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION EULER                            **/
/**                                                                **/
/********************************************************************/

void
consteuler(long prec)
{
  GEN u,v,a,b,tmpeuler;
  long l,n,k,x,av1,av2;

  if (geuler && lg(geuler) >= prec) return;

  av1 = avma; tmpeuler = newbloc(prec);
  *tmpeuler = evaltyp(t_REAL) | evallg(prec);

  l = prec+1; x = (long) (1 + (bit_accuracy(l) >> 2) * LOG2);
  a=cgetr(l); affsr(x,a); u=mplog(a); setsigne(u,-1); affrr(u,a);
  b=cgetr(l); affsr(1,b);
  v=cgetr(l); affsr(1,v);
  n=(long)(1+3.591*x); /* z=3.591: z*[ ln(z)-1 ]=1 */
  av2 = avma;
  if (x < SQRTVERYBIGINT)
  {
    long xx = x*x;
    for (k=1; k<=n; k++)
    {
      divrsz(mulsr(xx,b),k*k, b);
      divrsz(addrr(divrs(mulsr(xx,a),k),b),k, a);
      addrrz(u,a,u); addrrz(v,b,v); avma = av2;
    }
  }
  else
  {
    GEN xx = mulss(x,x);
    for (k=1; k<=n; k++)
    {
      divrsz(mulir(xx,b),k*k, b);
      divrsz(addrr(divrs(mulir(xx,a),k),b),k, a);
      addrrz(u,a,u); addrrz(v,b,v); avma = av2;
    }
  }
  divrrz(u,v,tmpeuler);
  gunclone(geuler); avma = av1; geuler = tmpeuler;
}

GEN
mpeuler(long prec)
{
  GEN x=cgetr(prec);
  consteuler(prec+1); affrr(geuler,x); return x;
}

/********************************************************************/
/**                                                                **/
/**       CONVERSION DE TYPES POUR FONCTIONS TRANSCENDANTES        **/
/**                                                                **/
/********************************************************************/

GEN
transc(GEN (*f)(GEN,long), GEN x, long prec)
{
  GEN p1,p2,y;
  long lx,i,av,tetpil;

  av=avma;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      p1=cgetr(prec); gaffect(x,p1); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_COMPLEX: case t_QUAD:
      av=avma; p1=cgetr(prec); affsr(1,p1);
      p1=gmul(x,p1); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_POL: case t_RFRAC: case t_RFRACN:
      p1=tayl(x,gvar(x),precdl); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,typ(x));
      for (i=1; i<lx; i++)
	y[i] = (long) f((GEN)x[i],prec);
      return y;

    case t_POLMOD:
      av=avma; p1=roots((GEN)x[1],prec); lx=lg(p1); p2=cgetg(lx,t_COL);
      for (i=1; i<lx; i++) p2[i]=lpoleval((GEN)x[2],(GEN)p1[i]);
      tetpil=avma; y=cgetg(lx,t_COL);
      for (i=1; i<lx; i++)
        y[i] = (long)f((GEN)p2[i],prec);
      return gerepile(av,tetpil,y);

    case t_QFR: case t_QFI:
      err(talker,"quadratic forms cannot be used in transcendental functions");
  }
  return f(x,prec);
}

/*******************************************************************/
/*                                                                 */
/*                            POWERING                             */
/*                                                                 */
/*******************************************************************/
GEN real_unit_form(GEN x);
GEN imag_unit_form(GEN x);

static GEN
puiss0(GEN x)
{
  long lx,i;
  GEN y;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN: case t_PADIC:
      return gun;

    case t_INTMOD:
      y=cgetg(3,t_INTMOD); copyifstack(x[1],y[1]); y[2]=un; break;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); y[1]=un; y[2]=zero; break;

    case t_QUAD:
      y=cgetg(4,t_QUAD); copyifstack(x[1],y[1]);
      y[2]=un; y[3]=zero; break;

    case t_POLMOD:
      y=cgetg(3,t_POLMOD); copyifstack(x[1],y[1]);
      y[2]=lpolun[varn(x[1])]; break;

    case t_POL: case t_SER: case t_RFRAC: case t_RFRACN:
      return polun[gvar(x)];

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      if (lx != (lg(x[1]))) err(mattype1,"gpowgs");
      y = idmat(lx-1);
      for (i=1; i<lx; i++) coeff(y,i,i) = lpuigs(gcoeff(x,i,i),0);
      break;
    case t_QFR: return real_unit_form(x);
    case t_QFI: return imag_unit_form(x);
    case t_VEC: case t_COL:
      err(typeer,"gpowgs");
  }
  return y;
}

/* INTEGER POWERING (a^n for integer a and integer n > 1)
 *
 * Nonpositive powers and exponent one should be handled by gpow() and
 * gpowgs() in trans1.c, which at the time of this writing is the only place
 * where the following is [slated to be] used.
 *
 * Use left shift binary algorithm (RS is wasteful: multiplies big numbers,
 * with LS one of them is the base, hence small). If result is nonzero, its
 * sign is set to s (= +-1) regardless of what it would have been. This makes
 * life easier for gpow()/gpowgs(), which otherwise might do a
 * setsigne(gun,-1)... -- GN1998May04
 */
static GEN
puissii(GEN a, GEN n, long s)
{
  long av,*p,man,k,nb,lim;
  GEN y;

  if (!signe(a)) return gzero; /* a==0 */
  if (lgefint(a)==3)
  { /* easy if |a| < 3 */
    if (a[2] == 1) return (s>0)? gun: negi(gun);
    if (a[2] == 2) { a = shifti(gun, itos(n)); setsigne(a,s); return a; }
  }
  if (lgefint(n)==3)
  { /* or if |n| < 3 */
    if (n[2] == 1) { a = icopy(a); setsigne(a,s); return a; }
    if (n[2] == 2) return sqri(a);
  }
  /* be paranoid about memory consumption */
  av=avma; lim=stack_lim(av,1);
  y = a; p = n+2; man = *p;
  /* normalize, i.e set highest bit to 1 (we know man != 0) */
  k = 1+bfffo(man); man<<=k; k = BITS_IN_LONG-k;
  /* first bit is now implicit */
  for (nb=lgefint(n)-2;;)
  {
    for (; k; man<<=1,k--)
    {
      y = sqri(y);
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"[1]: puissii");
        y = gerepileupto(av,y);
      }
      if (man < 0)
      { /* first bit is set: multiply by the base */
        y = mulii(y,a);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if (DEBUGMEM>1) err(warnmem,"[2]: puissii");
          y = gerepileupto(av,y);
        }
      }
    }
    nb--; if (nb == 0) break;
    man = *++p, k = BITS_IN_LONG;
  }
  setsigne(y,s); return gerepileupto(av,y);
}

GEN
gpowgs(GEN x, long n)
{
  long lim,av,m,tx;
  static long gn[3] = {evaltyp(t_INT)|m_evallg(3), 0, 0};
  GEN y;

  if (n == 0) return puiss0(x);
  if (n == 1) return gcopy(x);
  if (n ==-1) return ginv(x);
  if (n>0)
    { gn[1] = evalsigne( 1) | evallgefint(3); gn[2]= n; }
  else
    { gn[1] = evalsigne(-1) | evallgefint(3); gn[2]=-n; }
 /* If gpowgs were only ever called from gpow, the switch wouldn't be needed.
  * In fact, under current word and bit field sizes, an integer power with
  * multiword exponent will always overflow.  But it seems easier to call
  * puissii|powmodulo() with a mock-up GEN as 2nd argument than to write
  * separate versions for a long exponent.  Note that n = HIGHBIT is an
  * invalid argument. --GN
  */
  switch((tx=typ(x)))
  {
    case t_INT:
    {
      long sx=signe(x), sr = (sx<0 && (n&1))? -1: 1;
      if (n>0) return puissii(x,(GEN)gn,sr);
      if (!sx) err(talker, "division by zero in gpowgs");
      if (is_pm1(x)) return (sr < 0)? icopy(x): gun;
      /* n<0, |x|>1 */
      y=cgetg(3,t_FRAC); setsigne(gn,1);
      y[1]=(sr>0)? un: lnegi(gun);
      y[2]=(long)puissii(x,(GEN)gn,1); /* force denominator > 0 */
      return y;
    }
    case t_INTMOD:
      y=cgetg(3,tx); copyifstack(x[1],y[1]);
      y[2]=(long)powmodulo((GEN)(x[2]),(GEN)gn,(GEN)(x[1]));
      return y;
    case t_FRAC: case t_FRACN:
    {
      long sr = ((n&1) && (signe(x[1])!=signe(x[2])))? -1: 1;
      if (n<0)
      {
        if (!signe((GEN)x[1]))
          err(talker, "division by zero fraction in gpowgs");
        setsigne((GEN)gn,1);
        if (is_pm1((GEN)x[1])) /* +-1/x[2] inverts to an integer */
          return puissii((GEN)x[2],(GEN)gn,sr);
        y=cgetg(3,tx);
        y[1]=(long)puissii((GEN)x[2],(GEN)gn,sr);
        y[2]=(long)puissii((GEN)x[1],(GEN)gn,1);
        return y;
      }
      else /* n > 0 */
      {
        y=cgetg(3,tx);
        if (!signe((GEN)x[1])) { y[1]=zero; y[2]=un; return y; }
        y[1]=(long)puissii((GEN)x[1],(GEN)gn,sr);
        y[2]=(long)puissii((GEN)x[2],(GEN)gn,1);
        return y;
      }
    }
    case t_POL: case t_POLMOD:
      return powgi(x,gn);
    case t_RFRAC: case t_RFRACN:
    {
      av=avma; y=cgetg(3,tx); m = labs(n);
      y[1]=lpuigs((GEN)x[1],m);
      y[2]=lpuigs((GEN)x[2],m);
      if (n<0) y=ginv(y);	/* let ginv worry about normalizations */
      return gerepileupto(av,y);
    }
    default:
      m = labs(n);
      av=avma; y=NULL; lim=stack_lim(av,1);
      for (; m>1; m>>=1)
      {
        if (m&1) y = y? gmul(y,x): x;
        x=gsqr(x);
        if (low_stack(lim, stack_lim(av,1)))
        {
          GEN *gptr[2]; gptr[0]=&x; gptr[1]=&y;
          if(DEBUGMEM>1) err(warnmem,"[3]: gpowgs");
          gerepilemany(av,gptr,y? 2: 1);
        }
      }
      y = y? gmul(y,x): x;
      if (n<=0) y=ginv(y);
      return gerepileupto(av,y);
  }
}

GEN
pow_monome(GEN x, GEN nn)
{
  long n,m,i,j,dd,tetpil, av = avma;
  GEN p1,y;
  if (is_bigint(nn)) err(talker,"power overflow in pow_monome");
  n = itos(nn); m = labs(n);
  j=lgef(x); dd=(j-3)*m+3;
  p1=cgetg(dd,t_POL); m = labs(n);
  p1[1] = evalsigne(1) | evallgef(dd) | evalvarn(varn(x));
  for (i=2; i<dd-1; i++) p1[i]=zero;
  p1[i]=lpuigs((GEN)x[j-1],m);
  if (n>0) return p1;

  tetpil=avma; y=cgetg(3,t_RFRAC);
  y[1]=(long)denom((GEN)p1[i]);
  y[2]=lmul(p1,(GEN)y[1]); return gerepile(av,tetpil,y);
}

/* n is assumed to be an integer */
GEN
powgi(GEN x, GEN n)
{
  long lim,av,i,j,m,tx, sn=signe(n);
  GEN y, p1;

  if (typ(n) != t_INT) err(talker,"not an integral exponent in powgi");
  if (!sn) return puiss0(x);

  switch(tx=typ(x))
  {/* catch some types here, instead of trying gpowgs() first, because of
    * the simpler call interface to puissii() and powmodulo() -- even though
    * for integer/rational bases other than 0,+-1 and non-wordsized
    * exponents the result will be certain to overflow. --GN
    */
    case t_INT:
    {
      long sx=signe(x), sr = (sx<0 && mod2(n))? -1: 1;
      if (sn>0) return puissii(x,n,sr);
      if (!sx) err(talker, "division by zero in powgi");
      if (is_pm1(x)) return (sr < 0)? icopy(x): gun;
      /* n<0, |x|>1 */
      y=cgetg(3,t_FRAC); setsigne(n,1); /* temporarily replace n by abs(n) */
      y[1]=(sr>0)? un: lnegi(gun);
      y[2]=(long)puissii(x,n,1);
      setsigne(n,-1); return y;
    }
    case t_INTMOD:
      y=cgetg(3,tx); copyifstack(x[1],y[1]);
      y[2]=(long)powmodulo((GEN)x[2],n,(GEN)x[1]);
      return y;
    case t_FRAC: case t_FRACN:
    {
      long sr = (mod2(n) && (signe(x[1])!=signe(x[2]))) ? -1 : 1;
      if (sn<0)
      {
        if (!signe((GEN)x[1]))
          err(talker, "division by zero fraction in powgi");
        setsigne(n,1);
        if (is_pm1((GEN)x[1])) /* +-1/x[2] inverts to an integer */
          y=puissii((GEN)x[2],n,sr);
        else
        {
          y=cgetg(3,tx);
          y[1]=(long)puissii((GEN)x[2],n,sr);
          y[2]=(long)puissii((GEN)x[1],n,1);
        }
        setsigne(n,-1); return y;
      }
      else /* n > 0 */
      {
        y=cgetg(3,tx);
        if (!signe((GEN)x[1])) { y[1]=zero; y[2]=un; return y; }
        y[1]=(long)puissii((GEN)x[1],n,sr);
        y[2]=(long)puissii((GEN)x[2],n,1);
        return y;
      }
    }
    case t_POL:
      if (ismonome(x)) return pow_monome(x,n);
    default:
      av=avma; lim=stack_lim(av,1);
      p1 = n+2; m = *p1;
      y=x; j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
      for (i=lgefint(n)-2;;)
      {
        for (; j; m<<=1,j--)
        {
          y=gsqr(y);
          if (low_stack(lim, stack_lim(av,1)))
          {
            if(DEBUGMEM>1) err(warnmem,"[1]: powgi");
            y = gerepileupto(av, y);
          }
          if (m<0) y=gmul(y,x);
          if (low_stack(lim, stack_lim(av,1)))
          {
            if(DEBUGMEM>1) err(warnmem,"[2]: powgi");
            y = gerepileupto(av, y);
          }
        }
        if (--i == 0) break;
        m = *++p1, j = BITS_IN_LONG;
      }
      if (sn<0) y = ginv(y);
      return av==avma? gcopy(y): gerepileupto(av,y);
  }
}

/* we suppose n != 0, and valp(x) = 0 */
static GEN
ser_pui(GEN x, GEN n, long prec)
{
  long av,tetpil,lx,i,j;
  GEN p1,p2,y,alp;

  if (gvar9(n) > varn(x))
  {
    GEN lead = (GEN)x[2];
    if (gcmp1(lead))
    {
      av=avma; alp = gclone(gadd(n,gun)); avma=av;
      y=cgetg(lx=lg(x),t_SER);
      y[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(x));
      y[2] = un;
      for (i=3; i<lx; i++)
      {
	av=avma; p1=gzero;
	for (j=1; j<i-1; j++)
	{
	  p2 = gsubgs(gmulgs(alp,j),i-2);
	  p1 = gadd(p1,gmul(gmul(p2,(GEN)x[j+2]),(GEN)y[i-j]));
	}
	tetpil=avma; y[i]=lpile(av,tetpil,gdivgs(p1,i-2));
      }
      gunclone(alp); return y;
    }
    av=avma; p1=gdiv(x,lead); p1[2] = un; /* in case it's inexact */
    p1=gpow(p1,n,prec); p2=gpow(lead,n,prec);
    tetpil=avma; return gerepile(av,tetpil,gmul(p1,p2));
  }
  av=avma; y=gmul(n,glog(x,prec)); tetpil=avma;
  return gerepile(av,tetpil,gexp(y,prec));
}

GEN
gpow(GEN x, GEN n, long prec)
{
  long av,tetpil,i,lx,tx;
  GEN y;

  if (typ(n)==t_INT) return powgi(x,n);
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i]=lpui((GEN)x[i],n,prec);
    return y;
  }
  if (tx==t_SER)
  {
    if (valp(x))
      err(talker,"not an integer exponent for non invertible series in gpow");
    if (lg(x) == 2) return gcopy(x); /* O(1) */
    return ser_pui(x,n,prec);
  }
  av=avma;
  if (gcmp0(x))
  {
    n = greal(n);
    if (gsigne(n)<=0) err(talker,"zero to a non positive exponent in gpow");
    i = precision(x); if (!i) return gcopy(x);

    x=ground(gmulsg(gexpo(x),n));
    if (lgefint(x)<=3)
    {
      i = itos(x);
      if (labs(i) < (long)HIGHEXPOBIT)
      {
        avma=av; y=cgetr(3); y[1]=evalexpo(i); y[2]=0;
        return y;
      }
    }
    err(talker,"underflow or overflow in gpow");
  }
  i = (long) precision(n); if (i) prec=i;
  y=gmul(n,glog(x,prec)); tetpil=avma;
  return gerepile(av,tetpil,gexp(y,prec));
}

/********************************************************************/
/**                                                                **/
/**                        RACINE CARREE                           **/
/**                                                                **/
/********************************************************************/

GEN
mpsqrt(GEN x)
{
  long l,l0,l1,l2,s,eps,n,i,ex,av;
  double beta;
  GEN y,p1,p2,p3;

  if (typ(x)!=t_REAL) err(typeer,"mpsqrt");
  s=signe(x); if (s<0) err(talker,"negative argument in mpsqrt");
  if (!s)
  {
    y = cgetr(3);
    y[1] = evalexpo(expo(x)>>1);
    y[2] = 0; return y;
  }
  l=lg(x); y=cgetr(l); av=avma;

  p1=cgetr(l+1); affrr(x,p1);
  ex=expo(x); eps = ex & 1; ex >>= 1; 
  setexpo(p1,eps); setlg(p1,3);

  n=(long)(2+log((double) (l-2))/LOG2);
  p2=cgetr(l+1); p2[1]=evalexpo(0) | evalsigne(1);
  beta=sqrt((eps+1) * (2 + p1[2]/C31));
  p2[2]=(long)((beta-2)*C31);
  if (!p2[2]) { p2[2]=HIGHBIT; setexpo(p2,1); }
  for (i=3; i<=l; i++) p2[i]=0;
  setlg(p2,3);

  p3=cgetr(l+1); l-=2; l1=1; l2=3;
  for (i=1; i<=n; i++)
  {
    l0 = l1<<1;
    if (l0<=l)
      { l2 += l1; l1=l0; }
    else
      { l2 += l+1-l1; l1=l+1; }
    setlg(p3,l1+2); setlg(p1,l1+2); setlg(p2,l2);
    divrrz(p1,p2,p3); addrrz(p2,p3,p2); setexpo(p2,expo(p2)-1);
  }
  affrr(p2,y); setexpo(y,expo(y)+ex);
  avma=av; return y;
}

static GEN
padic_sqrt(GEN x)
{
  long av = avma, av2,lim,e,r,lpp,lp,pp;
  GEN y;

  e=valp(x); y=cgetg(5,t_PADIC); copyifstack(x[2],y[2]);
  if (gcmp0(x))
  {
    y[4] = zero; e = (e+1)>>1;
    y[3] = lpuigs((GEN)x[2],e);
    y[1] = evalvalp(e) | evalprecp(precp(x));
    return y;
  }
  if (e & 1) err(sqrter6);
  e>>=1; setvalp(y,e); y[3] = y[2];
  pp = precp(x);
  if (egalii(gdeux, (GEN)x[2]))
  {
    lp=3; y[4] = un; r = mod8((GEN)x[4]);
    if ((r!=1 && pp>=2) && (r!=5 || pp!=2)) err(sqrter5);
    if (pp <= lp) { setprecp(y,1); return y; }

    x = dummycopy(x); setvalp(x,0); setvalp(y,0);
    av2=avma; lim = stack_lim(av2,2);
    y[3] = lstoi(8);
    for(;;)
    {
      lpp=lp; lp=(lp<<1)-1;
      if (lp < pp) y[3] = lshifti((GEN)y[3], lpp-1);
      else
        { lp=pp; y[3] = x[3]; }
      setprecp(y,lp); y = gdiv(gadd(y, gdiv(x,y)), gdeux);
      if (lp < pp) lp--;
      if (cmpii((GEN)y[4], (GEN)y[3]) >= 0)
        y[4] = lsubii((GEN)y[4], (GEN)y[3]);

      if (pp <= lp) break;
      if (low_stack(lim,stack_lim(av2,2)))
      {
        if (DEBUGMEM > 1) err(warnmem,"padic_sqrt");
        y = gerepileupto(av2,y);
      }
    }
    y = gcopy(y);
  }
  else /* p != 2 */
  {
    lp=1; y[4] = (long)mpsqrtmod((GEN)x[4],(GEN)x[2]);
    if (!y[4]) err(sqrter5);
    if (pp <= lp) { setprecp(y,1); return y; }

    x = dummycopy(x); setvalp(x,0); setvalp(y,0);
    av2=avma; lim = stack_lim(av2,2);
    for(;;)
    {
      lp<<=1;
      if (lp < pp) y[3] = lsqri((GEN)y[3]);
      else
        { lp=pp; y[3] = x[3]; }
      setprecp(y,lp); y = gdiv(gadd(y, gdiv(x,y)), gdeux);

      if (pp <= lp) break;
      if (low_stack(lim,stack_lim(av2,2)))
      {
        if (DEBUGMEM > 1) err(warnmem,"padic_sqrt");
        y = gerepileupto(av2,y);
      }
    }
  }
  setvalp(y,e); return gerepileupto(av,y);
}

GEN
gsqrt(GEN x, long prec)
{
  long av,tetpil,e;
  GEN y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)>=0) return mpsqrt(x);
      y=cgetg(3,t_COMPLEX); y[1]=zero;
      setsigne(x,1); y[2]=lmpsqrt(x); setsigne(x,-1);
      return y;

    case t_INTMOD:
      y=cgetg(3,t_INTMOD); copyifstack(x[1],y[1]);
      p1 = mpsqrtmod((GEN)x[2],(GEN)y[1]);
      if (!p1) err(sqrter5);
      y[2] = (long)p1; return y;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      if (gcmp0((GEN)x[2]))
      {
	long tx=typ(x[1]);

	if ((is_intreal_t(tx) || is_frac_t(tx)) && gsigne((GEN)x[1]) < 0)
	{
	  y[1]=zero; p1=gneg_i((GEN)x[1]); tetpil=avma;
	  y[2]=lpile(av,tetpil,gsqrt(p1,prec));
	  return y;
	}
	y[1]=lsqrt((GEN)x[1],prec);
	y[2]=zero; return y;
      }

      p1=gsqr((GEN)x[1]); p2=gsqr((GEN)x[2]);
      p1=gsqrt(gadd(p1,p2),prec);
      if (gcmp0(p1))
      {
	y[1]=lsqrt(p1,prec);
	y[2]=lcopy((GEN)y[1]);
	return y;
      }

      if (gsigne((GEN)x[1])<0)
      {
	p2=gsub(p1,(GEN)x[1]); p1=gmul2n(p2,-1);
	y[2]=lsqrt(p1,prec); y[1]=ldiv((GEN)x[2],gmul2n((GEN)y[2],1));
	tetpil=avma;
        y = (gsigne((GEN)x[2]) > 0)? gcopy(y): gneg(y);
	return gerepile(av,tetpil,y);
      }

      p1=gmul2n(gadd(p1,(GEN)x[1]),-1);
      tetpil=avma; y[1]=lpile(av,tetpil,gsqrt(p1,prec));
      av=avma; p1=gmul2n((GEN)y[1],1); tetpil=avma;
      y[2]=lpile(av,tetpil,gdiv((GEN)x[2],p1));
      return y;

    case t_PADIC:
      return padic_sqrt(x);

    case t_SER:
      e=valp(x);
      if (gcmp0(x)) return zeroser(varn(x), (e+1)>>1);
      if (e & 1) err(sqrter6);
      /* trick: ser_pui assumes valp(x) = 0 */
      y = ser_pui(x,ghalf,prec);
      y[1] = evalsigne(1) | evalvalp(e>>1) | evalvarn(varn(x));
      return y;
  }
  return transc(gsqrt,x,prec);
}

void
gsqrtz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gsqrtz");
  gaffect(gsqrt(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                    FONCTION EXPONENTIELLE-1                    **/
/**                                                                **/
/********************************************************************/
#ifdef LONG_IS_64BIT
#  define EXMAX 46
#else
#  define EXMAX 22
#endif

GEN
mpexp1(GEN x)
{
  long l,l1,l2,i,n,m,ex,s,av,av2, sx = signe(x);
  double a,b,alpha,beta, gama = 2.0 /* optimized for SUN3 */;
                                    /* KB: 3.0 is better for UltraSparc */
  GEN y,p1,p2,p3,p4,unr;

  if (typ(x)!=t_REAL) err(typeer,"mpexp1");
  if (!sx)
  {
    y=cgetr(3); y[1]=x[1]; y[2]=0; return y;
  }
  l=lg(x); y=cgetr(l); av=avma; /* room for result */

  l2 = l+1; ex = expo(x);
  if (ex > EXMAX) err(talker,"exponent too large in exp");
  alpha = -1-log(2+x[2]/C31)-ex*LOG2;
  beta = 5 + bit_accuracy(l)*LOG2;
  a = sqrt(beta/(gama*LOG2));
  b = (alpha + 0.5*log(beta*gama/LOG2))/LOG2;
  if (a>=b)
  {
    n=(long)(1+sqrt(beta*gama/LOG2));
    m=(long)(1+a-b);
    l2 += m>>TWOPOTBITS_IN_LONG;
  }
  else
  {
    n=(long)(1+beta/alpha);
    m=0;
  }
  unr=cgetr(l2); affsr(1,unr);
  p2=rcopy(unr); setlg(p2,4);
  p4=cgetr(l2); affrr(x,p4); setsigne(p4,1);
  if (m) setexpo(p4,ex-m);

  s=0; l1=4; av2 = avma;
  for (i=n; i>=2; i--)
  {
    setlg(p4,l1); p3 = divrs(p4,i);
    s -= expo(p3); p1 = mulrr(p3,p2); setlg(p1,l1);
    l1 += s>>TWOPOTBITS_IN_LONG; if (l1>l2) l1=l2;
    s %= BITS_IN_LONG;
    setlg(unr,l1); p1 = addrr(unr,p1);
    setlg(p2,l1); affrr(p1,p2); avma = av2;
  }
  setlg(p2,l2); setlg(p4,l2); p2 = mulrr(p4,p2);

  for (i=1; i<=m; i++)
  {
    setlg(p2,l2);
    p2 = mulrr(addsr(2,p2),p2);
  }
  if (sx == -1)
  {
    setlg(unr,l2); p2 = addrr(unr,p2);
    setlg(p2,l2); p2 = ginv(p2);
    p2 = subrr(p2,unr);
  }
  affrr(p2,y); avma = av; return y;
}
#undef EXMAX

/********************************************************************/
/**                                                                **/
/**                   FONCTION EXPONENTIELLE                       **/
/**                                                                **/
/********************************************************************/

GEN
mpexp(GEN x)
{
  long av, sx = signe(x);
  GEN y;

  if (!sx) return addsr(1,x);
  if (sx<0) setsigne(x,1);
  av = avma; y = addsr(1, mpexp1(x));
  if (sx<0) { y = divsr(1,y); setsigne(x,-1); }
  return gerepileupto(av,y);
}

static GEN
paexp(GEN x)
{
  long k,av, e = valp(x), pp = precp(x), n = e + pp;
  GEN y,r,p1;

  if (gcmp0(x)) return gaddgs(x,1);
  if (e<=0 || (!cmpis((GEN)x[2],2) && e==1))
    err(talker,"p-adic argument out of range in gexp");
  av = avma;
  if (egalii(gdeux,(GEN)x[2]))
  {
    n--; e--; k = n/e;
    if (n%e==0) k--;
  }
  else
  {
    p1 = subis((GEN)x[2], 1);
    k = itos(dvmdii(subis(mulis(p1,n), 1), subis(mulis(p1,e), 1), &r));
    if (!signe(r)) k--;
  }
  for (y=gun; k; k--) y = gaddsg(1, gdivgs(gmul(y,x), k));
  return gerepileupto(av, y);
}

GEN
gexp(GEN x, long prec)
{
  long av,tetpil,ex;
  GEN r,y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      return mpexp(x);

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      r=gexp((GEN)x[1],prec);
      gsincos((GEN)x[2],&p2,&p1,prec);
      tetpil=avma;
      y[1]=lmul(r,p1); y[2]=lmul(r,p2);
      gerepilemanyvec(av,tetpil,y+1,2);
      return y;

    case t_PADIC:
      return paexp(x);

    case t_SER:
      if (gcmp0(x)) return gaddsg(1,x);

      ex=valp(x); if (ex<0) err(negexper,"gexp");
      if (ex)
      {
	long i,j,ly=lg(x)+ex;

	y=cgetg(ly,t_SER);
	y[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(x));
        y[2] = un;
	for (i=3; i<ex+2; i++) y[i]=zero;
	for (   ; i<ly; i++)
	{
	  av=avma; p1=gzero;
	  for (j=ex; j<i-1; j++)
	    p1=gadd(p1,gmulgs(gmul((GEN)x[j-ex+2],(GEN)y[i-j]),j));
	  tetpil=avma; y[i]=lpile(av,tetpil,gdivgs(p1,i-2));
	}
	return y;
      }
      av=avma; p1=gcopy(x); p1[2]=zero;
      p2=gexp(normalize(p1),prec);
      p1=gexp((GEN)x[2],prec); tetpil=avma;
      return gerepile(av,tetpil,gmul(p1,p2));

    case t_INTMOD:
      err(typeer,"gexp");
  }
  return transc(gexp,x,prec);
}

void
gexpz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gexpz");
  gaffect(gexp(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION LOGARITHME                       **/
/**                                                                **/
/********************************************************************/

GEN
mplog(GEN x)
{
  long l,l1,l2,m,m1,n,i,ex,s,sgn,ltop,av;
  double alpha,beta,a,b;
  GEN y,p1,p2,p3,p4,p5,unr;

  if (typ(x)!=t_REAL) err(typeer,"mplog");
  if (signe(x)<=0) err(talker,"non positive argument in mplog");
  l=lg(x); sgn = cmpsr(1,x); if (!sgn) return realzero(l);
  y=cgetr(l); ltop=avma;

  l2 = l+1; p2=p1=cgetr(l2); affrr(x,p1);
  av=avma;
  if (sgn > 0) p2 = divsr(1,p1); /* x<1 changer x en 1/x */
  for (m1=1; expo(p2)>0; m1++) p2 = mpsqrt(p2);
  if (m1 > 1 || sgn > 0) { affrr(p2,p1); avma=av; }

  alpha = 1+p1[2]/C31; if (!alpha) alpha = 0.00000001;
  l -= 2; alpha = -log(alpha);
  beta = (BITS_IN_LONG/2)*l*LOG2;
  a = alpha/LOG2;
  b = sqrt((BITS_IN_LONG/2)*l/3.0);
  if (a<=b)
  {
    n=(long)(1+sqrt((BITS_IN_LONG/2)*3.0*l));
    m=(long)(1+b-a);
    l2 += m>>TWOPOTBITS_IN_LONG;
    p4=cgetr(l2); affrr(p1,p4);
    p1 = p4; av=avma;
    for (i=1; i<=m; i++)  p1 = mpsqrt(p1);
    affrr(p1,p4); avma=av;
  }
  else
  {
    n=(long)(1+beta/alpha);
    m=0; p4 = p1;
  }
  unr=cgetr(l2); affsr(1,unr);
  p2=cgetr(l2); p3=cgetr(l2); av=avma;

  /* affrr needed here instead of setlg since prec may DECREASE */
  p1 = cgetr(l2); affrr(subrr(p4,unr), p1);

  p5 = addrr(p4,unr); setlg(p5,l2);
  affrr(divrr(p1,p5), p2);
  affrr(mulrr(p2,p2), p3);
  affrr(divrs(unr,2*n+1), p4); setlg(p4,4); avma=av;

  s=0; ex=expo(p3); l1 = 4;
  for (i=n; i>=1; i--)
  {
    setlg(p3,l1); p5 = mulrr(p4,p3);
    setlg(unr,l1); p1 = divrs(unr,2*i-1);
    s -= ex;
    l1 += s>>TWOPOTBITS_IN_LONG; if (l1>l2) l1=l2;
    s %= BITS_IN_LONG;
    setlg(p1,l1); setlg(p4,l1); setlg(p5,l1);
    p1 = addrr(p1,p5); affrr(p1,p4); avma=av;
  }
  setlg(p4,l2); affrr(mulrr(p2,p4), y);
  setexpo(y, expo(y)+m+m1);
  if (sgn > 0) setsigne(y, -1);
  avma=ltop; return y;
}

GEN
teich(GEN x)
{
  GEN aux,y,z,p1;
  long av,n,k;

  if (typ(x)!=t_PADIC) err(talker,"not a p-adic argument in teichmuller");
  if (!signe(x[4])) return gcopy(x);
  y=cgetp(x); z=(GEN)x[4];
  if (!cmpis((GEN)x[2],2))
  {
    n = mod4(z);
    if (n & 2)
      addsiz(-1,(GEN)x[3],(GEN)y[4]);
    else
      affsi(1,(GEN)y[4]);
    return y;
  }
  av = avma; p1 = addsi(-1,(GEN)x[2]);
  aux = divii(addsi(-1,(GEN)x[3]),p1); n = precp(x);
  for (k=1; k<n; k<<=1)
    z=modii(mulii(z,addsi(1,mulii(aux,addsi(-1,powmodulo(z,p1,(GEN)x[3]))))),
            (GEN)x[3]);
  affii(z,(GEN)y[4]); avma=av; return y;
}

static GEN
palogaux(GEN x)
{
  long av1=avma,tetpil,k,e,pp;
  GEN y,s,y2;

  if (egalii(gun,(GEN)x[4]))
  {
    y=gaddgs(x,-1);
    if (egalii(gdeux,(GEN)x[2]))
    {
      setvalp(y,valp(y)-1);
      if (!gcmp1((GEN)y[3])) y[3]=lshifti((GEN)y[3],-1);
    }
    tetpil=avma; return gerepile(av1,tetpil,gcopy(y));
  }
  y=gdiv(gaddgs(x,-1),gaddgs(x,1)); e=valp(y); pp=e+precp(y);
  if (egalii(gdeux,(GEN)x[2])) pp--;
  else
  {
    long av=avma;
    GEN p1;

    for (p1=stoi(e); cmpsi(pp,p1)>0; pp++)
      p1 = mulii(p1,(GEN)x[2]);
    avma=av; pp-=2;
  }
  k=pp/e; if (!odd(k)) k--;
  y2=gsqr(y); s=gdivgs(gun,k);
  while (k>=3)
  {
    k-=2; s=gadd(gmul(y2,s),gdivgs(gun,k));
  }
  tetpil=avma; return gerepile(av1,tetpil,gmul(s,y));
}

GEN
palog(GEN x)
{
  long av=avma,tetpil;
  GEN p1,y;

  if (!signe(x[4])) err(talker,"zero argument in palog");
  if (cmpis((GEN)x[2],2))
  {
    y=cgetp(x); p1=gsubgs((GEN)x[2],1);
    affii(powmodulo((GEN)x[4],p1,(GEN)x[3]),(GEN)y[4]);
    y=gmulgs(palogaux(y),2); tetpil=avma;
    return gerepile(av,tetpil,gdiv(y,p1));
  }
  y=gsqr(x); setvalp(y,0); tetpil=avma;
  return gerepile(av,tetpil,palogaux(y));
}

GEN
log0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0: return glog(x,prec);
    case 1: return glogagm(x,prec);
    default: err(flagerr,"log");
  }
  return NULL; /* not reached */
}

GEN
glog(GEN x, long prec)
{
  long av,tetpil;
  GEN y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)>=0) return mplog(x);
      y=cgetg(3,t_COMPLEX); y[2]=lmppi(lg(x));
      setsigne(x,1); y[1]=lmplog(x);
      setsigne(x,-1); return y;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); y[2]=larg(x,prec);
      av=avma; p1=glog(gnorm(x),prec); tetpil=avma;
      y[1]=lpile(av,tetpil,gmul2n(p1,-1));
      return y;

    case t_PADIC:
      return palog(x);

    case t_SER:
      av=avma; if (valp(x)) err(negexper,"glog");
      p1=gdiv(derivser(x),x);
      tetpil=avma; p1=integ(p1,varn(x));
      if (gcmp1((GEN)x[2])) return gerepile(av,tetpil,p1);

      p2=glog((GEN)x[2],prec); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,p2));

    case t_INTMOD:
      err(typeer,"glog");
  }
  return transc(glog,x,prec);
}

void
glogz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"glogz");
  gaffect(glog(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION SINCOS-1                         **/
/**                                                                **/
/********************************************************************/

static GEN
mpsc1(GEN x, long *ptmod8)
{
  const long mmax = 23169;
 /* on a 64-bit machine with true 128 bit/64 bit division, one could
  * take mmax=1518500248; on the alpha it does not seem worthwhile
  */
  long l,l0,l1,l2,l4,ee,i,n,m,s,t,av;
  double alpha,beta,a,b,c,d;
  GEN y,p1,p2,p3,p4,pitemp;

  if (typ(x)!=t_REAL) err(typeer,"mpsc1");
  if (!signe(x))
  {
    y=cgetr(3);
    y[1] = evalexpo((expo(x)<<1) - 1);
    y[2] = 0; *ptmod8=0; return y;
  }
  l=lg(x); y=cgetr(l); av=avma;

  l++; pitemp = mppi(l+1); setexpo(pitemp,-1);
  p1 = addrr(x,pitemp); setexpo(pitemp,0);
  if (expo(p1) >= bit_accuracy(min(l,lg(p1))) + 3)
    err(talker,"loss of precision in mpsc1");
  p3 = divrr(p1,pitemp); p2 = mpent(p3);
  if (signe(p2)) x = subrr(x, mulir(p2,pitemp));
  p1 = cgetr(l+1); affrr(x, p1);

  *ptmod8 = (signe(p1) < 0)? 4: 0;
  if (signe(p2))
  {
    long mod4 = mod4(p2);
    if (signe(p2) < 0 && mod4) mod4 = 4-mod4;
    *ptmod8 += mod4;
  }
  if (gcmp0(p1)) alpha=1000000.0;
  else
  {
    m=expo(p1); alpha=(m<-1023)? -1-m*LOG2: -1-log(fabs(rtodbl(p1)));
  }
  beta = 5 + bit_accuracy(l)*LOG2;
  a=0.5/LOG2; b=0.5*a;
  c = a+sqrt((beta+b)/LOG2);
  d = ((beta/c)-alpha-log(c))/LOG2;
  if (d>=0)
  {
    m=(long)(1+d);
    n=(long)((1+c)/2.0);
    setexpo(p1,expo(p1)-m);
  }
  else { m=0; n=(long)((1+beta/alpha)/2.0); }
  l2=l+1+(m>>TWOPOTBITS_IN_LONG);
  p2=cgetr(l2); affsr(1,p2); setlg(p2,4);
  p4=cgetr(l2); av = avma;
  affrr(mulrr(p1,p1),p4); setlg(p4,4);

  if (n>mmax)
    p3 = divrs(divrs(p4,2*n+2),2*n+1);
  else
    p3 = divrs(p4, (2*n+2)*(2*n+1));
  ee = -expo(p3); s=0;
  l4 = l1 = 3 + (ee>>TWOPOTBITS_IN_LONG);
  if (l4<=l2) { setlg(p2,l4); setlg(p4,l4); }
  for (i=n; i>mmax; i--)
  {
    p3 = divrs(divrs(p4,2*i),2*i-1); s -= expo(p3);
    t=s&(BITS_IN_LONG-1); l0=(s>>TWOPOTBITS_IN_LONG);
    if (t) l0++;
    l1 += l0; if (l1>l2) { l0 += l2-l1; l1=l2; }
    l4 += l0;
    p3 = mulrr(p3,p2);
    if (l4<=l2) { setlg(p2,l4); setlg(p4,l4); }
    subsrz(1,p3,p2); avma=av;
  }
  for (  ; i>=2; i--)
  {
    p3 = divrs(p4, 2*i*(2*i-1)); s -= expo(p3);
    t=s&(BITS_IN_LONG-1); l0=(s>>TWOPOTBITS_IN_LONG);
    if (t) l0++;
    l1 += l0; if (l1>l2) { l0 += l2-l1; l1=l2; }
    l4 += l0;
    p3 = mulrr(p3,p2);
    if (l4<=l2) { setlg(p2,l4); setlg(p4,l4); }
    subsrz(1,p3,p2); avma=av;
  }
  if (l4<=l2) { setlg(p2,l4); setlg(p4,l4); }
  setexpo(p4,expo(p4)-1); setsigne(p4, -signe(p4));
  p2 = mulrr(p4,p2);
  for (i=1; i<=m; i++)
  {
    p2 = mulrr(p2,addsr(2,p2)); setexpo(p2,expo(p2)+1);
  }
  affrr(p2,y); avma=av; return y;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION sqrt(-x*(x+2))                   **/
/**                                                                **/
/********************************************************************/

static GEN
mpaut(GEN x)
{
  long av = avma;
  GEN p1;

  cgetr(2*lg(x)+3); /* bound for 2*lg(p1)+1 */
  p1=mulrr(x,addsr(2,x)); setsigne(p1,-signe(p1));
  avma = av; return mpsqrt(p1); /* safe ! */
}

/********************************************************************/
/**                                                                **/
/**                       FONCTION COSINUS                         **/
/**                                                                **/
/********************************************************************/

static GEN
mpcos(GEN x)
{
  long mod8,av,tetpil;
  GEN y,p1;

  if (typ(x)!=t_REAL) err(typeer,"mpcos");
  if (!signe(x)) return addsr(1,x);

  av=avma; p1=mpsc1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: case 4:
      y=addsr(1,p1); break;
    case 1: case 7:
      y=mpaut(p1); setsigne(y,-signe(y)); break;
    case 2: case 6:
      y=subsr(-1,p1); break;
    case 3: case 5:
      y=mpaut(p1); break;
    default:;
  }
  return gerepile(av,tetpil,y);
}

GEN
gcos(GEN x, long prec)
{
  long av,tetpil;
  GEN r,u,v,y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      return mpcos(x);

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      r=gexp((GEN)x[2],prec); p1=ginv(r);
      p2=gmul2n(mpadd(p1,r),-1);
      p1=mpsub(p2,r);
      gsincos((GEN)x[1],&u,&v,prec);
      tetpil=avma;
      y[1]=lmul(p2,v); y[2]=lmul(p1,u);
      gerepilemanyvec(av,tetpil,y+1,2);
      return y;

    case t_SER:
      if (gcmp0(x)) return gaddsg(1,x);
      if (valp(x)<0) err(negexper,"gcos");

      av=avma; gsincos(x,&u,&v,prec); tetpil=avma;
      return gerepile(av,tetpil,gcopy(v));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gcos");
  }
  return transc(gcos,x,prec);
}

void
gcosz(GEN x, GEN y)
{
  long av = avma, prec = precision(y);

  if (!prec) err(infprecer,"gcosz");
  gaffect(gcos(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                       FONCTION SINUS                           **/
/**                                                                **/
/********************************************************************/

GEN
mpsin(GEN x)
{
  long mod8,av,tetpil;
  GEN y,p1;

  if (typ(x)!=t_REAL) err(typeer,"mpsin");
  if (!signe(x))
  {
    y=cgetr(3); y[1]=x[1]; y[2]=0;
    return y;
  }

  av=avma; p1=mpsc1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: case 6:
      y=mpaut(p1); break;
    case 1: case 5:
      y=addsr(1,p1); break;
    case 2: case 4:
      y=mpaut(p1); setsigne(y,-signe(y)); break;
    case 3: case 7:
      y=subsr(-1,p1); break;
    default:;
  }
  return gerepile(av,tetpil,y);
}

GEN
gsin(GEN x, long prec)
{
  long av,tetpil;
  GEN r,u,v,y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      return mpsin(x);

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      r=gexp((GEN)x[2],prec); p1=ginv(r);
      p2=gmul2n(mpadd(p1,r),-1);
      p1=mpsub(p2,p1);
      gsincos((GEN)x[1],&u,&v,prec);
      tetpil=avma;
      y[1]=lmul(p2,u); y[2]=lmul(p1,v);
      gerepilemanyvec(av,tetpil,y+1,2);
      return y;

    case t_SER:
      if (gcmp0(x)) return gcopy(x);
      if (valp(x)<0) err(negexper,"gsin");

      av=avma; gsincos(x,&u,&v,prec); tetpil=avma;
      return gerepile(av,tetpil,gcopy(u));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gsin");
  }
  return transc(gsin,x,prec);
}

void
gsinz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gsinz");
  gaffect(gsin(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                    PROCEDURE SINUS,COSINUS                     **/
/**                                                                **/
/********************************************************************/

void
mpsincos(GEN x, GEN *s, GEN *c)
{
  long av,tetpil,mod8;
  GEN p1, *gptr[2];

  if (typ(x)!=t_REAL) err(typeer,"mpsincos");
  if (!signe(x))
  {
    p1=cgetr(3); *s=p1; p1[1]=x[1];
    p1[2]=0; *c=addsr(1,x); return;
  }

  av=avma; p1=mpsc1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: *c=addsr( 1,p1); *s=mpaut(p1); break;
    case 1: *s=addsr( 1,p1); *c=mpaut(p1); setsigne(*c,-signe(*c)); break;
    case 2: *c=subsr(-1,p1); *s=mpaut(p1); setsigne(*s,-signe(*s)); break;
    case 3: *s=subsr(-1,p1); *c=mpaut(p1); break;
    case 4: *c=addsr( 1,p1); *s=mpaut(p1); setsigne(*s,-signe(*s)); break;
    case 5: *s=addsr( 1,p1); *c=mpaut(p1); break;
    case 6: *c=subsr(-1,p1); *s=mpaut(p1); break;
    case 7: *s=subsr(-1,p1); *c=mpaut(p1); setsigne(*c,-signe(*c)); break;
  }
  gptr[0]=s; gptr[1]=c;
  gerepilemanysp(av,tetpil,gptr,2);
}

void
gsincos(GEN x, GEN *s, GEN *c, long prec)
{
  long av,tetpil,ii,i,j,ex,ex2,lx,ly;
  GEN r,u,v,u1,v1,p1,p2,p3,p4,ps,pc;
  GEN *gptr[4];

  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      av=avma; p1=cgetr(prec); gaffect(x,p1); tetpil=avma;
      mpsincos(p1,s,c); gptr[0]=s; gptr[1]=c;
      gerepilemanysp(av,tetpil,gptr,2);
      return;

    case t_REAL:
      mpsincos(x,s,c); return;

    case t_COMPLEX:
      ps=cgetg(3,t_COMPLEX); pc=cgetg(3,t_COMPLEX);
      *s=ps; *c=pc; av=avma;
      r=gexp((GEN)x[2],prec); p1=ginv(r);
      p2=gmul2n(mpadd(p1,r),-1);
      p1=mpsub(p2,p1); r=mpsub(p2,r);
      gsincos((GEN)x[1],&u,&v,prec);
      tetpil=avma;
      p1=gmul(p2,u); p2=gmul(p1,v);
      p3=gmul(p2,v); p4=gmul(r,u);
      gptr[0]=&p1; gptr[1]=&p2; gptr[2]=&p3; gptr[3]=&p4;
      gerepilemanysp(av,tetpil,gptr,4);
      ps[1]=(long)p1; ps[2]=(long)p2; pc[1]=(long)p3; pc[2]=(long)p4;
      return;

    case t_SER:
      if (gcmp0(x)) { *c=gaddsg(1,x); *s=gcopy(x); return; }

      ex=valp(x); lx=lg(x); ex2=2*ex+2;
      if (ex < 0) err(talker,"non zero exponent in gsincos");
      if (ex2 > lx)
      {
        *s=gcopy(x); av=avma; p1=gdivgs(gsqr(x),2);
        tetpil=avma; *c=gerepile(av,tetpil,gsubsg(1,p1));
	return;
      }
      if (!ex)
      {
        av=avma; p1=gcopy(x); p1[2]=zero;
        gsincos(normalize(p1),&u,&v,prec);
        gsincos((GEN)x[2],&u1,&v1,prec);
        p1=gmul(v1,v); p2=gmul(u1,u); p3=gmul(v1,u);
        p4=gmul(u1,v); tetpil=avma;
        *c=gsub(p1,p2); *s=gadd(p3,p4);
	gptr[0]=s; gptr[1]=c;
	gerepilemanysp(av,tetpil,gptr,2);
	return;
      }

      ly=lx+2*ex;
      pc=cgetg(ly,t_SER); *c=pc;
      ps=cgetg(lx,t_SER); *s=ps;
      pc[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(x));
      pc[2]=un; ps[1]=x[1];
      for (i=2; i<ex+2; i++) ps[i]=lcopy((GEN)x[i]);
      for (i=3; i<ex2; i++) pc[i]=zero;
      for (i=ex2; i<ly; i++)
      {
	ii=i-ex; av=avma; p1=gzero;
	for (j=ex; j<ii-1; j++)
	  p1=gadd(p1,gmulgs(gmul((GEN)x[j-ex+2],(GEN)ps[ii-j]),j));
	tetpil=avma;
	pc[i]=lpile(av,tetpil,gdivgs(p1,2-i));
	if (ii<lx)
	{
	  av=avma; p1=gzero;
	  for (j=ex; j<=i-ex2; j++)
	    p1=gadd(p1,gmulgs(gmul((GEN)x[j-ex+2],(GEN)pc[i-j]),j));
	  p1=gdivgs(p1,i-2); tetpil=avma;
	  ps[i-ex]=lpile(av,tetpil,gadd(p1,(GEN)x[i-ex]));
	}
      }
      return;
  }
  err(typeer,"gsincos");
}

/********************************************************************/
/**                                                                **/
/**                FONCTIONS TANGENTE ET COTANGENTE                **/
/**                                                                **/
/********************************************************************/

static GEN
mptan(GEN x)
{
  long av=avma,tetpil;
  GEN s,c;

  mpsincos(x,&s,&c); tetpil=avma;
  return gerepile(av,tetpil,divrr(s,c));
}

GEN
gtan(GEN x, long prec)
{
  long av,tetpil;
  GEN s,c;

  switch(typ(x))
  {
    case t_REAL:
      return mptan(x);

    case t_SER:
      if (gcmp0(x)) return gcopy(x);
      if (valp(x)<0) err(negexper,"gtan"); /* fall through */
    case t_COMPLEX:
      av=avma; gsincos(x,&s,&c,prec); tetpil=avma;
      return gerepile(av,tetpil,gdiv(s,c));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gtan");
  }
  return transc(gtan,x,prec);
}

void
gtanz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gtanz");
  gaffect(gtan(x,prec),y); avma=av;
}

static GEN
mpcotan(GEN x)
{
  long av=avma,tetpil;
  GEN s,c;

  mpsincos(x,&s,&c); tetpil=avma;
  return gerepile(av,tetpil,divrr(c,s));
}

GEN
gcotan(GEN x, long prec)
{
  long av,tetpil;
  GEN s,c;

  switch(typ(x))
  {
    case t_REAL:
      return mpcotan(x);

    case t_SER: err(negexper,"gcotan"); /* fall through */
    case t_COMPLEX:
      av=avma; gsincos(x,&s,&c,prec); tetpil=avma;
      return gerepile(av,tetpil,gdiv(c,s));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gcotan");
  }
  return transc(gcotan,x,prec);
}

void
gcotanz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gcotanz");
  gaffect(gcotan(x,prec),y); avma=av;
}
