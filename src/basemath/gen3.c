/********************************************************************/
/**                                                                **/
/**                      GENERIC OPERATIONS                        **/
/**                         (third part)                           **/
/**                                                                **/
/********************************************************************/
/* $Id$ */
#include "pari.h"

/********************************************************************/
/**                                                                **/
/**                 PRINCIPAL VARIABLE NUMBER                      **/
/**                                                                **/
/********************************************************************/

int
gvar(GEN x)
{
  long tx=typ(x),i,v,w;

  if (is_polser_t(tx)) return varn(x);
  if (tx==t_POLMOD) return varn(x[1]);
  if (is_const_t(tx) || is_qf_t(tx) || tx == t_STR || tx == t_LIST)
    return BIGINT;
  v=BIGINT;
  for (i=1; i < lg(x); i++) { w=gvar((GEN)x[i]); if (w<v) v=w; }
  return v;
}

int
gvar2(GEN x)
{
  long tx=typ(x),i,v,w;

  if (is_const_t(tx) || is_qf_t(tx)) return BIGINT;
  v = BIGINT;
  switch(tx)
  {
    case t_POLMOD:
      v=gvar2((GEN)x[1]);
      w=gvar2((GEN)x[2]); if (w<v) v=w;
      return v;

    case t_SER:
      for (i=2; i < lg(x); i++) { w=gvar((GEN)x[i]); if (w<v) v=w; }
      return v;

    case t_POL:
      for (i=2; i<lgef(x); i++) { w=gvar((GEN)x[i]); if (w<v) v=w; }
      return v;
  }
  for (i=1; i<lg(x); i++) { w=gvar2((GEN)x[i]); if (w<v) v=w; }
  return v;
}

GEN
gpolvar(GEN x)
{
  if (typ(x)==t_PADIC) x = (GEN)x[2];
  else
  {
    long v=gvar(x);
    if (v==BIGINT) err(typeer,"polvar");
    x = polx[v];
  }
  return gcopy(x);
}

/*******************************************************************/
/*                                                                 */
/*                    PRECISION OF SCALAR OBJECTS                  */
/*                                                                 */
/*******************************************************************/

long
precision(GEN x)
{
  long tx=typ(x),k,l;

  if (tx==t_REAL)
  {
    k=2-(expo(x)>>TWOPOTBITS_IN_LONG);
    l=lg(x); if (l>k) k=l;
    return k;
  }
  if (tx==t_COMPLEX)
  {
    k=precision((GEN)x[1]);
    l=precision((GEN)x[2]); if (l && l<k) k=l;
    return k;
  }
  return 0;
}

long
gprecision(GEN x)
{
  long tx=typ(x),lx=lg(x),i,k,l;

  if (is_scalar_t(tx)) return precision(x);
  switch(tx)
  {
    case t_POL: lx=lgef(x);
    case t_VEC: case t_COL: case t_MAT:
      k=VERYBIGINT;
      for (i=lontyp[tx]; i<lx; i++)
      {
        l = gprecision((GEN)x[i]);
	if (l && l<k) k = l;
      }
      return (k==VERYBIGINT)? 0: k;

    case t_RFRAC: case t_RFRACN:
    {
      k=gprecision((GEN)x[1]);
      l=gprecision((GEN)x[2]); if (l && l<k) k=l;
      return k;
    }
    case t_QFR:
      return gprecision((GEN)x[4]);
  }
  return 0;
}

GEN
ggprecision(GEN x)
{
  long a=gprecision(x);
  return stoi(a ? (long) ((a-2)*pariK): VERYBIGINT);
}

GEN
precision0(GEN x, long n)
{
  if (n) return gprec(x,n);
  return ggprecision(x);
}

/* attention: precision p-adique absolue */
long
padicprec(GEN x, GEN p)
{
  long i,s,t,lx=lg(x),tx=typ(x);

  switch(tx)
  {
    case t_INT: case t_FRAC: case t_FRACN:
      return VERYBIGINT;

    case t_INTMOD:
      return ggval((GEN)x[1],p);

    case t_PADIC:
      if (!gegal((GEN)x[2],p))
	err(talker,"not the same prime in padicprec");
      return precp(x)+valp(x);

    case t_POL:
      lx=lgef(x);

    case t_COMPLEX: case t_QUAD: case t_POLMOD: case t_SER: case t_RFRAC:
    case t_RFRACN: case t_VEC: case t_COL: case t_MAT:
      for (s=VERYBIGINT, i=lontyp[tx]; i<lx; i++)
      {
        t = padicprec((GEN)x[i],p); if (t<s) s = t;
      }
      return s;
  }
  err(typeer,"padicprec");
  return 0; /* not reached */
}

/* Degre de x par rapport a la variable v si v>=0, par rapport a la variable
 * principale si v<0. On suppose x fraction rationnelle ou polynome.
 * Convention deg(0)=-1.
 */
long
poldegree(GEN x, long v)
{
  long tx=typ(x), av, w, d;

  if (is_scalar_t(tx)) return gcmp0(x)? -1: 0;
  switch(tx)
  {
    case t_POL:
      w = varn(x);
      if (v < 0 || v == w) return lgef(x)-3;
      if (v < w) return signe(x)? 0: -1;
      av = avma; x = gsubst(gsubst(x,w,polx[MAXVARN]),v,polx[0]);
      if (gvar(x)) { d = gcmp0(x)? -1: 0; } else d = lgef(x)-3;
      avma = av; return d;

    case t_RFRAC: case t_RFRACN:
      if (gcmp0((GEN)x[1])) return -1;
      return poldegree((GEN)x[1],v) - poldegree((GEN)x[2],v);
  }
  err(typeer,"degree");
  return 0; /* not reached  */
}

long
degree(GEN x)
{
  return poldegree(x,-1);
}

/* si v<0, par rapport a la variable principale, sinon par rapport a v.
 * On suppose que x est un polynome ou une serie.
 */
GEN
pollead(GEN x, long v)
{
  long l,tx = typ(x),av,tetpil,w;
  GEN xinit;

  if (is_scalar_t(tx)) return gcopy(x);
  w = varn(x);
  switch(tx)
  {
    case t_POL:
      if (v < 0 || v == w)
      {
	l=lgef(x);
	return (l==2)? gzero: gcopy((GEN)x[l-1]);
      }
      if (v < w) return gcopy(x);
      av = avma; xinit = x;
      x = gsubst(gsubst(x,w,polx[MAXVARN]),v,polx[0]);
      if (gvar(x)) { avma = av; return gcopy(xinit); }
      l = lgef(x); if (l == 2) { avma = av; return gzero; }
      tetpil = avma; x = gsubst((GEN)x[l-1],MAXVARN,polx[w]);
      return gerepile(av,tetpil,x);

    case t_SER:
      if (v < 0 || v == w) return (!signe(x))? gzero: gcopy((GEN)x[2]);
      if (v < w) return gcopy(x);
      av = avma; xinit = x;
      x = gsubst(gsubst(x,w,polx[MAXVARN]),v,polx[0]);
      if (gvar(x)) { avma = av; return gcopy(xinit);}
      if (!signe(x)) { avma = av; return gzero;}
      tetpil = avma; x = gsubst((GEN)x[2],MAXVARN,polx[w]);
      return gerepile(av,tetpil,x);
  }
  err(typeer,"pollead");
  return NULL; /* not reached */
}

/* returns 1 if there's a real component in the structure, 0 otherwise */
int
isinexactreal(GEN x)
{
  long tx=typ(x),lx,i;

  if (is_scalar_t(tx))
  {
    switch(tx)
    {
      case t_REAL:
        return 1;

      case t_COMPLEX: case t_QUAD:
        return (typ(x[1])==t_REAL || typ(x[2])==t_REAL);
    }
    return 0;
  }
  switch(tx)
  {
    case t_QFR: case t_QFI:
      return 0;

    case t_RFRAC: case t_RFRACN:
      return isinexactreal((GEN)x[1]) || isinexactreal((GEN)x[2]);
  }
  lx = (tx==t_POL)? lgef(x): lg(x);
  for (i=lontyp[tx]; i<lx; i++)
    if (isinexactreal((GEN)x[i])) return 1;
  return 0;
}

int
isexactzero(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_INT:
      return !signe(g);
    case t_REAL: case t_PADIC: case t_SER:
      return 0;
    case t_INTMOD: case t_POLMOD:
      return isexactzero((GEN)g[2]);
    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      return isexactzero((GEN)g[1]);
    case t_COMPLEX:
      return isexactzero((GEN)g[1]) && isexactzero((GEN)g[2]);
    case t_QUAD:
      return isexactzero((GEN)g[2]) && isexactzero((GEN)g[3]);

    case t_POL:
      for (i=lgef(g)-1; i>1; i--)
        if (!isexactzero((GEN)g[i])) return 0;
      return 1;
    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(g)-1; i; i--)
	if (!isexactzero((GEN)g[i])) return 0;
      return 1;
  }
  return 0;
}

int
iscomplex(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return 0;
    case t_COMPLEX:
      return !gcmp0((GEN)x[2]);
    case t_QUAD:
      return signe(mael(x,1,2)) > 0;
  }
  err(typeer,"iscomplex");
  return 0; /* not reached */
}

int
ismonome(GEN x)
{
  long i;
  if (typ(x)!=t_POL || !signe(x)) return 0;
  for (i=lgef(x)-2; i>1; i--)
    if (!isexactzero((GEN)x[i])) return 0;
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                     MULTIPLICATION SIMPLE                      **/
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

GEN
gmulsg(long s, GEN y)
{
  long ty=typ(y),ly=lg(y),i,av,tetpil;
  GEN z,p1,p2;

  switch(ty)
  {
    case t_INT:
      return mulsi(s,y);

    case t_REAL:
      return mulsr(s,y);

    case t_INTMOD: z=cgetg(3,t_INTMOD); p2=(GEN)y[1];
      (void)new_chunk(lgefint(p2)<<2);
      p1=mulsi(s,(GEN)y[2]); avma=(long)z;
      z[2]=lmodii(p1,p2); icopyifstack(p2,z[1]); return z;

    case t_FRAC:
      if (!s) return gzero;
      z = cgetg(3,t_FRAC);
      i = cgcd(s, smodis((GEN)y[2], s));
      if (i == 1)
      {
        z[2] = licopy((GEN)y[2]);
        z[1] = lmulis((GEN)y[1], s);
      }
      else
      {
        z[2] = ldivis((GEN)y[2], i);
        z[1] = lmulis((GEN)y[1], s/i);
        fix_frac_if_int(z);
      }
      return z;

    case t_FRACN: z=cgetg(3,ty);
      z[1]=lmulsi(s,(GEN)y[1]);
      z[2]=licopy((GEN)y[2]);
      return z;

    case t_COMPLEX: z=cgetg(ly,ty);
      z[1]=lmulsg(s,(GEN)y[1]);
      z[2]=lmulsg(s,(GEN)y[2]); return z;

    case t_PADIC:
      if (!s) return gzero;
      av=avma; p1=cgetp(y); gaffsg(s,p1); tetpil=avma;
      return gerepile(av,tetpil,gmul(p1,y));

    case t_QUAD: z=cgetg(ly,ty);
      copyifstack(y[1],z[1]);
      z[2]=lmulsg(s,(GEN)y[2]);
      z[3]=lmulsg(s,(GEN)y[3]); return z;

    case t_POLMOD: z=cgetg(ly,ty);
      z[2]=lmulsg(s,(GEN)y[2]);
      copyifstack(y[1],z[1]); return z;

    case t_POL:
      if (!s || !signe(y)) return zeropol(varn(y));
      ly=lgef(y); z=cgetg(ly,t_POL); z[1]=y[1];
      for (i=2; i<ly; i++) z[i]=lmulsg(s,(GEN)y[i]);
      return normalizepol_i(z, ly);

    case t_SER:
      if (!s) return zeropol(varn(y));
      if (gcmp0(y)) return gcopy(y);
      z=cgetg(ly,ty);
      for (i=2; i<ly; i++) z[i]=lmulsg(s,(GEN)y[i]);
      z[1]=y[1]; return normalize(z);

    case t_RFRAC:
      if (!s) return zeropol(gvar(y));
      z = cgetg(3, t_RFRAC);
      i = ggcd(stoi(s),(GEN)y[2])[2];
      avma = (long)z;
      if (i == 1)
      {
        z[1]=lmulgs((GEN)y[1], s);
        z[2]= lcopy((GEN)y[2]);
      }
      else
      {
        z[1] = lmulgs((GEN)y[1], s/i);
        z[2] = ldivgs((GEN)y[2], i);
      }
      return z;

    case t_RFRACN:
      if (!s) return zeropol(gvar(y));
      z=cgetg(ly,t_RFRACN);
      z[1]=lmulsg(s,(GEN)y[1]);
      z[2]=lcopy((GEN)y[2]); return z;

    case t_VEC: case t_COL: case t_MAT:
      z=cgetg(ly,ty);
      for (i=1; i<ly; i++) z[i]=lmulsg(s,(GEN)y[i]);
      return z;
  }
  err(typeer,"gmulsg");
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                       DIVISION SIMPLE                          **/
/**                                                                **/
/********************************************************************/

GEN
gdivgs(GEN x, long s)
{
  static long court[] = { evaltyp(t_INT) | m_evallg(3),0,0 };
  long tx=typ(x),lx=lg(x),i,av;
  GEN z,p1;

  if (!s) err(gdiver2);
  switch(tx)
  {
    case t_INT:
      av=avma; z=dvmdis(x,s,&p1);
      if (p1==gzero) return z;

      i = cgcd(s, smodis(x,s));
      avma=av; z=cgetg(3,t_FRAC);
      if (i == 1)
        x = icopy(x);
      else
      {
        s /= i;
        x = divis(x, i);
      }
      z[1]=(long)x; z[2]=lstoi(s);
      fix_frac(z); return z;

    case t_REAL:
      return divrs(x,s);

    case t_FRAC: z=cgetg(3,tx);
      i = cgcd(s, smodis((GEN)x[1], s));
      if (i == 1)
      {
        z[2] = lmulsi(s, (GEN)x[2]);
        z[1] = licopy((GEN)x[1]);
      }
      else
      {
        z[2] = lmulsi(s/i, (GEN)x[2]);
        z[1] = ldivis((GEN)x[1], i);
      }
      fix_frac(z);
      fix_frac_if_int(z); return z;

    case t_FRACN: z = cgetg(3,tx);
      z[1]=licopy((GEN)x[1]);
      z[2]=lmulsi(s,(GEN)x[2]);
      fix_frac(z); return z;

    case t_COMPLEX: z=cgetg(lx,tx);
      z[1]=ldivgs((GEN)x[1],s);
      z[2]=ldivgs((GEN)x[2],s);
      return z;

    case t_QUAD: z=cgetg(lx,tx);
      copyifstack(x[1],z[1]);
      for (i=2; i<4; i++) z[i]=ldivgs((GEN)x[i],s);
      return z;

    case t_POLMOD: z=cgetg(lx,tx);
      copyifstack(x[1],z[1]);
      z[2]=ldivgs((GEN)x[2],s);
      return z;

    case t_POL: lx=lgef(x); z=cgetg(lx,tx);
      for (i=2; i<lx; i++) z[i]=ldivgs((GEN)x[i],s);
      z[1]=x[1]; return z;

    case t_SER: z=cgetg(lx,tx);
      for (i=2; i<lx; i++) z[i]=ldivgs((GEN)x[i],s);
      z[1]=x[1]; return z;

    case t_RFRAC:
      z = cgetg(3, t_RFRAC);
      i = ggcd(stoi(s),(GEN)x[1])[2];
      avma = (long)z;
      if (i == 1)
      {
        z[2]=lmulsg(s,(GEN)x[2]);
        z[1]=lcopy((GEN)x[1]); return z;
      }
      z[1] = ldivgs((GEN)x[1], i);
      z[2] = lmulgs((GEN)x[2], s/i); return z;

    case t_RFRACN: z=cgetg(3,t_RFRACN);
      z[2]=lmulsg(s,(GEN)x[2]);
      z[1]=lcopy((GEN)x[1]); return z;

    case t_VEC: case t_COL: case t_MAT: z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=ldivgs((GEN)x[i],s);
      return z;
  }
  affsi(s,court); return gdiv(x,court);
}

/*******************************************************************/
/*                                                                 */
/*                    MODULO GENERAL                               */
/*                                                                 */
/*******************************************************************/

GEN
gmod(GEN x, GEN y)
{
  long av,tetpil,i, tx=typ(x);
  GEN z,p1;

  if (is_matvec_t(tx))
  {
    i=lg(x); z=cgetg(i,tx);
    for (i--; i; i--) z[i]=lmod((GEN)x[i],y);
    return z;
  }
  switch(typ(y))
  {
    case t_INT:
      switch(tx)
      {
	case t_INT:
	  return modii(x,y);

	case t_INTMOD: z=cgetg(3,tx);
          z[1]=lmppgcd((GEN)x[1],y);
	  z[2]=lmodii((GEN)x[2],(GEN)z[1]); return z;

	case t_FRAC: case t_FRACN:
	  av=avma; if (tx==t_FRACN) x=gred(x);
	  p1=mulii((GEN)x[1],mpinvmod((GEN)x[2],y));
	  tetpil=avma; return gerepile(av,tetpil,modii(p1,y));

	case t_QUAD: z=cgetg(4,tx);
          copyifstack(x[1],z[1]);
	  z[2]=lmod((GEN)x[2],y);
          z[3]=lmod((GEN)x[3],y); return z;

	case t_PADIC:
        {
          long p1[] = {evaltyp(t_INTMOD)|m_evallg(3),0,0};
          p1[1] = (long)y;
          p1[2] = lgeti(lgefint(y));
          gaffect(x,p1); return (GEN)p1[2];
        }
	case t_POLMOD: case t_POL:
	  return gzero;

	default: err(gmoder1);
      }

    case t_REAL: case t_FRAC: case t_FRACN:
      switch(tx)
      {
	case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
	  av=avma; p1 = gfloor(gdiv(x,y)); p1 = gneg_i(gmul(p1,y));
          tetpil=avma; return gerepile(av,tetpil,gadd(x,p1));

	case t_POLMOD: case t_POL:
	  return gzero;

	default: err(gmoder1);
      }

    case t_POL:
      if (is_scalar_t(tx))
      {
        if (tx!=t_POLMOD || varn(x[1]) > varn(y))
          return (lgef(y) < 4)? gzero: gcopy(x);
	if (varn(x[1])!=varn(y)) return gzero;
        z=cgetg(3,t_POLMOD);
        z[1]=lgcd((GEN)x[1],y);
        z[2]=lres((GEN)x[2],(GEN)z[1]); return z;
      }
      switch(tx)
      {
	case t_POL:
	  return gres(x,y);

	case t_RFRAC: case t_RFRACN:
	  av=avma; if (tx==t_RFRACN) x=gred_rfrac(x);
	  p1=gmul((GEN)x[1],ginvmod((GEN)x[2],y)); tetpil=avma;
          return gerepile(av,tetpil,gres(p1,y));

	default: err(talker,"type mod polynomial forbidden in gmod");
      }
  }
  err(talker,"modulus type forbidden in gmod");
  return NULL; /* not reached */
}

GEN
gmodulsg(long x, GEN y)
{
  GEN z;

  switch(typ(y))
  {
    case t_INT: z=cgetg(3,t_INTMOD);
      z[1]=labsi(y); z[2]=lmodsi(x,y); return z;

    case t_POL: z=cgetg(3,t_POLMOD);
      z[1]=lcopy(y); z[2]=lstoi(x); return z;
  }
  err(gmoder1); return NULL; /* not reached */
}

GEN
gmodulss(long x, long y)
{
  GEN z=cgetg(3,t_INTMOD);

  y=labs(y); z[1]=lstoi(y); z[2]=lstoi(x % y); return z;
}

GEN
gmodulo(GEN x,GEN y)
{
  long tx=typ(x),l,i;
  GEN z;

  if (is_matvec_t(tx))
  {
    l=lg(x); z=cgetg(l,tx);
    for (i=1; i<l; i++) z[i] = (long) gmodulo((GEN)x[i],y);
    return z;
  }
  switch(typ(y))
  {
    case t_INT:
      if (tx!=t_INT && !is_frac_t(tx) && tx!=t_PADIC) break;
      z=cgetg(3,t_INTMOD);
      if (!signe(y)) err(talker,"zero modulus in gmodulo");
      y = gclone(y); setsigne(y,1);
      z[1]=(long)y;
      z[2]=lmod(x,y); return z;

    case t_POL: z=cgetg(3,t_POLMOD);
      z[1] = lclone(y);
      if (is_scalar_t(tx)) { z[2]=lcopy(x); return z; }
      if (tx==t_POL || is_rfrac_t(tx)) { z[2]=lmod(x,y); return z; }
  }
  err(gmoder1); return NULL; /* not reached */
}


GEN
gmodulcp(GEN x,GEN y)
{
  long tx=typ(x),l,i;
  GEN z;

  if (is_matvec_t(tx))
  {
    l=lg(x); z=cgetg(l,tx);
    for (i=1; i<l; i++) z[i] = lmodulcp((GEN)x[i],y);
    return z;
  }
  switch(typ(y))
  {
    case t_INT:
      if (tx!=t_INT && !is_frac_t(tx) && tx!=t_PADIC) break;
      z=cgetg(3,t_INTMOD);
      z[1]=labsi(y);
      z[2]=lmod(x,y); return z;

    case t_POL: z=cgetg(3,t_POLMOD);
      z[1]=lcopy(y);
      if (is_scalar_t(tx)) { z[2]=lcopy(x); return z; }
      if (tx==t_POL || is_rfrac_t(tx)) { z[2]=lmod(x,y); return z; }
  }
  err(gmoder1); return NULL; /* not reached */
}

GEN
Mod0(GEN x,GEN y,long flag)
{
  switch(flag)
  {
    case 0: return gmodulcp(x,y);
    case 1: return gmodulo(x,y);
    default: err(flagerr,"Mod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                 DIVISION ENTIERE GENERALE                       */
/*            DIVISION ENTIERE AVEC RESTE GENERALE                 */
/*                                                                 */
/*******************************************************************/

GEN
gdivent(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y);

  if (tx == t_INT)
  {
    if (ty == t_INT)
    {
      GEN z,p1;
      long av,tetpil;

      if (signe(x)>=0) return divii(x,y);
      av=avma; z=dvmdii(x,y,&p1);
      if (p1==gzero) return z;
      tetpil=avma; return gerepile(av,tetpil,addsi(-signe(y),z));
    }
    if (ty!=t_POL) err(typeer,"gdivent");
    return gzero;
  }
  if (ty != t_POL) err(typeer,"gdivent");
  if (tx == t_POL) return gdeuc(x,y);
  if (! is_scalar_t(tx)) err(typeer,"gdivent");
  return gzero;
}

GEN
gdiventres(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y);
  GEN z = cgetg(3,t_COL);

  if (tx==t_INT)
  {
    if (ty==t_INT) z[1]=(long)truedvmdii(x,y,(GEN*)(z+2));
    else
    {
      if (ty!=t_POL) err(typeer,"gdiventres");
      z[1]=zero; z[2]=licopy(x);
    }
    return z;
  }
  if (ty != t_POL) err(typeer,"gdiventres");
  if (tx == t_POL)
  {
    z[1]=ldivres(x,y,(GEN *)(z+2));
    return z;
  }
  if (! is_scalar_t(tx)) err(typeer,"gdiventres");
  z[1]=zero; z[2]=lcopy(x); return z;
}

GEN
gdivmod(GEN x, GEN y, GEN *pr)
{
  long ty,tx=typ(x);

  if (tx==t_INT)
  {
    ty=typ(y);
    if (ty==t_INT) return dvmdii(x,y,pr);
    if (ty==t_POL) { *pr=gcopy(x); return gzero; }
    err(typeer,"gdivmod");
  }
  if (tx!=t_POL) err(typeer,"gdivmod");
  return poldivres(x,y,pr);
}

/* When x and y are integers, compute the quotient x/y, rounded to the
 * nearest integer. If there is a tie, the quotient is rounded towards zero.
 * If x and y are not both integers, same as gdivent.
 */
GEN
gdivround(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y);

  if (tx==t_INT)
  {
    if (ty==t_INT)
    {
      long av = avma, av1,fl;
      GEN r, q=dvmdii(x,y,&r); /* q = x/y rounded towards 0, sqn(r)=sgn(x) */

      if (r==gzero) return q;
      av1 = avma;
      fl = absi_cmp(shifti(r,1),y);
      avma = av1; cgiv(r);
      if (fl >= 0) /* If 2*|r| >= |y| */
      {
        long sz = signe(x)*signe(y);
	if (fl || sz > 0)
          { av1=avma; q = gerepile(av,av1,addis(q,sz)); }
      }
      return q;
    }
    if (ty!=t_POL) err(typeer,"gdivround");
    return gzero;
  }
  if (ty != t_POL) err(typeer,"gdivround");
  if (tx == t_POL) return gdeuc(x,y);
  if (! is_scalar_t(tx)) err(typeer,"gdivround");
  return gzero;
}

/*******************************************************************/
/*                                                                 */
/*                       SHIFT D'UN GEN                            */
/*                                                                 */
/*******************************************************************/

/* Shift tronque si n<0 (multiplication tronquee par 2^n)  */
GEN
gshift(GEN x, long n)
{
  long i,l,lx, tx = typ(x);
  GEN y;

  switch(tx)
  {
    case t_INT:
      return shifti(x,n);
    case t_REAL:
      return shiftr(x,n);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx); l=lontyp[tx];
      for (i=1; i<l ; i++) y[i]=x[i];
      for (   ; i<lx; i++) y[i]=lshift((GEN)x[i],n);
      return y;
  }
  return gmul2n(x,n);
}

GEN mulscalrfrac(GEN x, GEN y);

/* Shift vrai (multiplication exacte par 2^n) */
GEN
gmul2n(GEN x, long n)
{
  long tx,lx,i,k,l,av,tetpil;
  GEN p2,p1,y;

  tx=typ(x);
  switch(tx)
  {
    case t_INT:
      if (n>=0) return shifti(x,n);
      if (!signe(x)) return gzero;
      l = vali(x); n = -n;
      if (n<=l) return shifti(x,-n);
      y=cgetg(3,t_FRAC);
      y[1]=lshifti(x,-l);
      y[2]=lshifti(gun,n-l); return y;
	
    case t_REAL:
      return shiftr(x,n);

    case t_INTMOD:
      if (n > 0)
      {
        y=cgetg(3,t_INTMOD); p2=(GEN)x[1];
        av=avma; new_chunk(lgefint(p2) * (3 + (n>>TWOPOTBITS_IN_LONG)));
        p1 = shifti((GEN)x[2],n); avma=av;
        y[2]=lmodii(p1,p2); icopyifstack(p2,y[1]); return y;
      }
      l=avma; y=gmul2n(gun,n); tetpil=avma;
      return gerepile(l,tetpil,gmul(y,x));

    case t_FRAC: case t_FRACN:
      l = vali((GEN)x[1]);
      k = vali((GEN)x[2]);
      if (n+l-k>=0)
      {
        if (expi((GEN)x[2]) == k) /* x[2] power of 2 */
          return shifti((GEN)x[1],n-k);
        l = n-k; k = -k;
      }
      else
      {
        k = -l-n; l = -l;
      }
      y=cgetg(3,t_FRAC);
      y[1]=lshifti((GEN)x[1],l);
      y[2]=lshifti((GEN)x[2],k); return y;

    case t_QUAD: y=cgetg(4,t_QUAD);
      copyifstack(x[1],y[1]);
      for (i=2; i<4; i++) y[i]=lmul2n((GEN)x[i],n);
      return y;

    case t_POLMOD: y=cgetg(3,t_POLMOD);
      copyifstack(x[1],y[1]);
      y[2]=lmul2n((GEN)x[2],n); return y;

    case t_POL: case t_COMPLEX: case t_SER:
    case t_VEC: case t_COL: case t_MAT:
      lx = (tx==t_POL)? lgef(x): lg(x);
      y=cgetg(lx,tx); l=lontyp[tx];
      for (i=1; i<l ; i++) y[i]=x[i];
      for (   ; i<lx; i++) y[i]=lmul2n((GEN)x[i],n);
      return y;

    case t_RFRAC: av=avma; p1 = gmul2n(gun,n); tetpil = avma;
      return gerepile(av,tetpil, mulscalrfrac(p1,x));

    case t_RFRACN: y=cgetg(3,tx);
      if (n>=0)
      {
        y[1]=lmul2n((GEN)x[1],n);  y[2]=lcopy((GEN)x[2]);
      }
      else
      {
        y[2]=lmul2n((GEN)x[2],-n); y[1]=lcopy((GEN)x[1]);
      }
      return y;

    case t_PADIC:
      l=avma; y=gmul2n(gun,n); tetpil=avma;
      return gerepile(l,tetpil,gmul(y,x));
  }
  err(typeer,"gmul2n");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                      INVERSE D'UN GEN                           */
/*                                                                 */
/*******************************************************************/
GEN fix_rfrac_if_pol(GEN x, GEN y);

GEN
ginv(GEN x)
{
  long tx=typ(x),av,tetpil,s;
  GEN z,y,p1,p2;

  switch(tx)
  {
    case t_INT:
      if (is_pm1(x)) return icopy(x);
      if (!signe(x)) err(gdiver2);
      z=cgetg(3,t_FRAC);
      z[1] = (signe(x)<0)? lnegi(gun): un;
      z[2]=labsi(x); return z;

    case t_REAL:
      return divsr(1,x);

    case t_INTMOD: z=cgetg(3,t_INTMOD);
      icopyifstack(x[1],z[1]);
      z[2]=lmpinvmod((GEN)x[2],(GEN)x[1]); return z;

    case t_FRAC: case t_FRACN: z=cgetg(3,tx);
      s = signe(x[1]);
      if (!s) err(gdiver2);
      if (is_pm1(x[1]))
        return s>0? icopy((GEN)x[2]): negi((GEN)x[2]);
      z[1]=licopy((GEN)x[2]);
      z[2]=licopy((GEN)x[1]);
      if (s < 0)
      {
	setsigne(z[1],-signe(z[1]));
	setsigne(z[2],1);
      }
      return z;

    case t_COMPLEX: case t_QUAD:
      av=avma; p1=gnorm(x); p2=gconj(x); tetpil=avma;
      return gerepile(av,tetpil,gdiv(p2,p1));

    case t_PADIC: z = cgetg(5,t_PADIC);
      if (!signe(x[4])) err(gdiver2);
      z[1] = evalprecp(precp(x)) | evalvalp(-valp(x));
      icopyifstack(x[2], z[2]);
      z[3] = licopy((GEN)x[3]);
      z[4] = lmpinvmod((GEN)x[4],(GEN)z[3]); return z;

    case t_POLMOD: z=cgetg(3,t_POLMOD);
      copyifstack(x[1],z[1]);
      z[2]=linvmod((GEN)x[2],(GEN)x[1]); return z;

    case t_POL: case t_SER:
      return gdiv(gun,x);

    case t_RFRAC: case t_RFRACN:
      if (gcmp0((GEN) x[1])) err(gdiver2);
      p1 = fix_rfrac_if_pol((GEN)x[2],(GEN)x[1]);
      if (p1) return p1;
      z=cgetg(3,tx);
      z[1]=lcopy((GEN)x[2]);
      z[2]=lcopy((GEN)x[1]); return z;

    case t_QFR:
    {
      long k,l;
      l=signe(x[2]); setsigne(x[2],-l);
      k=signe(x[4]); setsigne(x[4],-k); z=redreal(x);
      setsigne(x[2],l); setsigne(x[4],k); return z;
    }
    case t_QFI:
      y=gcopy(x);
      if (!egalii((GEN)x[1],(GEN)x[2]) && !egalii((GEN)x[1],(GEN)x[3]))
	setsigne(y[2],-signe(y[2]));
      return y;
    case t_MAT:
      return (lg(x)==1)? cgetg(1,t_MAT): invmat(x);
  }
  err(typeer,"inverse");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*           SUBSTITUTION DANS UN POLYNOME OU UNE SERIE            */
/*                                                                 */
/*******************************************************************/

/* Convert t_SER --> t_POL / t_RFRAC */
static GEN
gconvsp(GEN x, int flpile)
{
  long v = varn(x), av,tetpil,i;
  GEN p1,y;

  if (gcmp0(x)) return zeropol(v);
  av=avma; y=dummycopy(x); settyp(y,t_POL);
  i=lg(x)-1; while (i>1 && gcmp0((GEN)y[i])) i--;
  setlgef(y,i+1);
  p1=gpuigs(polx[v],valp(x));
  tetpil=avma; p1=gmul(p1,y);
  return flpile? gerepile(av,tetpil,p1): p1;
}

GEN
gsubst(GEN x, long v, GEN y)
{
  long tx = typ(x), ty = typ(y), lx = lg(x), ly = lg(y);
  long l,vx,vy,e,ex,ey,tetpil,av,i,j,k,jb,limite;
  GEN t,p1,p2,z;

  if (ty==t_MAT)
  {
    if (ly==1) return cgetg(1,t_MAT);
    if (ly != lg(y[1]))
      err(talker,"forbidden substitution by a non square matrix");
  } else if (is_graphicvec_t(ty))
    err(talker,"forbidden substitution by a vector");

  if (is_scalar_t(tx))
  {
    if (tx!=t_POLMOD || v <= varn(x[1]))
    {
      if (ty==t_MAT) return gscalmat(x,ly-1);
      return gcopy(x);
    }
    av=avma;
    p1=gsubst((GEN)x[1],v,y); vx=varn(p1);
    p2=gsubst((GEN)x[2],v,y); vy=gvar(p2);
    if (typ(p1)!=t_POL)
      err(talker,"forbidden substitution in a scalar type");
    if (vy>=vx)
    {
      tetpil=avma;
      return gerepile(av,tetpil,gmodulcp(p2,p1));
    }
    lx=lgef(p2); tetpil=avma; z=cgetg(lx,t_POL); z[1]=p2[1];
    for (i=2; i<lx; i++) z[i]=lmodulcp((GEN)p2[i],p1);
    return gerepile(av,tetpil, normalizepol_i(z,lx));
  }

  switch(tx)
  {
    case t_POL:
      l=lgef(x);
      if (l==2)
        return (ty==t_MAT)? gscalmat(gzero,ly-1): gzero;

      vx=varn(x);
      if (vx<v)
      {
	av=avma; p1=polx[vx]; z= gsubst((GEN)x[l-1],v,y);
	for (i=l-1; i>2; i--) z=gadd(gmul(z,p1),gsubst((GEN)x[i-1],v,y));
	return gerepileupto(av,z);
      }
      if (ty!=t_MAT)
        return (vx>v)? gcopy(x): poleval(x,y);

      if (vx>v) return gscalmat(x,ly-1);
      if (l==3) return gscalmat((GEN)x[2],ly-1);
      av=avma; z=(GEN)x[l-1];
      for (i=l-1; i>2; i--) z=gaddmat((GEN)x[i-1],gmul(z,y));
      return gerepileupto(av,z);

    case t_SER:
      vx=varn(x);
      if (vx > v)
        return (ty==t_MAT)? gscalmat(x,ly-1): gcopy(x);
      ex = valp(x);
      if (vx < v)
      {
        if (!signe(x)) return gcopy(x);
        /* a ameliorer */
        av=avma; setvalp(x,0); p1=gconvsp(x,0); setvalp(x,ex);
        p2=gsubst(p1,v,y); tetpil=avma; z=tayl(p2,vx,lx-2);
        if (ex)
        {
          p1=gpuigs(polx[vx],ex); tetpil=avma; z=gmul(z,p1);
        }
        return gerepile(av,tetpil,z);
      }
      switch(ty) /* here vx == v */
      {
        case t_SER:
	  ey=valp(y); vy=varn(y);
	  if (ey<1) return zeroser(vy,ey*(ex+lx-2));
	  l=(lx-2)*ey+2;
	  if (ex) { if (l>ly) l=ly; }
	  else
	  {
	    if (gcmp0(y)) l=ey+2;
	    else { if (l>ly) l=ey+ly; }
	  }
	  if (vy!=vx)
	  {
	    av=avma; z = zeroser(vy,0);
	    for (i=lx-1; i>=2; i--)
              z = gadd((GEN)x[i], gmul(y,z));
	    if (ex) z = gmul(z, gpuigs(y,ex));
	    return gerepileupto(av,z);
	  }

	  av=avma; limite=stack_lim(av,1);
          t=cgetg(ly,t_SER);
          z = scalarser((GEN)x[2],varn(y),l-2);
	  for (i=2; i<ly; i++) t[i]=y[i];
	
	  for (i=3,jb=ey; jb<=l-2; i++,jb+=ey)
	  {
	    for (j=jb+2; j<l; j++)
	    {
	      p1=gmul((GEN)x[i],(GEN)t[j-jb]);
	      z[j]=ladd((GEN)z[j],p1);
	    }
	    for (j=l-1-jb-ey; j>1; j--)
	    {
	      p1=gzero;
	      for (k=2; k<j; k++)
		p1=gadd(p1,gmul((GEN)t[j-k+2],(GEN)y[k]));
	      p2=gmul((GEN)t[2],(GEN)y[j]);
	      t[j]=ladd(p1,p2);
	    }
            if (low_stack(limite, stack_lim(av,1)))
	    {
	      GEN *gptr[2];
	      if(DEBUGMEM>1) err(warnmem,"gsubst");
	      gptr[0]=&z; gptr[1]=&t; gerepilemany(av,gptr,2);
	    }
	  }
	  if (!ex) { tetpil=avma; return gerepile(av,tetpil,gcopy(z)); }

          if (l<ly) { setlg(y,l); p1=gpuigs(y,ex); setlg(y,ly); }
          else p1=gpuigs(y,ex);
          tetpil=avma; return gerepile(av,tetpil,gmul(z,p1));

        case t_POL: case t_RFRAC: case t_RFRACN:
          if (isexactzero(y)) return scalarser((GEN)x[2],v,lx-2);
          vy=gvar(y); e=gval(y,vy);
          if (e<=0)
            err(talker,"non positive valuation in a series substitution");
	  av=avma; p1=gconvsp(x,0); p2=gsubst(p1,v,y); tetpil=avma;
	  return gerepile(av,tetpil,tayl(p2,vy,e*(lx-2+ex)));

        default:
          err(talker,"non polynomial or series type substituted in a series");
      }
      break;

    case t_RFRAC: case t_RFRACN: av=avma;
      p1=gsubst((GEN)x[1],v,y);
      p2=gsubst((GEN)x[2],v,y); tetpil=avma;
      return gerepile(av,tetpil,gdiv(p1,p2));

    case t_VEC: case t_COL: case t_MAT: z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=lsubst((GEN)x[i],v,y);
  }
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                SERIE RECIPROQUE D'UNE SERIE                     */
/*                                                                 */
/*******************************************************************/

GEN
recip(GEN x)
{
  long tetpil, av=avma, v=varn(x);
  GEN p1,p2,a,y,u;

  if (typ(x)!=t_SER) err(talker,"not a series in serreverse");
  if (valp(x)!=1) err(talker,"valuation not equal to 1 in serreverse");

  a=(GEN)x[2];
  if (gcmp1(a))
  {
    long i,j,k, lx=lg(x), lim=stack_lim(av,2);

    u=cgetg(lx,t_SER); y=cgetg(lx,t_SER);
    u[1]=y[1]=evalsigne(1) | evalvalp(1) | evalvarn(v);
    u[2]=un; u[3]=lmulsg(-2,(GEN)x[3]);
    y[2]=un; y[3]=lneg((GEN)x[3]);
    for (i=3; i<lx-1; )
    {
      for (j=3; j<i+1; j++)
      {
        p1=(GEN)u[j];
        for (k=j-1; k>2; k--)
          p1=gsub(p1,gmul((GEN)u[k],(GEN)x[j-k+2]));
        u[j]=lsub(p1,(GEN)x[j]);
      }
      p1=gmulsg(i,(GEN)x[i+1]);
      for (k=2; k<i; k++)
      {
        p2=gmul((GEN)x[k+1],(GEN)u[i-k+2]);
        p1=gadd(p1,gmulsg(k,p2));
      }
      i++; u[i]=lneg(p1); y[i]=ldivgs((GEN)u[i],i-1);
      if (low_stack(lim, stack_lim(av,2)))
      {
	GEN *gptr[2];
	if(DEBUGMEM>1) err(warnmem,"recip");
	for(k=i+1; k<lx; k++) u[k]=y[k]=zero; /* dummy */
	gptr[0]=&u; gptr[1]=&y; gerepilemany(av,gptr,2);
      }
    }
    tetpil=avma; return gerepile(av,tetpil,gcopy(y));
  }
  y=gdiv(x,a); y[2]=un; y=recip(y);
  a=gdiv(polx[v],a); tetpil=avma;
  return gerepile(av,tetpil,gsubst(y,v,a));
}

/*******************************************************************/
/*                                                                 */
/*                    DERIVATION ET INTEGRATION                    */
/*                                                                 */
/*******************************************************************/
GEN
derivpol(GEN x)
{
  long i,lx = lgef(x)-1;
  GEN y;

  if (lx<3) return gzero;
  y = cgetg(lx,t_POL);
  for (i=2; i<lx ; i++) y[i] = lmulsg(i-1,(GEN)x[i+1]);
  y[1] = x[1]; return normalizepol_i(y,i);
}

GEN
derivser(GEN x)
{
  long i,j,vx = varn(x), e = valp(x), lx = lg(x);
  GEN y;
  if (gcmp0(x)) return zeroser(vx,e-1);
  if (e)
  {
    y=cgetg(lx,t_SER); y[1] = evalsigne(1) | evalvalp(e-1) | evalvarn(vx);
    for (i=2; i<lx; i++) y[i]=lmulsg(i+e-2,(GEN)x[i]);
    return y;
  }
  i=3; while (i<lx && gcmp0((GEN)x[i])) i++;
  if (i==lx) return zeroser(vx,lx-3);
  lx--; if (lx<3) lx=3;
  lx = lx-i+3; y=cgetg(lx,t_SER);
  y[1]=evalsigne(1) | evalvalp(i-3) | evalvarn(vx);
  for (j=2; j<lx; j++) y[j]=lmulsg(j+i-4,(GEN)x[i+j-2]);
  return y;
}

GEN
deriv(GEN x, long v)
{
  long lx,vx,tx,e,i,j,l,av,tetpil;
  GEN y,p1,p2;

  tx=typ(x); if (is_const_t(tx)) return gzero;
  if (v < 0) v = gvar(x);
  switch(tx)
  {
    case t_POLMOD:
      if (v<=varn(x[1])) return gzero;
      y=cgetg(3,t_POLMOD); copyifstack(x[1],y[1]);
      y[2]=lderiv((GEN)x[2],v); return y;

    case t_POL:
      vx=varn(x); if (vx>v) return gzero;
      if (vx<v)
      {
        lx = lgef(x);
        y = cgetg(lx,t_POL);
        for (i=2; i<lx; i++) y[i] = lderiv((GEN)x[i],v);
        y[1] = evalvarn(vx);
        return normalizepol_i(y,i);
      }
      return derivpol(x);

    case t_SER:
      vx=varn(x); if (vx>v) return gzero;
      if (vx<v)
      {
        if (!signe(x)) return gcopy(x);
        lx=lg(x); e=valp(x);
	l=avma;
	for (i=2; i<lx; i++)
        {
          if (!gcmp0(deriv((GEN)x[i],v))) break;
          avma=l;
        }
	if (i==lx) return ggrando(polx[vx],e+lx-2);
	y=cgetg(lx-i+2,t_SER);
        y[1] = evalsigne(1) | evalvalp(e+i-2) | evalvarn(vx);
	for (j=2; i<lx; j++,i++) y[j]=lderiv((GEN)x[i],v);
        return y;
      }
      return derivser(x);

    case t_RFRAC: case t_RFRACN: av=avma; y=cgetg(3,tx);
      y[2]=lsqr((GEN)x[2]); l=avma;
      p1=gmul((GEN)x[2],deriv((GEN)x[1],v));
      p2=gmul(gneg_i((GEN)x[1]),deriv((GEN)x[2],v));
      tetpil=avma; p1=gadd(p1,p2);
      if (tx==t_RFRACN) { y[1]=lpile(l,tetpil,p1); return y; }
      y[1]=(long)p1; return gerepileupto(av,gred_rfrac(y));

    case t_VEC: case t_COL: case t_MAT: lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=lderiv((GEN)x[i],v);
      return y;
  }
  err(typeer,"deriv");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                    INTEGRATION FORMELLE                         */
/*                                                                 */
/*******************************************************************/

static GEN
triv_integ(GEN x, long v, long tx, long lx)
{
  GEN y=cgetg(lx,tx);
  long i;

  y[1]=x[1];
  for (i=2; i<lx; i++) y[i]=linteg((GEN)x[i],v);
  return y;
}

GEN
integ(GEN x, long v)
{
  long lx,tx,e,i,j,vx,n,av=avma,tetpil;
  GEN y,p1;

  tx = typ(x);
  if (v < 0) v = gvar(x);
  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD && v>varn(x[1]))
    {
      y=cgetg(3,t_POLMOD); copyifstack(x[1],y[1]);
      y[2]=linteg((GEN)x[2],v); return y;
    }
    if (gcmp0(x)) return gzero;

    y=cgetg(4,t_POL); y[1] = evalsigne(1) | evallgef(4) | evalvarn(v);
    y[2]=zero; y[3]=lcopy(x); return y;
  }

  switch(tx)
  {
    case t_POL:
      vx=varn(x); lx=lgef(x);
      if (lx==2) return zeropol(min(v,vx));
      if (vx>v)
      {
        y=cgetg(4,t_POL);
	y[1] = signe(x)? evallgef(4) | evalvarn(v) | evalsigne(1)
	               : evallgef(4) | evalvarn(v);
        y[2]=zero; y[3]=lcopy(x); return y;
      }
      if (vx<v) return triv_integ(x,v,tx,lx);
      y=cgetg(lx+1,tx); y[2]=zero;
      for (i=3; i<=lx; i++)
        y[i]=ldivgs((GEN)x[i-1],i-2);
      y[1] = signe(x)? evallgef(lx+1) | evalvarn(v) | evalsigne(1)
                     : evallgef(lx+1) | evalvarn(v);
      return y;

    case t_SER:
      lx=lg(x); e=valp(x); vx=varn(x);
      if (!signe(x))
      {
        if (vx == v) e++; else if (vx < v) v = vx;
        return zeroser(v,e);
      }
      if (vx>v)
      {
        y=cgetg(4,t_POL);
        y[1] = evallgef(4) | evalvarn(v) | evalsigne(1);
        y[2]=zero; y[3]=lcopy(x); return y;
      }
      if (vx<v) return triv_integ(x,v,tx,lx);
      y=cgetg(lx,tx);
      for (i=2; i<lx; i++)
      {
	j=i+e-1;
        if (!j)
	{
	  if (!gcmp0((GEN)x[i])) err(inter2);
	  y[i]=zero;
	}
	else y[i] = ldivgs((GEN)x[i],j);
      }
      y[1]=x[1]+1; return y;

    case t_RFRAC: case t_RFRACN:
      vx = gvar(x);
      if (vx>v)
      {
	y=cgetg(4,t_POL);
	y[1] = signe(x[1])? evallgef(4) | evalvarn(v) | evalsigne(1)
	                  : evallgef(4) | evalvarn(v);
        y[2]=zero; y[3]=lcopy(x); return y;
      }
      if (vx<v)
      {
	p1=cgetg(v+2,t_VEC);
	for (i=0; i<vx; i++)   p1[i+1] = lpolx[i];
	for (i=vx+1; i<v; i++) p1[i+1] = lpolx[i];
        p1[v+1] = lpolx[vx]; p1[vx+1] = lpolx[v];
	y=integ(changevar(x,p1),vx); tetpil=avma;
	return gerepile(av,tetpil,changevar(y,p1));
      }

      n=lgef(x[1])+lgef(x[2])-4;
      y=gdiv(gtrunc(gmul((GEN)x[2], integ(tayl(x,v,n),v))), (GEN)x[2]);
      if (!gegal(deriv(y,v),x)) err(inter2);
      if (typ(y)==t_RFRAC && lgef(y[1]) == lgef(y[2]))
      {
        GEN p2;
	tx=typ(y[1]); p1=is_scalar_t(tx)? (GEN)y[1]: leading_term(y[1]);
	tx=typ(y[2]); p2=is_scalar_t(tx)? (GEN)y[2]: leading_term(y[2]);
	y=gsub(y, gdiv(p1,p2));
      }
      return gerepileupto(av,y);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lg(x); i++) y[i]=linteg((GEN)x[i],v);
      return y;
  }
  err(typeer,"integ");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                    PARTIES ENTIERES                             */
/*                                                                 */
/*******************************************************************/

GEN
gfloor(GEN x)
{
  GEN y;
  long i,lx, tx = typ(x);

  switch(tx)
  {
    case t_INT: case t_POL:
      return gcopy(x);

    case t_REAL:
      return mpent(x);

    case t_FRAC: case t_FRACN:
      return truedvmdii((GEN)x[1],(GEN)x[2],NULL);

    case t_RFRAC: case t_RFRACN:
      return gdeuc((GEN)x[1],(GEN)x[2]);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=lfloor((GEN)x[i]);
      return y;
  }
  err(typeer,"gfloor");
  return NULL; /* not reached */
}

GEN
gfrac(GEN x)
{
  long av = avma,tetpil;
  GEN p1 = gneg_i(gfloor(x));

  tetpil=avma; return gerepile(av,tetpil,gadd(x,p1));
}

GEN
gceil(GEN x)
{
  GEN y,p1;
  long i,lx,tx=typ(x),av,tetpil;

  switch(tx)
  {
    case t_INT: case t_POL:
      return gcopy(x);

    case t_REAL:
      av=avma; y=mpent(x);
      if (!gegal(x,y))
      {
        tetpil=avma; return gerepile(av,tetpil,addsi(1,y));
      }
      return y;

    case t_FRAC: case t_FRACN:
      av=avma; y=dvmdii((GEN)x[1],(GEN)x[2],&p1);
      if (p1 != gzero && gsigne(x)>0)
      {
        cgiv(p1); tetpil=avma;
        return gerepile(av,tetpil,addsi(1,y));
      }
      return y;

    case t_RFRAC: case t_RFRACN:
      return gdeuc((GEN)x[1],(GEN)x[2]);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=lceil((GEN)x[i]);
      return y;
  }
  err(typeer,"gceil");
  return NULL; /* not reached */
}

GEN
round0(GEN x, GEN *pte)
{
  if (pte) { long e; x = grndtoi(x,&e); *pte = stoi(e); }
  return ground(x);
}

GEN
ground(GEN x)
{
  GEN y,p1;
  long i,lx,tx=typ(x),av,tetpil;

  switch(tx)
  {
    case t_INT: case t_INTMOD: case t_QUAD:
      return gcopy(x);

    case t_REAL:
    {
      long ex, s = signe(x);
      if (s==0 || (ex=expo(x)) < -1) return gzero;
      if (ex < 0) return s>0? gun: negi(gun);
      av=avma; p1 = cgetr(3 + (ex>>TWOPOTBITS_IN_LONG));
      affsr(1,p1); setexpo(p1,-1); /* p1 = 0.5 */
      p1 = addrr(x,p1); tetpil = avma;
      return gerepile(av,tetpil,mpent(p1));
    }
    case t_FRAC: case t_FRACN:
      av=avma; p1 = addii(shifti((GEN)x[2], -1), (GEN)x[1]);
      return gerepileuptoint(av, truedvmdii(p1, (GEN)x[2], NULL));

    case t_POLMOD: y=cgetg(3,t_POLMOD);
      copyifstack(x[1],y[1]);
      y[2]=lround((GEN)x[2]); return y;

    case t_COMPLEX: case t_POL: case t_SER: case t_RFRAC: case t_RFRACN:
    case t_VEC: case t_COL: case t_MAT:
      lx = (tx==t_POL)? lgef(x): lg(x);
      y=cgetg(lx,tx);
      for (i=1; i<lontyp[tx]; i++) y[i]=x[i];
      for (   ; i<lx; i++) y[i]=lround((GEN)x[i]);
      if (tx==t_POL) return normalizepol_i(y, lx);
      if (tx==t_SER) return normalize(y);
      return y;
  }
  err(typeer,"ground");
  return NULL; /* not reached */
}

/* e = number of error bits on integral part */
GEN
grndtoi(GEN x, long *e)
{
  GEN y,p1;
  long i,tx=typ(x), lx,av,ex,e1;

  *e = -HIGHEXPOBIT;
  switch(tx)
  {
    case t_INT: case t_INTMOD: case t_QUAD:
    case t_FRAC: case t_FRACN:
      return ground(x);

    case t_REAL:
      av=avma; p1=gadd(ghalf,x); ex=expo(p1);
      if (ex<0)
      {
	if (signe(p1)>=0) { *e=expo(x); avma=av; return gzero; }
        *e=expo(addsr(1,x)); avma=av; return negi(gun);
      }
      lx=lg(x); e1 = ex - bit_accuracy(lx) + 1;
      settyp(p1,t_INT); setlgefint(p1,lx);
      y=shifti(p1,e1); if (signe(x)<0) y=addsi(-1,y);
      y = gerepileupto(av,y);

      if (e1<=0) { av=avma; e1=expo(subri(x,y)); avma=av; }
      *e=e1; return y;

    case t_POLMOD: y=cgetg(3,t_POLMOD);
      copyifstack(x[1],y[1]);
      y[2]=lrndtoi((GEN)x[2],e); return y;

    case t_COMPLEX: case t_POL: case t_SER: case t_RFRAC: case t_RFRACN:
    case t_VEC: case t_COL: case t_MAT:
      lx=(tx==t_POL)? lgef(x): lg(x);
      y=cgetg(lx,tx);
      for (i=1; i<lontyp[tx]; i++) y[i]=x[i];
      for (   ; i<lx; i++)
      {
        y[i]=lrndtoi((GEN)x[i],&e1);
        if (e1>*e) *e=e1;
      }
      return y;
  }
  err(typeer,"grndtoi");
  return NULL; /* not reached */
}

/* e = number of error bits on integral part */
GEN
gcvtoi(GEN x, long *e)
{
  long tx=typ(x), lx,i,ex,av,e1;
  GEN y;

  *e = -HIGHEXPOBIT;
  if (tx == t_REAL)
  {
    long x0,x1;
    ex=expo(x); if (ex<0) { *e=ex; return gzero; }
    lx=lg(x); e1 = ex - bit_accuracy(lx) + 1;
    x0=x[0]; x1=x[1]; settyp(x,t_INT); setlgefint(x,lx);
    y=shifti(x,e1); x[0]=x0; x[1]=x1;
    if (e1<=0) { av=avma; e1=expo(subri(x,y)); avma=av; }
    *e=e1; return y;
  }
  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++)
    {
      y[i]=lcvtoi((GEN)x[i],&e1);
      if (e1>*e) *e=e1;
    }
    return y;
  }
  return gtrunc(x);
}

GEN
gtrunc(GEN x)
{
  long tx=typ(x),av,tetpil,i,v;
  GEN y;

  switch(tx)
  {
    case t_INT: case t_POL:
      return gcopy(x);

    case t_REAL:
      return mptrunc(x);

    case t_FRAC: case t_FRACN:
      return divii((GEN)x[1],(GEN)x[2]);

    case t_PADIC:
      if (!signe(x[4])) return gzero;
      v = valp(x);
      if (!v) return gcopy((GEN)x[4]);
      if (v>0)
      { /* here p^v is an integer */
        av=avma; y=gpuigs((GEN)x[2],v); tetpil=avma;
        return gerepile(av,tetpil, mulii(y,(GEN)x[4]));
      }
      y=cgetg(3,t_FRAC);
      y[1]=licopy((GEN)x[4]);
      y[2]=lpuigs((GEN)x[2],-v);
      return y;

    case t_RFRAC: case t_RFRACN:
      return gdeuc((GEN)x[1],(GEN)x[2]);

    case t_SER:
      return gconvsp(x,1);

    case t_VEC: case t_COL: case t_MAT:
    {
      long lx=lg(x);

      y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=ltrunc((GEN)x[i]);
      return y;
    }
  }
  err(typeer,"gtrunc");
  return NULL; /* not reached */
}

GEN
trunc0(GEN x, GEN *pte)
{
  if (pte) { long e; x = gcvtoi(x,&e); *pte = stoi(e); }
  return gtrunc(x);
}

/*******************************************************************/
/*                                                                 */
/*           CONVERSIONS GEN -->  POLYNOMIALS & SERIES             */
/*                                                                 */
/*******************************************************************/

GEN
zeropol(long v)
{
  GEN x = cgetg(2,t_POL);
  x[1] = evallgef(2) | evalvarn(v); return x;
}

GEN
scalarpol(GEN x, long v)
{
  GEN y=cgetg(3,t_POL);
  y[1] = gcmp0(x)? evallgef(3) | evalvarn(v)
                 : evallgef(3) | evalvarn(v) | evalsigne(1);
  y[2]=lcopy(x); return y;
}

static GEN
gtopoly0(GEN x, long v, int reverse)
{
  long tx=typ(x),lx,i,j;
  GEN y;

  if (v<0) v = 0;
  if (isexactzero(x)) return zeropol(v);
  if (is_scalar_t(tx)) return scalarpol(x,v);

  switch(tx)
  {
    case t_POL:
      y=gcopy(x); break;
    case t_SER:
      y=gconvsp(x,1); break;
    case t_RFRAC: case t_RFRACN:
      y=gdeuc((GEN)x[1],(GEN)x[2]); break;
    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x);
      if (reverse)
      {
	while (lx-- && isexactzero((GEN)x[lx]));
	i=lx+2; y=cgetg(i,t_POL);
	y[1]=evallgef(i); if (!gcmp0(x)) y[1] |= evalsigne(1);
	for (j=2; j<i; j++) y[j]=lcopy((GEN)x[j-1]);
      }
      else
      {
	i=1; j=lx; while (lx-- && isexactzero((GEN)x[i++]));
	i=lx+2; y=cgetg(i,t_POL);
	y[1]=evallgef(i); if (!gcmp0(x)) y[1] |= evalsigne(1);
	lx = j-1;
	for (j=2; j<i; j++) y[j]=lcopy((GEN)x[lx--]);
      }
      break;
    default: err(typeer,"gtopoly");
  }
  setvarn(y,v); return y;
}

GEN
gtopolyrev(GEN x, long v) { return gtopoly0(x,v,1); }

GEN
gtopoly(GEN x, long v) { return gtopoly0(x,v,0); }

GEN
zeroser(long v, long val)
{
  GEN x = cgetg(2,t_SER);
  x[1]=evalvalp(val) | evalvarn(v); return x;
}

GEN
scalarser(GEN x, long v, long prec)
{
  GEN y=cgetg(prec+2,t_SER);
  long i;

  y[1]=evalsigne(1) | evalvalp(0) | evalvarn(v);
  y[2]=lcopy(x); for (i=3; i<=prec+1; i++) y[i]=zero;
  return y;
}

GEN
gtoser(GEN x, long v)
{
  long tx=typ(x),lx,i,j,l,av,tetpil;
  GEN y,p1,p2;

  if (v<0) v = 0;
  if (tx==t_SER) { y=gcopy(x); setvarn(y,v); return y; }
  if (isexactzero(x)) return zeroser(v,precdl);
  if (is_scalar_t(tx)) return scalarser(x,v,precdl);

  switch(tx)
  {
    case t_POL:
      lx=lgef(x); i=2; while (i<lx && gcmp0((GEN)x[i])) i++;
      l=lx-i; if (precdl>l) l=precdl;
      y=cgetg(l+2,t_SER);
      y[1] = evalsigne(1) | evalvalp(i-2) | evalvarn(v);
      for (j=2; j<=lx-i+1; j++) y[j]=lcopy((GEN)x[j+i-2]);
      for (   ; j<=l+1;    j++) y[j]=zero;
      break;

    case t_RFRAC: case t_RFRACN:
      av=avma; p1=gtoser((GEN)x[1],v); p2=gtoser((GEN)x[2],v);
      tetpil=avma; return gerepile(av,tetpil,gdiv(p1,p2));

    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); i=1; while (i<lx && isexactzero((GEN)x[i])) i++;
      y = cgetg(lx-i+2,t_SER);
      y[1] = evalsigne(1) | evalvalp(i-1) | evalvarn(v);
      for (j=2; j<=lx-i+1; j++) y[j]=lcopy((GEN)x[j+i-2]);
      break;

    default: err(typeer,"gtoser");
  }
  return y;
}

GEN
gtovec(GEN x)
{
  long tx,lx,i;
  GEN y;

  if (!x) return cgetg(1,t_VEC);
  tx = typ(x);
  if (is_scalar_t(tx) || is_rfrac_t(tx))
  {
    y=cgetg(2,t_VEC); y[1]=lcopy(x);
    return y;
  }
  if (is_graphicvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,t_VEC);
    for (i=1; i<lx; i++) y[i]=lcopy((GEN)x[i]);
    return y;
  }
  if (tx==t_POL)
  {
    lx=lgef(x); y=cgetg(lx-1,t_VEC);
    for (i=1; i<=lx-2; i++) y[i]=lcopy((GEN)x[lx-i]);
    return y;
  }
  if (tx==t_LIST)
  {
    lx=lgef(x); y=cgetg(lx-1,t_VEC); x++;
    for (i=1; i<=lx-2; i++) y[i]=lcopy((GEN)x[i]);
    return y;
  }
  if (!signe(x)) { y=cgetg(2,t_VEC); y[1]=zero; return y; }
  lx=lg(x); y=cgetg(lx-1,t_VEC); x++;
  for (i=1; i<=lx-2; i++) y[i]=lcopy((GEN)x[i]);
  return y;
}

GEN
compo(GEN x, long n)
{
  long l,tx=typ(x);

  if (tx==t_POL && n+1 >= lgef(x)) return gzero;
  if (tx==t_SER && !signe(x)) return gzero;
  if (!is_recursive_t(tx))
    err(talker, "this object doesn't have components (is a leaf)");
  l=lontyp[tx]+n-1;
  if (n<1 || l>=lg(x))
    err(talker,"nonexistent component");
  return gcopy((GEN)x[l]);
}

/* with respect to the main variable if v<0, with respect to the variable v
   otherwise. v ignored if x is not a polynomial/series. */

GEN
polcoeff0(GEN x, long n, long v)
{
  long tx=typ(x),lx,ex,w,av,tetpil;
  GEN xinit;

  if (is_scalar_t(tx)) return n? gzero: gcopy(x);

  switch(tx)
  {
    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      if (n<1 || n>=lg(x)) break;
      return gcopy((GEN)x[n]);

    case t_POL:
      if (n<0) return gzero;
      w=varn(x);
      if (v < 0 || v == w)
	return (n>=lgef(x)-2)? gzero: gcopy((GEN)x[n+2]);
      if (v < w) return n? gzero: gcopy(x);
      av=avma; xinit=x;
      x=gsubst(gsubst(x,w,polx[MAXVARN]),v,polx[0]);
      if (gvar(x)) { avma=av; return n? gzero: gcopy(xinit); }
      if (typ(x) == t_POL)
      {
        if (n>=lgef(x)-2) { avma=av; return gzero; }
        x = (GEN)x[n+2];
      }
      else
        x = polcoeff0(x, n, 0);
      tetpil=avma; return gerepile(av,tetpil,gsubst(x,MAXVARN,polx[w]));

    case t_SER:
      w=varn(x);
      if (v < 0 || v == w)
      {
	if (!signe(x)) return gzero;
	lx=lg(x); ex=valp(x); if (n<ex) return gzero;
	if (n>=ex+lx-2) break;
	return gcopy((GEN)x[n-ex+2]);
      }
      if (v < w) return n?  gzero: gcopy(x);
      av=avma; xinit=x;
      x=gsubst(gsubst(x,w,polx[MAXVARN]),v,polx[0]);
      if (gvar(x)) { avma=av; return n? gzero: gcopy(xinit); }
      if (gcmp0(x)) { avma=av; return gzero; }
      if (typ(x) == t_SER)
      {
        lx=lg(x); ex=valp(x); if (n<ex) return gzero;
        if (n>=ex+lx-2) break;
        x = (GEN)x[n-ex+2];
      }
      else
        x = polcoeff0(x, n, 0);
      tetpil=avma; return gerepile(av,tetpil,gsubst(x,MAXVARN,polx[w]));

    case t_RFRAC: case t_RFRACN:
      w = precdl; av = avma;
      if (v<0) v = gvar(x);
      ex = ggval((GEN)x[2], polx[v]);
      precdl = n + ex + 1; x = gtoser(x, v); precdl = w;
      return gerepileupto(av, polcoeff0(x, n, v));
  }
  err(talker,"nonexistent component in truecoeff");
  return NULL; /* not reached */
}

GEN
truecoeff(GEN x, long n)
{
  return polcoeff0(x,n,-1);
}

GEN
denom(GEN x)
{
  long lx,i,av,tetpil;
  GEN s,t;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_PADIC: case t_SER:
      return gun;

    case t_FRAC: case t_FRACN:
      return absi((GEN)x[2]);

    case t_COMPLEX:
      av=avma; t=denom((GEN)x[1]); s=denom((GEN)x[2]); tetpil=avma;
      return gerepile(av,tetpil,glcm(s,t));

    case t_QUAD:
      av=avma; t=denom((GEN)x[2]); s=denom((GEN)x[3]); tetpil=avma;
      return gerepile(av,tetpil,glcm(s,t));

    case t_POLMOD:
      return denom((GEN)x[2]);

    case t_RFRAC: case t_RFRACN:
      return gcopy((GEN)x[2]);

    case t_POL:
      return polun[varn(x)];

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); if (lx==1) return gun;
      av = tetpil = avma; s = denom((GEN)x[1]);
      for (i=2; i<lx; i++)
      {
        t = denom((GEN)x[i]);
        /* t != gun est volontaire */
        if (t != gun) { tetpil=avma; s=glcm(s,t); }
      }
      return gerepile(av,tetpil,s);
  }
  err(typeer,"denom");
  return NULL; /* not reached */
}

GEN
numer(GEN x)
{
  long av,tetpil;
  GEN s;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD:
    case t_PADIC: case t_POL: case t_SER:
      return gcopy(x);

    case t_FRAC: case t_FRACN:
      return (signe(x[2])>0)? gcopy((GEN)x[1]): gneg((GEN)x[1]);

    case t_POLMOD:
      av=avma; s=numer((GEN)x[2]); tetpil=avma;
      return gerepile(av,tetpil,gmodulcp(s,(GEN)x[1]));

    case t_RFRAC: case t_RFRACN:
      return gcopy((GEN)x[1]);

    case t_COMPLEX: case t_QUAD: case t_VEC: case t_COL: case t_MAT:
      av=avma; s=denom(x); tetpil=avma;
      return gerepile(av,tetpil,gmul(s,x));
  }
  err(typeer,"numer");
  return NULL; /* not reached */
}

/* Lift only intmods if v does not occur in x, lift with respect to main
 * variable of x if v < 0, with respect to variable v otherwise.
 */
GEN
lift0(GEN x, long v)
{
  long lx,tx=typ(x),i;
  GEN y;

  switch(tx)
  {
    case t_INT: case t_REAL:
      return gcopy(x);

    case t_INTMOD:
      return gcopy((GEN)x[2]);

    case t_POLMOD:
      if (v < 0 || v == varn((GEN)x[1])) return gcopy((GEN)x[2]);
      y = cgetg(3,tx);
      y[1] = (long)lift0((GEN)x[1],v);
      y[2] = (long)lift0((GEN)x[2],v); return y;

    case t_SER:
      if (!signe(x)) return gcopy(x);
      lx=lg(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)lift0((GEN)x[i],v);
      return y;

    case t_FRAC: case t_FRACN: case t_COMPLEX: case t_RFRAC:
    case t_RFRACN: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=(long)lift0((GEN)x[i],v);
      return y;

    case t_POL:
      y=cgetg(lx=lgef(x),tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)lift0((GEN)x[i],v);
      return y;

    case t_QUAD:
      y=cgetg(4,tx); copyifstack(x[1],y[1]);
      for (i=2; i<4; i++) y[i]=(long)lift0((GEN)x[i],v);
      return y;
  }
  err(typeer,"lift");
  return NULL; /* not reached */
}

GEN
lift(GEN x)
{
  return lift0(x,-1);
}

/* same as lift, without copy. May DESTROY x. For internal use only.
   Conventions on v as for lift. */
GEN
lift_intern0(GEN x, long v)
{
  long i,lx,tx=typ(x);

  switch(tx)
  {
    case t_INT: case t_REAL:
      return x;

    case t_INTMOD:
      return (GEN)x[2];

    case t_POLMOD:
      if (v < 0 || v == varn((GEN)x[1])) return (GEN)x[2];
      x[1]=(long)lift_intern0((GEN)x[1],v);
      x[2]=(long)lift_intern0((GEN)x[2],v);
      return x;

    case t_SER: if (!signe(x)) return x; /* fall through */
    case t_FRAC: case t_FRACN: case t_COMPLEX: case t_QUAD: case t_POL:
    case t_RFRAC: case t_RFRACN: case t_VEC: case t_COL: case t_MAT:
      lx = (tx==t_POL)? lgef(x): lg(x);
      for (i = lx-1; i>=lontyp[tx]; i--)
        x[i] = (long) lift_intern0((GEN)x[i],v);
      return x;
  }
  err(typeer,"lift_intern");
  return NULL; /* not reached */
}

/* memes conventions pour v que lift */
GEN
centerlift0(GEN x, long v)
{
  long lx,tx=typ(x),i,av;
  GEN y;

  switch(tx)
  {
    case t_INT:
      return icopy(x);

    case t_INTMOD:
      av=avma; i=cmpii(shifti((GEN)x[2],1),(GEN)x[1]); avma=av;
      return (i>0)? subii((GEN)x[2],(GEN)x[1]): icopy((GEN)x[2]);

    case t_POLMOD:
      if (v < 0 || v == varn((GEN)x[1])) return gcopy((GEN)x[2]);
      y=cgetg(3,tx);
      y[1]=(long)centerlift0((GEN)x[1],v); y[2]=(long)centerlift0((GEN)x[2],v);
      return y;

    case t_SER:
      if (!signe(x)) return gcopy(x);
      lx=lg(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)centerlift0((GEN)x[i],v);
      return y;

    case t_POL:
    case t_FRAC: case t_FRACN: case t_COMPLEX: case t_RFRAC:
    case t_RFRACN: case t_VEC: case t_COL: case t_MAT:
      lx = (tx==t_POL)? lgef(x): lg(x);
      y=cgetg(lx,tx); y[1]=x[1];
      for (i=lontyp[tx]; i<lx; i++) y[i]=(long)centerlift0((GEN)x[i],v);
      return y;

    case t_QUAD:
      y=cgetg(4,tx); copyifstack(x[1],y[1]);
      for (i=2; i<4; i++) y[i]=(long)centerlift0((GEN)x[i],v);
      return y;
  }
  err(typeer,"centerlift");
  return NULL; /* not reached */
}

GEN
centerlift(GEN x)
{
  return centerlift0(x,-1);
}

/*******************************************************************/
/*                                                                 */
/*                  PARTIES REELLE ET IMAGINAIRES                  */
/*                                                                 */
/*******************************************************************/

static GEN
op_ReIm(GEN f(GEN), GEN x)
{
  long lx,i,j,av,tetpil, tx = typ(x);
  GEN p1,p2,r2,i2,z;

  switch(tx)
  {
    case t_POL:
      lx=lgef(x); av=avma;
      for (i=lx-1; i>=2; i--)
        if (!gcmp0(f((GEN)x[i]))) break;
      avma=av; if (i==1) return zeropol(varn(x));

      z=cgetg(i+1,tx); z[1]=evalsigne(1)|evallgef(1+i)|evalvarn(varn(x));
      for (j=2; j<=i; j++) z[j] = (long)f((GEN)x[j]);
      return z;

    case t_SER:
      if (gcmp0(x)) { z=cgetg(2,tx); z[1]=x[1]; return z; }
      lx=lg(x); av=avma;
      for (i=2; i<lx; i++)
        if (!gcmp0(f((GEN)x[i]))) break;
      avma=av; if (i==lx) return zeroser(varn(x),lx-2+valp(x));

      z=cgetg(lx-i+2,tx); z[1]=x[1]; setvalp(z, valp(x)+i-2);
      for (j=2; i<lx; j++,i++) z[j] = (long) f((GEN)x[i]);
      return z;

    case t_RFRAC: case t_RFRACN:
    {
      av=avma; r2=greal((GEN)x[2]); i2=gimag((GEN)x[2]);
      if (f==greal)
        p1 = gadd(gmul(greal((GEN)x[1]),r2),
                  gmul(gimag((GEN)x[1]),i2));
      else
        p1 = gsub(gmul(gimag((GEN)x[1]),r2),
                  gmul(greal((GEN)x[1]),i2));
      p2=gadd(gsqr(r2), gsqr(i2));
      tetpil=avma; return gerepile(av,tetpil,gdiv(p1,p2));
    }

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long) f((GEN)x[i]);
      return z;
  }
  err(typeer,"greal/gimag");
  return NULL; /* not reached */
}

GEN
greal(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return gcopy(x);

    case t_COMPLEX:
      return gcopy((GEN)x[1]);

    case t_QUAD:
      return gcopy((GEN)x[2]);
  }
  return op_ReIm(greal,x);
}

GEN
gimag(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return gzero;

    case t_COMPLEX:
      return gcopy((GEN)x[2]);

    case t_QUAD:
      return gcopy((GEN)x[3]);
  }
  return op_ReIm(gimag,x);
}

/*******************************************************************/
/*                                                                 */
/*                     LOGICAL OPERATIONS                          */
/*                                                                 */
/*******************************************************************/

GEN
glt(GEN x, GEN y) { return gcmp(x,y)<0? gun: gzero; }

GEN
gle(GEN x, GEN y) { return gcmp(x,y)<=0? gun: gzero; }

GEN
gge(GEN x, GEN y) { return gcmp(x,y)>=0? gun: gzero; }

GEN
ggt(GEN x, GEN y) { return gcmp(x,y)>0? gun: gzero; }

GEN
geq(GEN x, GEN y) { return gegal(x,y)? gun: gzero; }

GEN
gne(GEN x, GEN y) { return gegal(x,y)? gzero: gun; }

GEN
gand(GEN x, GEN y) { return gcmp0(x)? gzero: (gcmp0(y)? gzero: gun); }

GEN
gor(GEN x, GEN y) { return gcmp0(x)? (gcmp0(y)? gzero: gun): gun; }

GEN
gnot(GEN x) { return gcmp0(x)? gun: gzero; }

/*******************************************************************/
/*                                                                 */
/*                      FORMAL SIMPLIFICATIONS                     */
/*                                                                 */
/*******************************************************************/

GEN
geval(GEN x)
{
  long av,tetpil,lx,i, tx = typ(x);
  GEN y,z;

  if (is_const_t(tx)) return gcopy(x);
  if (is_graphicvec_t(tx) || tx == t_RFRACN)
  {
    lx=lg(x); y=cgetg(lx, tx);
    for (i=1; i<lx; i++) y[i] = (long)geval((GEN)x[i]);
    return y;
  }

  switch(tx)
  {
    case t_STR:
      return flisexpr(GSTR(x));

    case t_POLMOD: y=cgetg(3,tx);
      y[1]=(long)geval((GEN)x[1]);
      av=avma; z=geval((GEN)x[2]); tetpil=avma;
      y[2]=lpile(av,tetpil,gmod(z,(GEN)y[1]));
      return y;

    case t_POL:
      lx=lgef(x); if (lx==2) return gzero;
      {
        entree *ep = varentries[varn(x)];
        if (!ep) return gcopy(x);
        z = (GEN)ep->value;
      }
      y=gzero; av=avma;
      for (i=lx-1; i>1; i--)
      {
        tetpil=avma;
        y = gadd(geval((GEN)x[i]), gmul(z,y));
      }
      return gerepile(av,tetpil,y);

    case t_SER:
      err(impl, "evaluation of a power series");

    case t_RFRAC:
      return gdiv(geval((GEN)x[1]),geval((GEN)x[2]));
  }
  err(typeer,"geval");
  return NULL; /* not reached */
}

GEN
simplify(GEN x)
{
  long tx=typ(x),av,tetpil,i,lx;
  GEN p1,y;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC:
      return is_universal_constant(x)? x: gcopy(x);

    case t_INTMOD: case t_PADIC: case t_QFR: case t_QFI:
    case t_LIST: case t_STR: case t_VECSMALL:
      return gcopy(x);

    case t_FRACN:
      return gred(x);

    case t_COMPLEX:
      if (is_universal_constant(x)) return x;
      if (isexactzero((GEN)x[2])) return simplify((GEN)x[1]);
      y=cgetg(3,tx);
      y[1]=(long)simplify((GEN)x[1]);
      y[2]=(long)simplify((GEN)x[2]); return y;

    case t_QUAD:
      if (isexactzero((GEN)x[3])) return simplify((GEN)x[2]);
      y=cgetg(4,tx);
      y[1]=lcopy((GEN)x[1]);
      y[2]=(long)simplify((GEN)x[2]);
      y[3]=(long)simplify((GEN)x[3]); return y;

    case t_POLMOD: y=cgetg(3,tx);
      y[1]=(long)simplify((GEN)x[1]);
      av=avma; p1=gmod((GEN)x[2],(GEN)y[1]); tetpil=avma;
      y[2]=lpile(av,tetpil,simplify(p1)); return y;

    case t_POL:
      lx=lgef(x); if (lx==2) return gzero;
      if (lx==3) return simplify((GEN)x[2]);
      y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)simplify((GEN)x[i]);
      return y;

    case t_SER:
      if (!signe(x)) return gcopy(x);
      lx=lg(x);
      y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)simplify((GEN)x[i]);
      return y;

    case t_RFRAC: y=cgetg(3,tx);
      y[1]=(long)simplify((GEN)x[1]);
      y[2]=(long)simplify((GEN)x[2]); return y;

    case t_RFRACN:
      av=avma; y=gred_rfrac(x); tetpil=avma;
      return gerepile(av,tetpil,simplify(y));

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=(long)simplify((GEN)x[i]);
      return y;
  }
  err(typeer,"simplify");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*              EVALUATION OF SOME SIMPLE FORMAL OBJECTS           */
/*                                                                 */
/*******************************************************************/
static GEN
qfeval0_i(GEN q, GEN x, long n)
{
  long i,j,av=avma;
  GEN res=gzero;

  for (i=2;i<n;i++)
    for (j=1;j<i;j++)
      res = gadd(res, gmul(gcoeff(q,i,j), mulii((GEN)x[i],(GEN)x[j])) );
  res=gshift(res,1);
  for (i=1;i<n;i++)
    res = gadd(res, gmul(gcoeff(q,i,i), sqri((GEN)x[i])) );
  return gerepileupto(av,res);
}

#if 0
static GEN
qfeval0(GEN q, GEN x, long n)
{
  long i,j,av=avma;
  GEN res=gzero;

  for (i=2;i<n;i++)
    for (j=1;j<i;j++)
      res = gadd(res, gmul(gcoeff(q,i,j), gmul((GEN)x[i],(GEN)x[j])) );
  res=gshift(res,1);
  for (i=1;i<n;i++)
    res = gadd(res, gmul(gcoeff(q,i,i), gsqr((GEN)x[i])) );
  return gerepileupto(av,res);
}
#else
static GEN
qfeval0(GEN q, GEN x, long n)
{
  long i,j,av=avma;
  GEN res = gmul(gcoeff(q,1,1), gsqr((GEN)x[1]));

  for (i=2; i<n; i++)
  {
    GEN l = (GEN)q[i];
    GEN sx = gmul((GEN)l[1], (GEN)x[1]);
    for (j=2; j<i; j++)
      sx = gadd(sx, gmul((GEN)l[j],(GEN)x[j]));
    sx = gadd(gshift(sx,1), gmul((GEN)l[i],(GEN)x[i]));

    res = gadd(res, gmul((GEN)x[i], sx));
  }
  return gerepileupto(av,res);
}
#endif

/* We assume q is a real symetric matrix */
GEN
qfeval(GEN q, GEN x)
{
  long n=lg(q);

  if (n==1)
  {
    if (typ(q) != t_MAT || lg(x) != 1)
      err(talker,"invalid data in qfeval");
    return gzero;
  }
  if (typ(q) != t_MAT || lg(q[1]) != n)
    err(talker,"invalid quadratic form in qfeval");
  if (typ(x) != t_COL || lg(x) != n)
    err(talker,"invalid vector in qfeval");

  return qfeval0(q,x,n);
}

/* the Horner-type evaluation (mul x 2/3) would force us to use gmul and not
 * mulii (more than 4 x slower for small entries). Not worth it.
 */
static GEN
qfbeval0_i(GEN q, GEN x, GEN y, long n)
{
  long i,j,av=avma;
  GEN res = gmul(gcoeff(q,1,1), mulii((GEN)x[1],(GEN)y[1]));

  for (i=2;i<n;i++)
  {
    for (j=1;j<i;j++)
    {
      GEN p1 = addii(mulii((GEN)x[i],(GEN)y[j]), mulii((GEN)x[j],(GEN)y[i]));
      res = gadd(res, gmul(gcoeff(q,i,j),p1));
    }
    res = gadd(res, gmul(gcoeff(q,i,i), mulii((GEN)x[i],(GEN)y[i])));
  }
  return gerepileupto(av,res);
}

#if 0
static GEN
qfbeval0(GEN q, GEN x, GEN y, long n)
{
  long i,j,av=avma;
  GEN res = gmul(gcoeff(q,1,1), gmul((GEN)x[1],(GEN)y[1]));

  for (i=2;i<n;i++)
  {
    for (j=1;j<i;j++)
    {
      GEN p1 = gadd(gmul((GEN)x[i],(GEN)y[j]), gmul((GEN)x[j],(GEN)y[i]));
      res = gadd(res, gmul(gcoeff(q,i,j),p1));
    }
    res = gadd(res, gmul(gcoeff(q,i,i), gmul((GEN)x[i],(GEN)y[i])));
  }
  return gerepileupto(av,res);
}
#else
static GEN
qfbeval0(GEN q, GEN x, GEN y, long n)
{
  long i,j,av=avma;
  GEN res = gmul(gcoeff(q,1,1), gmul((GEN)x[1], (GEN)y[1]));

  for (i=2; i<n; i++)
  {
    GEN l = (GEN)q[i];
    GEN sx = gmul((GEN)l[1], (GEN)y[1]);
    GEN sy = gmul((GEN)l[1], (GEN)x[1]);
    for (j=2; j<i; j++)
    {
      sx = gadd(sx, gmul((GEN)l[j],(GEN)y[j]));
      sy = gadd(sy, gmul((GEN)l[j],(GEN)x[j]));
    }
    sx = gadd(sx, gmul((GEN)l[i],(GEN)y[i]));

    sx = gmul((GEN)x[i], sx);
    sy = gmul((GEN)y[i], sy);
    res = gadd(res, gadd(sx,sy));
  }
  return gerepileupto(av,res);
}
#endif

/* We assume q is a real symetric matrix */
GEN
qfbeval(GEN q, GEN x, GEN y)
{
  long n=lg(q);

  if (n==1)
  {
    if (typ(q) != t_MAT || lg(x) != 1 || lg(y) != 1)
      err(talker,"invalid data in qfbeval");
    return gzero;
  }
  if (typ(q) != t_MAT || lg(q[1]) != n)
    err(talker,"invalid quadratic form in qfbeval");
  if (typ(x) != t_COL || lg(x) != n || typ(y) != t_COL || lg(y) != n)
    err(talker,"invalid vector in qfbeval");

  return qfbeval0(q,x,y,n);
}

/* yield X = M'.q.M, assuming q is symetric.
 * X_ij are X_ji identical, not copies
 * if flag is set, M has integer entries
 */
GEN
qf_base_change(GEN q, GEN M, int flag)
{
  long i,j, k = lg(M), n=lg(q);
  GEN res = cgetg(k,t_MAT);
  GEN (*qf)(GEN,GEN,long)  = flag? qfeval0_i:  qfeval0;
  GEN (*qfb)(GEN,GEN,GEN,long) = flag? qfbeval0_i: qfbeval0;

  if (n==1)
  {
    if (typ(q) != t_MAT || k != 1)
      err(talker,"invalid data in qf_base_change");
    return res;
  }
  if (typ(M) != t_MAT || k == 1 || lg(M[1]) != n)
    err(talker,"invalid base change matrix in qf_base_change");

  for (i=1;i<k;i++)
  {
    res[i] = lgetg(k,t_COL);
    coeff(res,i,i) = (long) qf(q,(GEN)M[i],n);
  }
  for (i=2;i<k;i++)
    for (j=1;j<i;j++)
      coeff(res,i,j)=coeff(res,j,i) = (long) qfb(q,(GEN)M[i],(GEN)M[j],n);
  return res;
}

/* compute M'.M */
GEN
gram_matrix(GEN M)
{
  long n=lg(M),i,j,k, av;
  GEN res = cgetg(n,t_MAT),p1;

  if (n==1)
  {
    if (typ(M) != t_MAT)
      err(talker,"invalid data in gram_matrix");
    return res;
  }
  if (typ(M) != t_MAT || lg(M[1]) != n)
    err(talker,"not a square matrix in gram_matrix");

  for (i=1;i<n;i++) res[i]=lgetg(n,t_COL);
  av=avma;
  for (i=1;i<n;i++)
  {
    p1 = gzero;
    for (k=1;k<n;k++)
      p1 = gadd(p1, gsqr(gcoeff(M,k,i)));
    coeff(res,i,i) = (long) gerepileupto(av,p1);
    av=avma;
  }
  for (i=2;i<n;i++)
    for (j=1;j<i;j++)
    {
      p1=gzero;
      for (k=1;k<n;k++)
	p1 = gadd(p1, gmul(gcoeff(M,k,i),gcoeff(M,k,j)));
      coeff(res,i,j)=coeff(res,j,i) = lpileupto(av,p1);
      av=avma;
    }
  return res;
}

/* return Re(x * y), x and y scalars */
static GEN
mul_real(GEN x, GEN y)
{
  if (typ(x) == t_COMPLEX)
  {
    if (typ(y) == t_COMPLEX)
    {
      long av=avma, tetpil;
      GEN p1 = gmul((GEN)x[1], (GEN) y[1]);
      GEN p2 = gneg(gmul((GEN)x[2], (GEN) y[2]));
      tetpil=avma; return gerepile(av,tetpil,gadd(p1,p2));
    }
    x = (GEN)x[1];
  }
  else if (typ(y) == t_COMPLEX) y = (GEN)y[1];
  return gmul(x,y);
}

/* Compute Re(x * y), x and y matrices of compatible dimensions
 * assume lx, ly > 1, and scalar entries */
GEN
mulmat_real(GEN x, GEN y)
{
  long av,tetpil,i,j,k, lx = lg(x), ly = lg(y), l = lg(x[1]);
  GEN p1,p2, z = cgetg(ly,t_MAT);

  for (j=1; j<ly; j++)
  {
    z[j] = lgetg(l,t_COL);
    for (i=1; i<l; i++)
    {
      p1=gzero; av=avma;
      for (k=1; k<lx; k++)
      {
        p2=mul_real(gcoeff(x,i,k),gcoeff(y,k,j));
        tetpil=avma; p1=gadd(p1,p2);
      }
      coeff(z,i,j)=lpile(av,tetpil,p1);
    }
  }
  return z;
}

static GEN
hqfeval0(GEN q, GEN x, long n)
{
  long i,j, av=avma;
  GEN res=gzero;

  for (i=2;i<n;i++)
    for (j=1;j<i;j++)
    {
      GEN p1 = gmul((GEN)x[i],gconj((GEN)x[j]));
      res = gadd(res, mul_real(gcoeff(q,i,j),p1));
    }
  res=gshift(res,1);
  for (i=1;i<n;i++)
    res = gadd(res, gmul(gcoeff(q,i,i), gnorm((GEN)x[i])) );
  return gerepileupto(av,res);
}

/* We assume q is a hermitian complex matrix */
GEN
hqfeval(GEN q, GEN x)
{
  long n=lg(q);

  if (n==1)
  {
    if (typ(q) != t_MAT || lg(x) != 1)
      err(talker,"invalid data in hqfeval");
    return gzero;
  }
  if (typ(q) != t_MAT || lg(q[1]) != n)
    err(talker,"invalid quadratic form in hqfeval");
  if (typ(x) != t_COL || lg(x) != n)
    err(talker,"invalid vector in hqfeval");

  return hqfeval0(q,x,n);
}

GEN
poleval(GEN x, GEN y)
{
  long av,tetpil,i,j,imin,tx=typ(x);
  GEN p1,p2,p3,r,s;

  if (is_scalar_t(tx)) return gcopy(x);
  switch(tx)
  {
    case t_POL:
      i=lgef(x)-1; imin=2; break;

    case t_RFRAC: case t_RFRACN: av=avma;
      p1=poleval((GEN)x[1],y);
      p2=poleval((GEN)x[2],y); tetpil=avma;
      return gerepile(av,tetpil,gdiv(p1,p2));

    case t_VEC: case t_COL:
      i=lg(x)-1; imin=1; break;
    default: err(typeer,"poleval");
  }
  if (i<=imin)
    return (i==imin)? gcopy((GEN)x[imin]): gzero;

  av=avma; p1=(GEN)x[i]; i--;
  if (typ(y)!=t_COMPLEX)
  {
#if 0 /* standard Horner's rule */
    for ( ; i>=imin; i--)
      p1 = gadd(gmul(p1,y),(GEN)x[i]);
#endif
    /* specific attention to sparse polynomials */
    for ( ; i>=imin; i=j-1)
    {
      for (j=i; gcmp0((GEN)x[j]); j--)
        if (j==imin)
        {
          if (i!=j) y = gpuigs(y,i-j+1);
          tetpil=avma; return gerepile(av,tetpil,gmul(p1,y));
        }
      r = (i==j)? y: gpuigs(y,i-j+1);
      p1 = gadd(gmul(p1,r), (GEN)x[j]);
    }
    return gerepileupto(av,p1);
  }

  p2=(GEN)x[i]; i--; r=gtrace(y); s=gneg_i(gnorm(y));
  for ( ; i>=imin; i--)
  {
    p3=gadd(p2,gmul(r,p1));
    p2=gadd((GEN)x[i],gmul(s,p1)); p1=p3;
  }
  p1=gmul(y,p1); tetpil=avma;
  return gerepile(av,tetpil,gadd(p1,p2));
}
