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
/**                      GENERIC OPERATIONS                        **/
/**                        (second part)                           **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

/*******************************************************************/
/*                                                                 */
/*                    OPERATIONS BY VALUE                          */
/*            f is a pointer to the function called.               */
/*            result is gaffect-ed to last parameter               */
/*                                                                 */
/*******************************************************************/

void
gop1z(GEN (*f)(GEN), GEN x, GEN y)
{
  pari_sp av=avma; gaffect(f(x), y); avma=av;
}

void
gop2z(GEN (*f)(GEN, GEN), GEN x, GEN y, GEN z)
{
  pari_sp av=avma; gaffect(f(x, y), z); avma=av;
}

void
gops2gsz(GEN (*f)(GEN, long), GEN x, long s, GEN z)
{
  pari_sp av=avma; gaffect(f(x, s), z); avma=av;
}

void
gops2sgz(GEN (*f)(long, GEN), long s, GEN y, GEN z)
{
  pari_sp av=avma; gaffect(f(s, y), z); avma=av;
}

void
gops2ssz(GEN (*f)(long, long), long s, long y, GEN z)
{
  pari_sp av=avma; gaffect(f(s, y), z); avma=av;
}

/*******************************************************************/
/*                                                                 */
/*                OPERATIONS USING SMALL INTEGERS                  */
/*                                                                 */
/*******************************************************************/

/* small int prototype */
static long court_p[] = { evaltyp(t_INT) | _evallg(3),0,0 };

GEN
gopsg2(GEN (*f)(GEN, GEN), long s, GEN y)
{
  affsi(s,court_p); return f(court_p,y);
}

GEN
gopgs2(GEN (*f)(GEN, GEN), GEN y, long s)
{
  affsi(s,court_p); return f(y,court_p);
}

long
opgs2(int (*f)(GEN, GEN), GEN y, long s)
{
  affsi(s,court_p); return f(y,court_p);
}

void
gopsg2z(GEN (*f)(GEN, GEN), long s, GEN y, GEN z)
{
  pari_sp av=avma;
  affsi(s,court_p); gaffect(f(court_p,y),z); avma=av;
}

void
gopgs2z(GEN (*f)(GEN, GEN), GEN y, long s, GEN z)
{
  pari_sp av=avma;
  affsi(s,court_p); gaffect(f(y,court_p),z); avma=av;
}

/*******************************************************************/
/*                                                                 */
/*                    CREATION OF A P-ADIC GEN                     */
/*                                                                 */
/*******************************************************************/

/* y[4] not filled */
static GEN
cgetp2(GEN x, long v)
{
  GEN y = cgetg(5,t_PADIC);
  y[1] = evalprecp(precp(x)) | evalvalp(v);
  icopyifstack(x[2], y[2]);
  y[3] = licopy((GEN)x[3]); return y;
}

GEN
cgetp(GEN x)
{
  GEN y = cgetp2(x, 0);
  y[4] = lgeti(lgefint(x[3])); return y;
}

GEN 
pureimag(GEN x)
{
  GEN y = cgetg(3,t_COMPLEX);
  y[1] = zero;
  y[2] = (long)x; return y;
}

/*******************************************************************/
/*                                                                 */
/*                            SIZES                                */
/*                                                                 */
/*******************************************************************/

long
glength(GEN x)
{
  switch(typ(x))
  {
    case t_INT: return lgefint(x)-2;
    case t_POL: case t_LIST: return lgef(x)-2;
    case t_REAL: return signe(x)? lg(x)-2: 0;
    case t_STR: return strlen(GSTR(x));
    case t_VECSMALL: return lg(x)-1;
  }
  return lg(x)-lontyp[typ(x)];
}

GEN
matsize(GEN x)
{
  GEN y=cgetg(3,t_VEC);

  switch(typ(x))
  {
    case t_VEC:
      y[1]=un; y[2]=lstoi(lg(x)-1); break;
    case t_COL:
      y[1]=lstoi(lg(x)-1); y[2]=un; break;
    case t_MAT:
      y[2]=lstoi(lg(x)-1);
      y[1]=(lg(x)==1)? zero: lstoi(lg(x[1])-1); break;
    default: err(typeer,"matsize");
  }
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                  Conversion t_POL --> t_SER                     */
/*                                                                 */
/*******************************************************************/

GEN
greffe(GEN x, long l, long use_stack)
{
  long i, e, k;
  GEN y;

  if (typ(x)!=t_POL) err(notpoler,"greffe");
  if (use_stack) y = cgetg(l,t_SER);
  else
  {
    y = (GEN) gpmalloc(l*sizeof(long));
    y[0] = evaltyp(t_SER) | evallg(l);
  }
  if (gcmp0(x))
  {
    y[1] = evalvalp(l-2) | evalvarn(varn(x));
    for (i = 2; i < l; i++) y[i] = zero;
    return y;
  }
  
  e = polvaluation(x, NULL);
  y[1] = evalsigne(1) | evalvalp(e) | evalvarn(varn(x));
  k = lgef(x)-1 - e;
  for (i = l-1; i >  k; i--) y[i] = zero;
  for (       ; i >= 2; i--) y[i] = x[i+e];
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                 CONVERSION GEN --> long                         */
/*                                                                 */
/*******************************************************************/

long
gtolong(GEN x)
{
  long y, tx=typ(x);
  pari_sp av=avma;

  switch(tx)
  {
    case t_INT:
      return itos(x);
    case t_REAL: case t_FRAC: case t_FRACN:
      y=itos(ground(x)); avma=av; return y;
    case t_COMPLEX:
      if (gcmp0((GEN)x[2])) return gtolong((GEN)x[1]); break;
    case t_QUAD:
      if (gcmp0((GEN)x[3])) return gtolong((GEN)x[2]); break;
  }
  err(typeer,"gtolong");
  return 0; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                         COMPARISONS                             */
/*                                                                 */
/*******************************************************************/

/* returns 1 whenever x = 0, and 0 otherwise */
int
gcmp0(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_POL: case t_SER:
      return !signe(x);

    case t_INTMOD: case t_POLMOD:
      return gcmp0((GEN)x[2]);

    case t_FRAC: case t_FRACN:
      return !signe(x[1]);

    case t_COMPLEX:
     /* is 0 iff norm(x) would be 0 (can happen with Re(x) and Im(x) != 0
      * only if Re(x) and Im(x) are of type t_REAL). See mp.c:addrr().
      */
      if (gcmp0((GEN)x[1]))
      {
	if (gcmp0((GEN)x[2])) return 1;
	if (typ(x[1])!=t_REAL || typ(x[2])!=t_REAL) return 0;
	return (expo(x[1])>expo(x[2]));
      }
      if (gcmp0((GEN)x[2]))
      {
	if (typ(x[1])!=t_REAL || typ(x[2])!=t_REAL) return 0;
	return (expo(x[2])>expo(x[1]));
      }
      return 0;

    case t_PADIC:
      return !signe(x[4]);

    case t_QUAD:
      return gcmp0((GEN)x[2]) && gcmp0((GEN)x[3]);

    case t_RFRAC: case t_RFRACN:
      return gcmp0((GEN)x[1]);

    case t_VEC: case t_COL: case t_MAT:
    {
      long i;
      for (i=lg(x)-1; i; i--)
        if (!gcmp0((GEN)x[i])) return 0;
      return 1;
    }
  }
  return 0;
}

/* returns 1 whenever x = 1, 0 otherwise */
int
gcmp1(GEN x)
{
  switch(typ(x))
  {
    case t_INT:
      return is_pm1(x) && signe(x)==1;

    case t_REAL:
      if (signe(x) > 0 && expo(x)==0 && (ulong)x[2]==HIGHBIT)
      {
        long i,lx = lg(x);
        for (i=3; i<lx; i++)
          if (x[i]) return 0;
        return 1;
      }
      return 0;

    case t_INTMOD: case t_POLMOD:
      return gcmp1((GEN)x[2]);

    case t_FRAC:
      return gcmp1((GEN)x[1]) && gcmp1((GEN)x[2]);

    case t_FRACN:
      return egalii((GEN)x[1],(GEN)x[2]);

    case t_COMPLEX:
      return gcmp1((GEN)x[1]) && gcmp0((GEN)x[2]);

    case t_PADIC:
      return !valp(x) && gcmp1((GEN)x[4]);

    case t_QUAD:
      return gcmp1((GEN)x[2]) && gcmp0((GEN)x[3]);

    case t_POL:
      return lgef(x)==3 && gcmp1((GEN)x[2]);
  }
  return 0;
}

/* returns 1 whenever the x = -1, 0 otherwise */
int
gcmp_1(GEN x)
{
  pari_sp av;
  long l,y;
  GEN p1;

  switch(typ(x))
  {
    case t_INT:
      return is_pm1(x) && signe(x)== -1;

    case t_REAL:
      if (signe(x) < 0 && expo(x)==0 && (ulong)x[2]==HIGHBIT)
      {
        long i,lx = lg(x);
        for (i=3; i<lx; i++)
          if (x[i]) return 0;
        return 1;
      }
      return 0;

    case t_INTMOD:
      av=avma; y=egalii(addsi(1,(GEN)x[2]), (GEN)x[1]); avma=av; return y;

    case t_FRAC: case t_FRACN:
      l = signe(x[1]);
      return l && l == -signe(x[2]) && !absi_cmp((GEN)x[1],(GEN)x[2]);

    case t_COMPLEX:
      return gcmp_1((GEN)x[1]) && gcmp0((GEN)x[2]);

    case t_QUAD:
      return gcmp_1((GEN)x[2]) && gcmp0((GEN)x[3]);

    case t_PADIC:
      av=avma; y=gegal(addsi(1,(GEN)x[4]), (GEN)x[3]); avma=av; return y;

    case t_POLMOD:
      av=avma; p1=gadd(gun,(GEN)x[2]);
      y = signe(p1) && !gegal(p1,(GEN)x[1]); avma=av; return !y;

    case t_POL:
      return lgef(x)==3 && gcmp_1((GEN)x[2]);
  }
  return 0;
}

/* returns the sign of x - y when it makes sense. 0 otherwise */
int
gcmp(GEN x, GEN y)
{
  long tx, ty, f;
  pari_sp av;

  tx=typ(x); ty=typ(y);
  if (is_intreal_t(tx))
    { if (is_intreal_t(ty)) return mpcmp(x,y); }
  else
  {
    if (tx==t_STR)
    {
      if (ty != t_STR) return 1;
      f = strcmp(GSTR(x),GSTR(y));
      return f > 0? 1
                  : f? -1: 0;
    }
    if (!is_frac_t(tx)) err(typeer,"comparison");
  }
  if (ty == t_STR) return -1;
  if (!is_intreal_t(ty) && !is_frac_t(ty)) err(typeer,"comparison");
  av=avma; y=gneg_i(y); f=gsigne(gadd(x,y)); avma=av; return f;
}

static int
lexcmp_scal_vec(GEN x, GEN y)
{
  long fl;
  if (lg(y)==1) return 1;
  fl = lexcmp(x,(GEN)y[1]);
  if (fl) return fl;
  return -1;
}

static int
lexcmp_vec_mat(GEN x, GEN y)
{
  if (lg(x)==1) return -1;
  return lexcmp_scal_vec(x,y);
}

/* as gcmp for vector/matrices, using lexicographic ordering on components */
int
lexcmp(GEN x, GEN y)
{
  const long tx=typ(x), ty=typ(y);
  long lx,ly,l,fl,i;

  if (!is_matvec_t(tx))
  {
    if (!is_matvec_t(ty)) return gcmp(x,y);
    return  lexcmp_scal_vec(x,y);
  }
  if (!is_matvec_t(ty))
    return -lexcmp_scal_vec(y,x);

  /* x and y are matvec_t */
  if (ty==t_MAT)
  {
    if (tx != t_MAT)
      return lexcmp_vec_mat(x,y);
  }
  else if (tx==t_MAT)
    return -lexcmp_vec_mat(y,x);
   
  /* tx = ty = t_MAT, or x and y are both vect_t */
  lx = lg(x);
  ly = lg(y); l = min(lx,ly);
  for (i=1; i<l; i++)
  {
    fl = lexcmp((GEN)x[i],(GEN)y[i]);
    if (fl) return fl;
  }
  if (lx == ly) return 0;
  return (lx < ly)? -1 : 1;
}

/*****************************************************************/
/*                                                               */
/*                          EQUALITY                             */
/*                returns 1 if x == y, 0 otherwise               */
/*                                                               */
/*****************************************************************/

/* x,y t_POL */
static int
polegal(GEN x, GEN y)
{
  long i, lx = lgef(x);

  if (x[1] != y[1] && (lgef(y) != lx || lx > 3)) return 0;
  for (i = 2; i < lx; i++)
    if (!gegal((GEN)x[i],(GEN)y[i])) return 0;
  return 1;
}

#define MASK(x) (((ulong)(x)) & (TYPBITS | LGBITS))
/* typ(x) = typ(y) = t_VEC/COL/MAT */
static int
vecegal(GEN x, GEN y)
{
  long i;

  if (MASK(x[0]) != MASK(y[0])) return 0;

  i = lg(x)-1;
  if (typ(x) != t_MAT)
  {
    for ( ; i; i--)
      if (! gegal((GEN)x[i],(GEN)y[i]) ) return 0;
    return 1;
  }
  for ( ; i; i--)
    if (! vecegal((GEN)x[i],(GEN)y[i]) ) return 0;
  return 1;
}

static int
gegal_try(GEN x, GEN y)
{
  int i;
  CATCH(CATCH_ALL) {
    CATCH_RELEASE(); return 0;
  } TRY {
    i = gcmp0(gadd(x, gneg_i(y)));
  } ENDCATCH;
  return i;
}

int
gegal(GEN x, GEN y)
{
  pari_sp av;
  long tx;
  long i;
  
  if (x == y) return 1;
  tx = typ(x);
  if (tx==typ(y))
    switch(tx)
    {
      case t_INT:
        return egalii(x,y);

      case t_POL:
        return polegal(x,y);

      case t_COMPLEX:
	return gegal((GEN)x[1],(GEN)y[1]) && gegal((GEN)x[2],(GEN)y[2]);

      case t_INTMOD: case t_POLMOD:
	return gegal((GEN)x[2],(GEN)y[2])
            && (x[1]==y[1] || gegal((GEN)x[1],(GEN)y[1]));

      case t_QFR:
	    if (!gegal((GEN)x[4],(GEN)y[4])) return 0; /* fall through */
      case t_QUAD: case t_QFI:
	return gegal((GEN)x[1],(GEN)y[1])
	    && gegal((GEN)x[2],(GEN)y[2])
	    && gegal((GEN)x[3],(GEN)y[3]);

      case t_FRAC:
	return gegal((GEN)x[1], (GEN)y[1])
            && gegal((GEN)x[2], (GEN)y[2]);

      case t_FRACN: case t_RFRAC: case t_RFRACN:
	av=avma; i=gegal(gmul((GEN)x[1],(GEN)y[2]),gmul((GEN)x[2],(GEN)y[1]));
	avma=av; return i;

      case t_STR:
        return !strcmp(GSTR(x),GSTR(y));

      case t_VEC: case t_COL: case t_MAT:
        return vecegal(x,y);
      case t_VECSMALL:
        if (MASK(x[0]) != MASK(y[0])) return 0;
        for (i = lg(x)-1; i; i--)
          if (x[i] != y[i]) return 0;
        return 1;
    }
  av = avma; i = gegal_try(x, y);
  avma = av; return i;
}
#undef MASK

/*******************************************************************/
/*                                                                 */
/*                          VALUATION                              */
/*             p is either an int or a polynomial.                 */
/*  returns the largest exponent of p dividing x when this makes   */
/*  sense : error for types real, integermod and polymod if p does */
/*  not divide the modulus, q-adic if q!=p.                        */
/*                                                                 */
/*******************************************************************/

static long
minval(GEN x, GEN p, long first, long lx)
{
  long i,k, val = VERYBIGINT;
  for (i=first; i<lx; i++)
  {
    k = ggval((GEN)x[i],p);
    if (k < val) val = k;
  }
  return val;
}

long 
polvaluation(GEN x, GEN *Z)
{
  long v;

  if (!signe(x)) { if (Z) *Z = zeropol(varn(x)); return VERYBIGINT; }
  for (v = 0;; v++)
    if (!isexactzero((GEN)x[2+v])) break;
  if (Z)
  {
    if (!v) *Z = x;
    else
    {
      long i, lz = lgef(x)-v;
      GEN z = cgetg(lz, t_POL);
      z[1] = x[1]; setlgef(z,lz); x += v;
      for (i=2; i<lz; i++) z[i] = x[i];
      *Z = z;
    }
  }
  return v;
}

long
ggval(GEN x, GEN p)
{
  long tx=typ(x), tp=typ(p), vx, v, i, val;
  pari_sp av, limit;
  GEN p1,p2;

  if (isexactzero(x)) return VERYBIGINT;
  if (is_const_t(tx) && tp==t_POL) return 0;
  switch(tx)
  {
    case t_INT:
      if (tp != t_INT) break;
      av=avma; val = pvaluation(x,p, &p1);
      avma=av; return val;

    case t_INTMOD:
      av=avma;
      p1=cgeti(lgefint(x[1]));
      p2=cgeti(lgefint(x[2]));
      if (tp!=t_INT || !mpdivis((GEN)x[1],p,p1)) break;
      if (!mpdivis((GEN)x[2],p,p2)) { avma=av; return 0; }
      val=1; while (mpdivis(p1,p,p1) && mpdivis(p2,p,p2)) val++;
      avma=av; return val;

    case t_PADIC:
      if (tp!=t_INT || !gegal(p,(GEN)x[2])) break;
      return valp(x);

    case t_POLMOD:
      if (tp==t_INT) return ggval((GEN)x[2],p);
      av = avma;
      if (tp!=t_POL || !poldivis((GEN)x[1],p,&p1)) break;
      if (!poldivis((GEN)x[2],p,&p2)) { avma=av; return 0; }
      val=1; while (poldivis(p1,p,&p1)&&poldivis(p2,p,&p2)) val++;
      avma = av; return val;

    case t_POL:
      if (tp==t_POL)
      {
	v=varn(p); vx=varn(x);
	if (vx == v)
	{
	  if ((p>=(GEN)polx && p <= (GEN)(polx+MAXVARN)) || ismonome(p))
            return polvaluation(x, NULL);
	  av = avma; limit=stack_lim(av,1);
	  for (val=0; ; val++)
	  {
	    if (!poldivis(x,p,&x)) break;
            if (low_stack(limit, stack_lim(av,1)))
	    {
	      if(DEBUGMEM>1) err(warnmem,"ggval");
	      x = gerepilecopy(av, x);
	    }
	  }
	  avma = av; return val;
	}
	if (vx > v) return 0;
      }
      else if (tp!=t_INT) break;
      i=2; while (isexactzero((GEN)x[i])) i++;
      return minval(x,p,i,lgef(x));

    case t_SER:
      if (tp!=t_POL && tp!=t_SER && tp!=t_INT) break;
      v=gvar(p); vx=varn(x);
      if (vx==v) return (long)(valp(x)/ggval(p,polx[v]));
      if (vx>v) return 0;
      return minval(x,p,2,lg(x));

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      return ggval((GEN)x[1],p) - ggval((GEN)x[2],p);

    case t_COMPLEX: case t_QUAD: case t_VEC: case t_COL: case t_MAT:
      return minval(x,p,1,lg(x));
  }
  err(talker,"forbidden or conflicting type in gval");
  return 0; /* not reached */
}

/* x is non-zero */
long
svaluation(ulong x, ulong p, ulong *py)
{
  ulong v = 0;
  for(;;)
  {
    if (x%p) { *py = x; return v; }
    v++; x/=p;
  }
}

/* x is a non-zero integer */
long
pvaluation(GEN x, GEN p, GEN *py)
{
  long v;
  pari_sp av, av2;
  GEN p1,p2;

  if (egalii(p,gdeux))
  {
    v = vali(x);
    if (py) *py = shifti(x, -v);
    return v;
  }
  if (is_pm1(p))
  {
    v = (signe(p) < 0 && signe(x) < 0);
    if (py) { *py = v? negi(x): icopy(x); }
    return v;
  }
  if (lgefint(x) == 3)
  {
    if (lgefint(p) == 3)
    {
      ulong y;
      v = svaluation((ulong)x[2],(ulong)p[2], &y);
      if (py)
      {
        *py = utoi(y);
        if (signe(x) < 0) setsigne(*py, -1);
      }
    }
    else
    {
      v = 0;
      if (py) *py = icopy(x);
    }
    return v;
  }
  av = avma; v = 0; (void)new_chunk(lgefint(x));
  av2= avma;
  for(;;)
  {
    p1 = dvmdii(x,p,&p2);
    if (p2 != gzero) { avma=av; if (py) *py = icopy(x); return v; }
    v++; x = p1;
    if ((v & 0xff) == 0) p1 = gerepileuptoint(av2, p1);
  }
}

/*******************************************************************/
/*                                                                 */
/*                       NEGATION: Create -x                       */
/*                                                                 */
/*******************************************************************/

GEN
gneg(GEN x)
{
  long tx=typ(x),lx,i;
  GEN y;

  if (gcmp0(x)) return gcopy(x);
  switch(tx)
  {
    case t_INT: case t_REAL:
      return mpneg(x);

    case t_INTMOD: y=cgetg(3,t_INTMOD);
      icopyifstack(x[1],y[1]);
      y[2] = lsubii((GEN)y[1],(GEN)x[2]);
      break;

    case t_POLMOD: y=cgetg(3,t_POLMOD);
      copyifstack(x[1],y[1]);
      y[2]=lneg((GEN)x[2]); break;

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      y=cgetg(3,tx);
      y[1]=lneg((GEN)x[1]);
      y[2]=lcopy((GEN)x[2]); break;

    case t_PADIC:
      y=cgetp2(x,valp(x));
      y[4]=lsubii((GEN)x[3],(GEN)x[4]);
      break;

    case t_QUAD:
      y=cgetg(4,t_QUAD); copyifstack(x[1],y[1]);
      y[2]=lneg((GEN)x[2]);
      y[3]=lneg((GEN)x[3]); break;

    case t_COMPLEX: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=lneg((GEN)x[i]);
      break;

    case t_POL:
      lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=lneg((GEN)x[i]);
      break;

    case t_SER:
      lx=lg(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=lneg((GEN)x[i]);
      break;

    default:
      err(typeer,"negation");
      return NULL; /* not reached */
  }
  return y;
}

GEN
gneg_i(GEN x)
{
  long tx=typ(x),lx,i;
  GEN y;

  if (gcmp0(x)) return x;
  switch(tx)
  {
    case t_INT: case t_REAL:
      return mpneg(x);

    case t_INTMOD: y=cgetg(3,t_INTMOD); y[1]=x[1];
      y[2] = lsubii((GEN)y[1],(GEN)x[2]);
      break;

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      y=cgetg(3,tx); y[2]=x[2];
      y[1]=(long)gneg_i((GEN)x[1]); break;

    case t_PADIC: y = cgetg(5,t_PADIC); y[2]=x[2]; y[3]=x[3];
      y[1] = evalprecp(precp(x)) | evalvalp(valp(x));
      y[4]=lsubii((GEN)x[3],(GEN)x[4]); break;

    case t_POLMOD: y=cgetg(3,t_POLMOD); y[1]=x[1];
      y[2]=(long)gneg_i((GEN)x[2]); break;

    case t_QUAD: y=cgetg(4,t_QUAD); y[1]=x[1];
      y[2]=(long)gneg_i((GEN)x[2]);
      y[3]=(long)gneg_i((GEN)x[3]); break;

    case t_COMPLEX: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=(long)gneg_i((GEN)x[i]);
      break;

    case t_POL: lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)gneg_i((GEN)x[i]);
      break;

    case t_SER: lx=lg(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)gneg_i((GEN)x[i]);
      break;

    default:
      err(typeer,"negation");
      return NULL; /* not reached */
  }
  return y;
}

/******************************************************************/
/*                                                                */
/*                       ABSOLUTE VALUE                           */
/*    Create abs(x) if x is integer, real, fraction or complex.   */
/*                       Error otherwise.                         */
/*                                                                */
/******************************************************************/

GEN
gabs(GEN x, long prec)
{
  long tx=typ(x), lx, i;
  pari_sp av, tetpil;
  GEN y,p1;

  switch(tx)
  {
    case t_INT: case t_REAL:
      return mpabs(x);

    case t_FRAC: case t_FRACN: y=cgetg(lg(x),tx);
      y[1]=labsi((GEN)x[1]);
      y[2]=labsi((GEN)x[2]); return y;

    case t_COMPLEX:
      av=avma; p1=gnorm(x);
      switch(typ(p1))
      {
        case t_INT:
          if (!carrecomplet(p1, &y)) break;
          return gerepileupto(av, y);
        case t_FRAC:
        case t_FRACN:
        {
          GEN a,b;
          if (!carrecomplet((GEN)p1[1], &a)) break;
          if (!carrecomplet((GEN)p1[2], &b)) break;
          return gerepileupto(av, gdiv(a,b));
        }
      }
      tetpil=avma;
      return gerepile(av,tetpil,gsqrt(p1,prec));

    case t_QUAD:
      av=avma; p1=gmul(x, realun(prec)); tetpil=avma;
      return gerepile(av,tetpil,gabs(p1,prec));

    case t_POL:
      lx=lgef(x); if (lx<=2) return gcopy(x);
      p1=(GEN)x[lx-1];
      switch(typ(p1))
      {
	case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
	  if (gsigne(p1)<0) return gneg(x);
      }
      return gcopy(x);

   case t_SER:
     if (valp(x) || !signe(x) || lg(x)<3)
       err(talker,"abs is not analytic at 0");
     if (gsigne((GEN) x[2])<0) return gneg(x);
     return gcopy(x);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++)
        y[i]=(long)gabs((GEN)x[i],prec);
      return y;
  }
  err(typeer,"gabs");
  return NULL; /* not reached */
}

GEN
gmax(GEN x, GEN y)
{
  if (gcmp(x,y)>0) y=x; return gcopy(y);
}

GEN
gmin(GEN x, GEN y)
{
  if (gcmp(x,y)<0) y=x; return gcopy(y);
}

GEN
vecmax(GEN x)
{
  long tx=typ(x),lx,lx2,i,j;
  GEN *p1,s;

  if (!is_matvec_t(tx)) return gcopy(x);
  lx=lg(x); if (lx==1) return stoi(-VERYBIGINT);
  if (tx!=t_MAT)
  {
    s=(GEN)x[1];
    for (i=2; i<lx; i++)
      if (gcmp((GEN)x[i],s) > 0) s=(GEN)x[i];
  }
  else
  {
    lx2 = lg(x[1]);
    if (lx2==1) return stoi(-VERYBIGINT);
    s=gmael(x,1,1); i=2;
    for (j=1; j<lx; j++)
    {
      p1 = (GEN *) x[j];
      for (; i<lx2; i++)
	if (gcmp(p1[i],s) > 0) s=p1[i];
      i=1;
    }
  }
  return gcopy(s);
}

GEN
vecmin(GEN x)
{
  long tx=typ(x),lx,lx2,i,j;
  GEN *p1,s;

  if (!is_matvec_t(tx)) return gcopy(x);
  lx=lg(x); if (lx==1) return stoi(VERYBIGINT);
  if (tx!=t_MAT)
  {
    s=(GEN)x[1];
    for (i=2; i<lx; i++)
      if (gcmp((GEN)x[i],s) < 0) s=(GEN)x[i];
  }
  else
  {
    lx2 = lg(x[1]);
    if (lx2==1) return stoi(VERYBIGINT);
    s=gmael(x,1,1); i=2;
    for (j=1; j<lx; j++)
    {
      p1 = (GEN *) x[j];
      for (; i<lx2; i++)
	if (gcmp(p1[i],s) < 0) s=p1[i];
      i=1;
    }
  }
  return gcopy(s);
}

/*******************************************************************/
/*                                                                 */
/*                      AFFECT long --> GEN                        */
/*         affect long s to GEN x. Useful for initialization.      */
/*                                                                 */
/*******************************************************************/

static void
padicaff0(GEN x)
{
  if (signe(x[4]))
  {
    setvalp(x, valp(x)|precp(x));
    affsi(0,(GEN)x[4]);
  }
}

void
gaffsg(long s, GEN x)
{
  long l,i,v;

  switch(typ(x))
  {
    case t_INT:
      affsi(s,x); break;

    case t_REAL:
      affsr(s,x); break;

    case t_INTMOD:
      modsiz(s,(GEN)x[1],(GEN)x[2]); break;

    case t_FRAC: case t_FRACN:
      affsi(s,(GEN)x[1]); affsi(1,(GEN)x[2]); break;

    case t_COMPLEX:
      gaffsg(s,(GEN)x[1]); gaffsg(0,(GEN)x[2]); break;

    case t_PADIC:
    {
      GEN y;
      if (!s) { padicaff0(x); break; }
      v = pvaluation(stoi(s), (GEN)x[2], &y);
      setvalp(x,v); modiiz(y,(GEN)x[3],(GEN)x[4]);
      break;
    }

    case t_QUAD:
      gaffsg(s,(GEN)x[2]); gaffsg(0,(GEN)x[3]); break;

    case t_POLMOD:
      gaffsg(s,(GEN)x[2]); break;

    case t_POL:
      v=varn(x);
      if (!s) x[1]=evallgef(2) | evalvarn(v);
      else
      {
        x[1]=evalsigne(1) | evallgef(3) | evalvarn(v);
	gaffsg(s,(GEN)x[2]);
      }
      break;

    case t_SER:
      v=varn(x); gaffsg(s,(GEN)x[2]); l=lg(x);
      if (!s)
        x[1] = evalvalp(l-2) | evalvarn(v);
      else
        x[1] = evalsigne(1) | evalvalp(0) | evalvarn(v);
      for (i=3; i<l; i++) gaffsg(0,(GEN)x[i]);
      break;

    case t_RFRAC: case t_RFRACN:
      gaffsg(s,(GEN)x[1]); gaffsg(1,(GEN)x[2]); break;

    case t_VEC: case t_COL: case t_MAT:
      if (lg(x)!=2) err(operi,"",stoi(s),x);
      gaffsg(s,(GEN)x[1]); break;

    default: err(operf,"",stoi(s),x);
  }
}

/*******************************************************************/
/*                                                                 */
/*                     GENERIC AFFECTATION                         */
/*         Affect the content of x to y, whenever possible         */
/*                                                                 */
/*******************************************************************/
void
gaffect(GEN x, GEN y)
{
  long i, j, k, l, v, vy, lx, ly, tx, ty;
  pari_sp av;
  GEN p1,num,den;


  tx=typ(x); ty=typ(y); lx=lg(x); ly=lg(y);
  if (is_scalar_t(tx))
  {
    if (is_scalar_t(ty))
    {
      switch(tx)
      {
	case t_INT:
	  switch(ty)
	  {
	    case t_INT:
	      /* y = gzero, gnil, gun or gdeux */
	      if (is_universal_constant(y))
	      {
		if (y==gzero) err(overwriter,"gaffect (gzero)");
		if (y==gun)   err(overwriter,"gaffect (gun)");
		if (y==gdeux) err(overwriter,"gaffect (gdeux)");
		err(overwriter,"gaffect (gnil)");
	      }
	      affii(x,y); break;

	    case t_REAL:
              if (y ==  gpi) err(overwriter,"gaffect (gpi)");
              if (y==geuler) err(overwriter,"gaffect (geuler)");
	      affir(x,y); break;

	    case t_INTMOD:
	      modiiz(x,(GEN)y[1],(GEN)y[2]); break;

	    case t_FRAC:
	      if (y == ghalf) err(overwriter,"gaffect (ghalf)");
	    case t_FRACN:
	      affii(x,(GEN)y[1]); affsi(1,(GEN)y[2]); break;

	    case t_COMPLEX:
	      if (y == gi) err(overwriter,"gaffect (gi)");
	      gaffect(x,(GEN)y[1]); gaffsg(0,(GEN)y[2]); break;

	    case t_PADIC:
              if (!signe(x)) { padicaff0(y); break; }
	      av=avma;
	      setvalp(y, pvaluation(x,(GEN)y[2],&p1));
	      modiiz(p1,(GEN)y[3],(GEN)y[4]);
	      avma=av; break;

	    case t_QUAD:
	      gaffect(x,(GEN)y[2]); gaffsg(0,(GEN)y[3]); break;

	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;

	    default: err(operf,"",x,y);
	  }
	  break;
	
	case t_REAL:
	  switch(ty)
	  {
	    case t_REAL:
	      affrr(x,y); break;

	    case t_COMPLEX:
	      gaffect(x,(GEN)y[1]); gaffsg(0,(GEN)y[2]); break;

	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;

	    case t_INT: case t_INTMOD: case t_FRAC:
	    case t_FRACN: case t_PADIC: case t_QUAD:
              err(operf,"",x,y);

	    default: err(operf,"",x,y);
	  }
	  break;
	
	case t_INTMOD:
	  switch(ty)
	  {
	    case t_INTMOD:
	      if (!divise((GEN)x[1],(GEN)y[1]))
                err(operi,"",x,y);
	      modiiz((GEN)x[2],(GEN)y[1],(GEN)y[2]); break;

	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;

	    default: err(operf,"",x,y);
	  }
	  break;

	case t_FRAC:
	  switch(ty)
	  {
	    case t_INT:
	      if (! mpdivis((GEN)x[1],(GEN)x[2],y))
                err(operi,"",x,y);
	      break;

	    case t_REAL:
	      diviiz((GEN)x[1],(GEN)x[2],y); break;
	
	    case t_INTMOD:
	      av=avma; p1=mpinvmod((GEN)x[2],(GEN)y[1]);
	      modiiz(mulii((GEN)x[1],p1),(GEN)y[1],(GEN)y[2]);
	      avma=av; break;

	    case t_FRAC: case t_FRACN:
	      affii((GEN)x[1],(GEN)y[1]);
	      affii((GEN)x[2],(GEN)y[2]);
	      break;
	
	    case t_COMPLEX:
	      gaffect(x,(GEN)y[1]); gaffsg(0,(GEN)y[2]); break;

	    case t_PADIC:
	      if (!signe(x[1])) { padicaff0(y); break; }
	      av=avma; num=(GEN)x[1]; den=(GEN)x[2];
	      v = pvaluation(num, (GEN) y[2], &num);
	      if (!v) v = -pvaluation(den,(GEN)y[2],&den);
	      p1=mulii(num,mpinvmod(den,(GEN)y[3]));
	      modiiz(p1,(GEN)y[3],(GEN)y[4]); avma=av;
	      setvalp(y,v); break;

	    case t_QUAD:
	      gaffect(x,(GEN)y[2]); gaffsg(0,(GEN)y[3]); break;
	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;
	    default: err(operf,"",x,y);
	  }
	  break;

	case t_FRACN:
	  switch(ty)
	  {
	    case t_INT:
	      if (! mpdivis((GEN)x[1],(GEN)x[2],y)) err(operi,"",x,y);
	      break;

	    case t_REAL:
	      diviiz((GEN)x[1],(GEN)x[2],y); break;
	    case t_INTMOD:
	      av=avma; gaffect(gred(x),y); avma=av; break;
	    case t_FRAC:
	      gredz(x,y); break;
	    case t_FRACN:
	      affii((GEN)x[1],(GEN)y[1]);
	      affii((GEN)x[2],(GEN)y[2]); break;
	    case t_COMPLEX:
	      gaffect(x,(GEN)y[1]); gaffsg(0,(GEN)y[2]); break;
	    case t_PADIC:
	      if (!signe(x[1])) { padicaff0(y); break; }
	      av=avma; num=(GEN)x[1]; den=(GEN)x[2];
	      v =  pvaluation(num,(GEN)y[2],&num)
	         - pvaluation(den,(GEN)y[2],&den);
	      p1=mulii(num,mpinvmod(den,(GEN)y[3]));
	      modiiz(p1,(GEN)y[3],(GEN)y[4]); avma=av;
	      setvalp(y,v); break;

	    case t_QUAD:
	      gaffect(x,(GEN)y[2]); gaffsg(0,(GEN)y[3]); break;
	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;
	    default: err(operf,"",x,y);
	  }
	  break;
	
	case t_COMPLEX:
	  switch(ty)
	  {
	    case t_INT: case t_REAL: case t_INTMOD:
	    case t_FRAC: case t_FRACN: case t_PADIC: case t_QUAD:
	      if (!gcmp0((GEN)x[2])) err(operi,"",x,y);
	      gaffect((GEN)x[1],y); break;
	
	    case t_COMPLEX:
	      gaffect((GEN)x[1],(GEN)y[1]);
	      gaffect((GEN)x[2],(GEN)y[2]);
	      break;

	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;

	    default: err(operf,"",x,y);
	  }
	  break;
	
	case t_PADIC:
	  switch(ty)
	  {
	    case t_INTMOD:
	      if (valp(x)<0) err(operi,"",x,y);
	      av=avma;
	      v = pvaluation((GEN)y[1],(GEN)x[2],&p1);
              k = signe(x[4])? (precp(x)+valp(x)): valp(x)+1;
	      if (!gcmp1(p1) || v > k) err(operi,"",x,y);
	      modiiz(gtrunc(x),(GEN)y[1],(GEN)y[2]); avma=av; break;
	
	    case t_PADIC:
	      if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"",x,y);
	      modiiz((GEN)x[4],(GEN)y[3],(GEN)y[4]);
	      setvalp(y,valp(x)); break;
	
	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;

	    default: err(operf,"",x,y);
	  }
	  break;
	
	case t_QUAD:
	  switch(ty)
	  {
	    case t_INT: case t_INTMOD: case t_FRAC:
	    case t_FRACN: case t_PADIC:
	      if (!gcmp0((GEN)x[3])) err(operi,"",x,y);
	      gaffect((GEN)x[2],y); break;

	    case t_REAL:
	      av=avma; p1=co8(x,ly); gaffect(p1,y); avma=av; break;
	    case t_COMPLEX:
	      ly=precision(y);
	      if (ly)
	      {
		av=avma; p1=co8(x,ly); gaffect(p1,y); avma=av;
	      }
	      else
	      {
                if (!gcmp0((GEN)x[3])) err(operi,"",x,y);
		gaffect((GEN)x[2],y);
	      }
	      break;

	    case t_QUAD:
	      if (! gegal((GEN)x[1],(GEN)y[1])) err(operi,"",x,y);
	      affii((GEN)x[2],(GEN)y[2]);
	      affii((GEN)x[3],(GEN)y[3]);
	      break;
	    case t_POLMOD:
	      gaffect(x,(GEN)y[2]); break;
	    default: err(operf,"",x,y);
	  }
	  break;

	case t_POLMOD:
	  if (ty!=t_POLMOD) err(operf,"",x,y);
	  if (! gdivise((GEN)x[1],(GEN)y[1])) err(operi,"",x,y);
	  gmodz((GEN)x[2],(GEN)y[1],(GEN)y[2]); break;

        default: err(operf,"",x,y);
      }
      return;
    }

    /* here y is not scalar */
    switch(ty)
    {
      case t_POL:
	v=varn(y);
	if (y==polun[v] || y==polx[v])
	  err(talker,"trying to overwrite a universal polynomial");
	gaffect(x,(GEN)y[2]);
	for (i=3; i<ly; i++) gaffsg(0,(GEN)y[i]);
	if (gcmp0(x)) y[1]=evallgef(2)+evalvarn(v);
	else y[1]=evalsigne(1)+evallgef(3)+evalvarn(v);
	break;

      case t_SER:
	v=varn(y); gaffect(x,(GEN)y[2]);
	if (gcmp0(x))
          y[1] = evalvalp(ly-2) | evalvarn(v);
	else
	  y[1] = evalsigne(1) | evalvalp(0) | evalvarn(v);
        for (i=3; i<ly; i++) gaffsg(0,(GEN)y[i]);
	break;

      case t_RFRAC: case t_RFRACN:
	gaffect(x,(GEN)y[1]); gaffsg(1,(GEN)y[2]); break;

      default: err(operf,"",x,y);
    }
    return;
  }

  if (is_const_t(ty)) {
    entree *varnum, *varden;
    long vnum, vden;
    GEN num, den;
    if (tx == t_POL) {
      vnum = varn(x); varnum = varentries[ordvar[vnum]];
      if (varnum) {
        x = geval(x); tx = typ(x);
        if (tx != t_POL || varn(x) != vnum) { gaffect(x, y); return; }
      }	  
    } else if (is_rfrac_t(tx)) {
      num = (GEN)x[1]; vnum = gvar(num); varnum = varentries[ordvar[vnum]];
      den = (GEN)x[2]; vden = gvar(den); varden = varentries[ordvar[vden]];
      if (varnum && varden) {
        vnum = min(vnum, vden);
        x = geval(x); tx = typ(x);
        if (!is_rfrac_t(tx) || gvar(x) != vnum) { gaffect(x, y); return; }
      }
    }
    err(operf,"",x,y);
  }
  
  switch(tx)
  {
    case t_POL:
      v=varn(x);
      switch(ty)
      {
	case t_POL:
	  vy=varn(y); if (vy>v) err(operf,"",x,y);
	  if (vy==v)
	  {
	    l=lgef(x); if (l>ly) err(operi,"",x,y);
	    y[1]=x[1]; for (i=2; i<l; i++) gaffect((GEN)x[i],(GEN)y[i]);
	  }
	  else
	  {
	    gaffect(x,(GEN)y[2]);
	    for (i=3; i<ly; i++) gaffsg(0,(GEN)y[i]);
	    if (signe(x)) y[1]=evalsigne(1)+evallgef(3)+evalvarn(vy);
	    else y[1]=evallgef(2)+evalvarn(vy);
	  }
	  break;
	
	case t_SER:
	  vy=varn(y); if (vy>v) err(operf,"",x,y);
	  if (!signe(x)) { gaffsg(0,y); return; }
	  if (vy==v)
	  {
	    i=gval(x,v); y[1]=evalvarn(v) | evalvalp(i) | evalsigne(1);
	    k=lgef(x)-i; if (k>ly) k=ly;
	    for (j=2; j<k; j++) gaffect((GEN)x[i+j],(GEN)y[j]);
	    for (   ; j<ly; j++) gaffsg(0,(GEN)y[j]);
	  }
	  else
	  {
	    gaffect(x,(GEN)y[2]);
	    if (!signe(x))
              y[1] = evalvalp(ly-2) | evalvarn(vy);
	    else
	      y[1] = evalsigne(1) | evalvalp(0) | evalvarn(vy);
            for (i=3; i<ly; i++) gaffsg(0,(GEN)y[i]);
	  }
	  break;
	
	case t_POLMOD:
	  gmodz(x,(GEN)y[1],(GEN)y[2]); break;

	case t_RFRAC: case t_RFRACN:
	  gaffect(x,(GEN)y[1]); gaffsg(1,(GEN)y[2]); break;

        default: err(operf,"",x,y);
      }
      break;

    case t_SER:
      if (ty!=t_SER) err(operf,"",x,y);
      v=varn(x); vy=varn(y); if (vy>v) err(operf,"",x,y);
      if (vy==v)
      {
	y[1]=x[1]; k=lx; if (k>ly) k=ly;
        for (i=2; i< k; i++) gaffect((GEN)x[i],(GEN)y[i]);
        for (   ; i<ly; i++) gaffsg(0,(GEN)y[i]);
      }
      else
      {
	gaffect(x,(GEN)y[2]);
	if (!signe(x))
          y[1] = evalvalp(ly-2) | evalvarn(vy);
	else
	  y[1] = evalsigne(1) | evalvalp(0) | evalvarn(vy);
        for (i=3; i<ly; i++) gaffsg(0,(GEN)y[i]);
      }
      break;

    case t_RFRAC: case t_RFRACN:
      switch(ty)
      {
	case t_POL: case t_VEC: case t_COL: case t_MAT:
	  err(operf,"",x,y);

	case t_POLMOD:
	  av=avma; p1=ginvmod((GEN)x[2],(GEN)y[1]);
	  gmodz(gmul((GEN)x[1],p1),(GEN)y[1],(GEN)y[2]);
	  avma=av; break;

	case t_SER:
	  gdivz((GEN)x[1],(GEN)x[2],y); break;
	
	case t_RFRAC:
	  if (tx==t_RFRACN) gredz(x,y);
	  else
	  {
	    gaffect((GEN)x[1],(GEN)y[1]);
	    gaffect((GEN)x[2],(GEN)y[2]);
	  }
	  break;
	
	case t_RFRACN:
	  gaffect((GEN)x[1],(GEN)y[1]);
	  gaffect((GEN)x[2],(GEN)y[2]); break;
	
        default: err(operf,"",x,y);
      }
      break;

    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      if (ty != tx || ly != lx) err(operi,"",x,y);
      for (i=1; i<lx; i++) gaffect((GEN)x[i],(GEN)y[i]);
      break;

    default: err(operf,"",x,y);
  }
}

/*******************************************************************/
/*                                                                 */
/*           CONVERSION QUAD --> REAL, COMPLEX OR P-ADIC           */
/*                                                                 */
/*******************************************************************/

GEN
co8(GEN x, long prec)
{
  pari_sp av=avma, tetpil;
  GEN p1, p = (GEN) x[1];

  p1 = subii(sqri((GEN)p[3]), shifti((GEN)p[2],2));
  if (signe(p1) > 0)
  {
    p1 = subri(gsqrt(p1,prec), (GEN)p[3]);
    setexpo(p1, expo(p1)-1);
  }
  else
  {
    p1 = gsub(gsqrt(p1,prec), (GEN)p[3]);
    p1[1] = lmul2n((GEN)p1[1],-1);
    setexpo(p1[2], expo(p1[2])-1);
  }/* p1 = (-b + sqrt(D)) / 2 */
  p1 = gmul((GEN)x[3],p1); tetpil=avma;
  return gerepile(av,tetpil,gadd((GEN)x[2],p1));
}

GEN
cvtop(GEN x, GEN p, long l)
{
  GEN p1,p2,p3;
  long n;
  pari_sp av, tetpil;

  if (typ(p)!=t_INT)
    err(talker,"not an integer modulus in cvtop or gcvtop");
  if (gcmp0(x)) return ggrandocp(p,l);
  switch(typ(x))
  {
    case t_INT:
      return gadd(x,ggrandocp(p,ggval(x,p)+l));

    case t_INTMOD:
      n=ggval((GEN)x[1],p); if (n>l) n=l;
      return gadd((GEN)x[2],ggrandocp(p,n));

    case t_FRAC: case t_FRACN:
      n = ggval((GEN)x[1],p) - ggval((GEN)x[2],p);
      return gadd(x,ggrandocp(p,n+l));

    case t_COMPLEX:
      av=avma; p1=gsqrt(gaddgs(ggrandocp(p,l),-1),0);
      p1=gmul(p1,(GEN)x[2]); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,(GEN)x[1]));

    case t_PADIC:
      return gprec(x,l);

    case t_QUAD:
      av=avma; p1=(GEN)x[1]; p3=gmul2n((GEN)p1[3],-1);
      p2=gsub(gsqr(p3),(GEN)p1[2]);
      switch(typ(p2))
      {
	case t_INT:
	  n=ggval(p2,p); p2=gadd(p2,ggrandocp(p,n+l)); break;

	case t_INTMOD: case t_PADIC:
	  break;

	case t_FRAC: case t_FRACN:
	  n = ggval((GEN)p2[1],p) - ggval((GEN)p2[2],p);
	  p2=gadd(p2,ggrandocp(p,n+l)); break;

	default: err(operi,"",x,x);
      }
      p2=gsqrt(p2,0); p1=gmul((GEN)x[3],gsub(p2,p3)); tetpil=avma;
      return gerepile(av,tetpil,gadd((GEN)x[2],p1));

  }
  err(typeer,"cvtop");
  return NULL; /* not reached */
}

GEN
gcvtop(GEN x, GEN p, long r)
{
  long i,lx, tx=typ(x);
  GEN y;

  if (is_const_t(tx)) return cvtop(x,p,r);
  switch(tx)
  {
    case t_POL:
      lx=lgef(x); y=cgetg(lx,t_POL); y[1]=x[1];
      for (i=2; i<lx; i++)
	y[i]=(long)gcvtop((GEN)x[i],p,r);
      break;

    case t_SER:
      lx=lg(x); y=cgetg(lx,t_SER); y[1]=x[1];
      for (i=2; i<lx; i++)
	y[i]=(long)gcvtop((GEN)x[i],p,r);
      break;

    case t_POLMOD: case t_RFRAC: case t_RFRACN:
    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++)
	y[i]=(long)gcvtop((GEN)x[i],p,r);
      break;

    default: err(typeer,"gcvtop");
      return NULL; /* not reached */
  }
  return y;
}

long
gexpo(GEN x)
{
  long tx=typ(x), lx, e, i, y;
  pari_sp av;

  switch(tx)
  {
    case t_INT:
      return expi(x);

    case t_FRAC: case t_FRACN:
      if (!signe(x[1])) return -HIGHEXPOBIT;
      return expi((GEN)x[1]) - expi((GEN)x[2]);

    case t_REAL:
      return expo(x);

    case t_COMPLEX:
      e = gexpo((GEN)x[1]);
      y = gexpo((GEN)x[2]); return max(e,y);

    case t_QUAD:
      av=avma; e = gexpo(co8(x,3)); avma=av; return e;

    case t_POL: case t_SER: case t_VEC: case t_COL: case t_MAT:
      lx=(tx==t_POL)? lgef(x): lg(x);
      y = -HIGHEXPOBIT;
      for (i=lontyp[tx]; i<lx; i++) { e=gexpo((GEN)x[i]); if (e>y) y=e; }
      return y;
  }
  err(typeer,"gexpo");
  return 0; /* not reached */
}

long
sizedigit(GEN x)
{
  return gcmp0(x)? 0: (long) ((gexpo(x)+1) * L2SL10) + 1;
}

/* normalize series. avma is not updated */
GEN
normalize(GEN x)
{
  long i, lx = lg(x);
  GEN y;

  if (typ(x) != t_SER) err(typeer,"normalize");
  if (lx==2) { setsigne(x,0); return x; }
  if (! isexactzero((GEN)x[2])) { setsigne(x,1); return x; }
  for (i=3; i<lx; i++)
    if (! isexactzero((GEN)x[i]))
    {
      i -= 2; y = x + i;
      y[1] = evalsigne(1) | evalvalp(valp(x)+i) | evalvarn(varn(x));
      y[0] = evaltyp(t_SER) | evallg(lx-i); /* don't swap these lines ! */
      stackdummy(x, i); return y;
    }
  return zeroser(varn(x),lx-2);
}

GEN
normalizepol_i(GEN x, long lx)
{
  long i;
  for (i=lx-1; i>1; i--)
    if (! isexactzero((GEN)x[i])) break;
  setlgef(x,i+1);
  for (; i>1; i--)
    if (! gcmp0((GEN)x[i]) ) { setsigne(x,1); return x; }
  setsigne(x,0); return x;
}

/* Normalize polynomial x in place. See preceding comment */
GEN
normalizepol(GEN x)
{
  if (typ(x)!=t_POL) err(typeer,"normalizepol");
  return normalizepol_i(x, lgef(x));
}

int
gsigne(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL:
      return signe(x);

    case t_FRAC: case t_FRACN:
      return (signe(x[2])>0) ? signe(x[1]) : -signe(x[1]);
  }
  err(typeer,"gsigne");
  return 0; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                              LISTS                              */
/*                                                                 */
/*******************************************************************/

GEN
listcreate(long n)
{
  GEN list;

  if (n<0) err(talker,"negative length in listcreate");
  n += 2;
  if (n & ~LGEFBITS) err(talker,"list too long (max = %ld)",LGEFBITS-2);
  list = cgetg(n,t_LIST);
  list[1] = evallgef(2); return list;
}

static void
listaffect(GEN list, long index, GEN object)
{
  if (index < lgef(list) && isclone(list[index])) gunclone((GEN)list[index]);
  list[index] = lclone(object);
}

void
listkill(GEN list)
{
  long l, i;

  if (typ(list) != t_LIST) err(typeer,"listkill");
  l = lgef(list);
  for (i=2; i<l; i++)
    if (isclone(list[i])) gunclone((GEN)list[i]);
  list[1] = evallgef(2);
}

GEN
listput(GEN list, GEN object, long index)
{
  long l = lgef(list);

  if (typ(list) != t_LIST) err(typeer,"listput");
  if (index < 0) err(talker,"negative index (%ld) in listput", index);
  if (!index || index >= l-1)
  {
    index = l-1; l++;
    if (l > lg(list))
      err(talker,"no more room in this list (size %ld)", lg(list)-2);
  }
  listaffect(list, index+1, object);
  list[1] = evallgef(l);
  return (GEN)list[index+1];
}

GEN
listinsert(GEN list, GEN object, long index)
{
  long l = lgef(list), i;

  if (typ(list) != t_LIST) err(typeer,"listinsert");
  if (index <= 0 || index > l-1) err(talker,"bad index in listinsert");
  l++; if (l > lg(list)) err(talker,"no more room in this list");

  for (i=l-2; i > index; i--) list[i+1] = list[i];
  list[index+1] = lclone(object);
  list[1] = evallgef(l);
  return (GEN)list[index+1];
}

GEN
gtolist(GEN x)
{
  long tx, lx, i;
  GEN list;

  if (!x) { list = cgetg(2, t_LIST); list[1] = evallgef(2); return list; }

  tx = typ(x);
  lx = (tx==t_LIST)? lgef(x): lg(x);
  switch(tx)
  {
    case t_VEC: case t_COL:
      lx++; x--; /* fall through */
    case t_LIST:
      list = cgetg(lx,t_LIST);
      for (i=2; i<lx; i++) list[i] = lclone((GEN)x[i]);
      break;
    default: err(typeer,"gtolist");
      return NULL; /* not reached */
  }
  list[1] = evallgef(lx); return list;
}

GEN
listconcat(GEN list1, GEN list2)
{
  long i, l1, lx;
  GEN list;

  if (typ(list1) != t_LIST || typ(list2) != t_LIST) err(typeer,"listconcat");
  l1 = lgef(list1)-2;
  lx = l1 + lgef(list2);
  list = listcreate(lx-2);
  for (i=2; i<=l1+1; i++) listaffect(list, i, (GEN)list1[i]);
  for (   ; i<lx;    i++) listaffect(list, i, (GEN)list2[i-l1]);
  list[1] = evallgef(lx); return list;
}

GEN
listsort(GEN list, long flag)
{
  long i, c = list[1], lx = lgef(list)-1;
  pari_sp av = avma;
  GEN perm, vec, l;

  if (typ(list) != t_LIST) err(typeer,"listsort");
  vec = list+1;
  vec[0] = evaltyp(t_VEC) | evallg(lx);
  perm = sindexsort(vec);
  list[1] = c; l = cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) l[i] = vec[perm[i]];
  if (flag)
  {
    c=1; vec[1] = l[1];
    for (i=2; i<lx; i++)
      if (!gegal((GEN)l[i], (GEN)vec[c]))
        vec[++c] = l[i];
      else
        if (isclone(l[i])) gunclone((GEN)l[i]);
    setlgef(list, c+2);
  }
  else
    for (i=1; i<lx; i++) vec[i] = l[i];

  avma = av; return list;
}
