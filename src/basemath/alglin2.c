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
/**                         LINEAR ALGEBRA                         **/
/**                         (second part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

/*******************************************************************/
/*                                                                 */
/*                   CHARACTERISTIC POLYNOMIAL                     */
/*                                                                 */
/*******************************************************************/

GEN
charpoly0(GEN x, int v, long flag)
{
  if (v<0) v = 0;
  switch(flag)
  {
    case 0: return caradj(x,v,0);
    case 1: return caract(x,v);
    case 2: return carhess(x,v);
  }
  err(flagerr,"charpoly"); return NULL; /* not reached */
}

static GEN
caract2_i(GEN p, GEN x, int v, GEN (subres_f)(GEN,GEN,GEN*))
{
  gpmem_t av = avma;
  long d;
  GEN p1, p2 = leading_term(p);

  if (!signe(x)) return gpowgs(polx[v], degpol(p));
  if (typ(x) != t_POL) x = scalarpol(x,v);
  x = gneg_i(x); x[2] = ladd((GEN)x[2], polx[MAXVARN]);
  p1=subres_f(p, x, NULL);
  if (typ(p1) == t_POL && varn(p1)==MAXVARN)
    setvarn(p1,v);
  else
    p1 = gsubst(p1,MAXVARN,polx[v]);

  if (!gcmp1(p2) && (d=degpol(x)) > 0) p1 = gdiv(p1, gpowgs(p2,d));
  return gerepileupto(av,p1);
}

/* return caract(Mod(x,p)) in variable v */
GEN
caract2(GEN p, GEN x, int v)
{
  return caract2_i(p,x,v, subresall);
}
GEN
caractducos(GEN p, GEN x, int v)
{
  return caract2_i(p,x,v, (GEN (*)(GEN,GEN,GEN*))resultantducos);
}

/* characteristic pol. Easy cases. Return NULL in case it's not so easy. */
static GEN
easychar(GEN x, int v, GEN *py)
{
  gpmem_t av;
  long lx;
  GEN p1,p2;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD:
    case t_FRAC: case t_FRACN: case t_PADIC:
      p1=cgetg(4,t_POL);
      p1[1]=evalsigne(1) | evallgef(4) | evalvarn(v);
      p1[2]=lneg(x); p1[3]=un;
      if (py)
      {
	p2=cgetg(2,t_MAT);
	p2[1]=lgetg(2,t_COL);
	coeff(p2,1,1)=lcopy(x);
	*py=p2;
      }
      return p1;

    case t_COMPLEX: case t_QUAD:
      if (py) err(typeer,"easychar");
      p1 = cgetg(5,t_POL);
      p1[1] = evalsigne(1) | evallgef(5) | evalvarn(v);
      p1[2] = lnorm(x); av = avma;
      p1[3] = lpileupto(av, gneg(gtrace(x)));
      p1[4] = un; return p1;

    case t_POLMOD:
      if (py) err(typeer,"easychar");
      return caract2((GEN)x[1], (GEN)x[2], v);

    case t_MAT:
      lx=lg(x);
      if (lx==1)
      {
	if (py) *py = cgetg(1,t_MAT);
	return polun[v];
      }
      if (lg(x[1]) != lx) break;
      return NULL;
  }
  err(mattype1,"easychar");
  return NULL; /* not reached */
}

GEN
caract(GEN x, int v)
{
  long k;
  gpmem_t av=avma;
  GEN  p1,p2,p3,p4,x_k;

  if ((p1 = easychar(x,v,NULL))) return p1;

  p1 = gzero; p2 = gun;
  n = lg(x)-1; if (n&1) p2 = negi(p2);
  x_k = dummycopy(polx[v]);
  p4 = cgetg(3,t_RFRACN); p4[2] = (long)x_k;
  for (k=0; k<=n; k++)
  {
    p3 = det(gsub(gscalmat(stoi(k),n), x));
    p4[1] = lmul(p3,p2); x_k[2] = lstoi(-k);
    p1 = gadd(p4,p1);
    if (k == n) break;

    p2 = gdivgs(gmulsg(k-n,p2),k+1);
  }
  return gerepileupto(av, gdiv((GEN)p1[1], mpfact(n)));
}

GEN
caradj0(GEN x, long v)
{
  return caradj(x,v,NULL);
}

/* Using traces: return the characteristic polynomial of x (in variable v).
 * If py != NULL, the adjoint matrix is put there.
 */
GEN
caradj(GEN x, long v, GEN *py)
{
  gpmem_t av,tetpil;
  long i,j,k,l;
  GEN p,y,t,*gptr[2];

  if ((p = easychar(x,v,py))) return p;

  l=lg(x);
  if (l==1) { p=polun[v]; if (py) *py=gcopy(x); return p; }
  if (l==2) { p=gsub(polx[v],gtrace(x)); if (py) *py=idmat(1); return p; }

  p=cgetg(l+2,t_POL); p[1]=evalsigne(1) | evallgef(l+2) | evalvarn(v);
  av=avma; t=gtrace(x); tetpil=avma;
  t=gerepile(av,tetpil,gneg(t));
  p[l]=(long)t; p[l+1]=un;

  av=avma; y=cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    y[j]=lgetg(l,t_COL);
    for (i=1; i<l; i++)
      coeff(y,i,j) = (i==j) ? ladd(gcoeff(x,i,j),t) : coeff(x,i,j);
  }

  for (k=2; k<l-1; k++)
  {
    GEN z=gmul(x,y);

    t=gtrace(z); tetpil=avma;
    t=gdivgs(t,-k); y=cgetg(l,t_MAT);
    for (j=1; j<l; j++)
    {
      y[j]=lgetg(l,t_COL);
      for (i=1;i<l;i++)
	coeff(y,i,j) = (i==j)? ladd(gcoeff(z,i,i),t): lcopy(gcoeff(z,i,j));
    }
    gptr[0]=&y; gptr[1]=&t;
    gerepilemanysp(av,tetpil,gptr,2);
    p[l-k+1]=(long)t; av=avma;
  }

  t=gzero;
  for (i=1; i<l; i++)
    t=gadd(t,gmul(gcoeff(x,1,i),gcoeff(y,i,1)));
  tetpil=avma; t=gneg(t);

  if (py)
  {
    *py = (l&1) ? gneg(y) : gcopy(y);
    gptr[0] = &t; gptr[1] = py;
    gerepilemanysp(av,tetpil,gptr,2);
    p[2]=(long)t;
  }
  else p[2]=lpile(av,tetpil,t);
  i = gvar2(p);
  if (i == v) err(talker,"incorrect variable in caradj");
  if (i < v) p = poleval(p, polx[v]); 
  return p;
}

GEN
adj(GEN x)
{
  GEN y;
  caradj(x,MAXVARN,&y); return y;
}

/*******************************************************************/
/*                                                                 */
/*                       HESSENBERG FORM                           */
/*                                                                 */
/*******************************************************************/
#define lswap(x,y) { long _t=x; x=y; y=_t; }
#define swap(x,y) { GEN _t=x; x=y; y=_t; }

GEN
hess(GEN x)
{
  gpmem_t av = avma;
  long lx=lg(x),m,i,j;
  GEN p,p1,p2;

  if (typ(x) != t_MAT) err(mattype1,"hess");
  if (lx==1) return cgetg(1,t_MAT);
  if (lg(x[1])!=lx) err(mattype1,"hess");
  x = dummycopy(x);

  for (m=2; m<lx-1; m++)
    for (i=m+1; i<lx; i++)
    {
      p = gcoeff(x,i,m-1);
      if (gcmp0(p)) continue;

      for (j=m-1; j<lx; j++) lswap(coeff(x,i,j), coeff(x,m,j));
      lswap(x[i], x[m]); p = ginv(p);
      for (i=m+1; i<lx; i++)
      {
        p1 = gcoeff(x,i,m-1);
        if (gcmp0(p1)) continue;

        p1 = gmul(p1,p); p2 = gneg_i(p1);
        coeff(x,i,m-1) = zero;
        for (j=m; j<lx; j++)
          coeff(x,i,j) = ladd(gcoeff(x,i,j), gmul(p2,gcoeff(x,m,j)));
        for (j=1; j<lx; j++)
          coeff(x,j,m) = ladd(gcoeff(x,j,m), gmul(p1,gcoeff(x,j,i)));
      }
      break;
    }
  return gerepilecopy(av,x);
}

GEN
carhess(GEN x, long v)
{
  gpmem_t av,tetpil;
  long lx,r,i;
  GEN *y,p1,p2,p3,p4;

  if ((p1 = easychar(x,v,NULL))) return p1;

  lx=lg(x); av=avma; y = (GEN*) new_chunk(lx);
  y[0]=polun[v]; p1=hess(x); p2=polx[v];
  tetpil=avma;
  for (r=1; r<lx; r++)
  {
    y[r]=gmul(y[r-1], gsub(p2,gcoeff(p1,r,r)));
    p3=gun; p4=gzero;
    for (i=r-1; i; i--)
    {
      p3=gmul(p3,gcoeff(p1,i+1,i));
      p4=gadd(p4,gmul(gmul(p3,gcoeff(p1,i,r)),y[i-1]));
    }
    tetpil=avma; y[r]=gsub(y[r],p4);
  }
  return gerepile(av,tetpil,y[lx-1]);
}

/*******************************************************************/
/*                                                                 */
/*                            NORM                                 */
/*                                                                 */
/*******************************************************************/

GEN
gnorm(GEN x)
{
  gpmem_t av;
  long lx,i, tx=typ(x);
  GEN p1,p2,y;

  switch(tx)
  {
    case t_INT:
      return sqri(x);

    case t_REAL:
      return mulrr(x,x);

    case t_FRAC: case t_FRACN:
      return gsqr(x);

    case t_COMPLEX: av = avma;
      return gerepileupto(av, gadd(gsqr((GEN)x[1]), gsqr((GEN)x[2])));

    case t_QUAD: av = avma;
      p1 = (GEN)x[1];
      p2 = gmul((GEN)p1[2], gsqr((GEN)x[3]));
      p1 = gcmp0((GEN)p1[3])? gsqr((GEN)x[2])
                            : gmul((GEN)x[2], gadd((GEN)x[2],(GEN)x[3]));
      return gerepileupto(av, gadd(p1,p2));

    case t_POL: case t_SER: case t_RFRAC: case t_RFRACN: av = avma;
      return gerepileupto(av, greal(gmul(gconj(x),x)));

    case t_POLMOD:
    {
      GEN T = (GEN)x[1], A = (GEN)x[2];
      if (typ(A) != t_POL) return gpowgs(A, degpol(T));

      y = subres(T, A); p1 = leading_term(T);
      if (gcmp1(p1) || gcmp0(A)) return y;
      av = avma; T = gpowgs(p1, degpol(A));
      return gerepileupto(av, gdiv(y,T));
    }

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=lnorm((GEN) x[i]);
      return y;
  }
  err(typeer,"gnorm");
  return NULL; /* not reached */
}

GEN
gnorml2(GEN x)
{
  gpmem_t av,lim;
  GEN y;
  long i,tx=typ(x),lx;

  if (! is_matvec_t(tx)) return gnorm(x);
  lx=lg(x); if (lx==1) return gzero;

  av=avma; lim = stack_lim(av,1); y = gnorml2((GEN) x[1]);
  for (i=2; i<lx; i++)
  {
    y = gadd(y, gnorml2((GEN) x[i]));
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"gnorml2");
      y = gerepileupto(av, y);
    }
  }
  return gerepileupto(av,y);
}

GEN
QuickNormL2(GEN x, long prec)
{
  gpmem_t av = avma;
  GEN y = gmul(x, realun(prec));
  if (typ(x) == t_POL)
    *++y = evaltyp(t_VEC) | evallg(lgef(x)-1);
  return gerepileupto(av, gnorml2(y));
}

GEN
gnorml1(GEN x,long prec)
{
  gpmem_t av = avma;
  long lx,i;
  GEN s;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_COMPLEX: case t_FRAC:
    case t_FRACN: case t_QUAD:
      return gabs(x,prec);

    case t_POL:
      lx = lgef(x); s = gzero;
      for (i=2; i<lx; i++) s = gadd(s, gabs((GEN)x[i],prec));
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); s = gzero;
      for (i=1; i<lx; i++) s = gadd(s, gabs((GEN)x[i],prec));
      break;

    default: err(typeer,"gnorml1");
      return NULL; /* not reached */
  }
  return gerepileupto(av, s);
}

GEN
QuickNormL1(GEN x,long prec)
{
  gpmem_t av = avma;
  long lx,i;
  GEN p1,p2,s;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return gabs(x,prec);

    case t_INTMOD: case t_PADIC: case t_POLMOD:
    case t_SER: case t_RFRAC: case t_RFRACN:
      return gcopy(x);

    case t_COMPLEX:
      p1=gabs((GEN)x[1],prec); p2=gabs((GEN)x[2],prec);
      return gerepileupto(av, gadd(p1,p2));

    case t_QUAD:
      p1=gabs((GEN)x[2],prec); p2=gabs((GEN)x[3],prec);
      return gerepileupto(av, gadd(p1,p2));

    case t_POL:
      lx=lg(x); s=gzero;
      for (i=2; i<lx; i++) s=gadd(s,QuickNormL1((GEN)x[i],prec));
      return gerepileupto(av, s);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); s=gzero;
      for (i=1; i<lx; i++) s=gadd(s,QuickNormL1((GEN)x[i],prec));
      return gerepileupto(av, s);
  }
  err(typeer,"QuickNormL1");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                          CONJUGATION                            */
/*                                                                 */
/*******************************************************************/

GEN
gconj(GEN x)
{
  long lx,i,tx=typ(x);
  GEN z;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_INTMOD:
    case t_FRAC: case t_FRACN: case t_PADIC:
      return gcopy(x);

    case t_COMPLEX:
      z=cgetg(3,t_COMPLEX);
      z[1]=lcopy((GEN) x[1]);
      z[2]=lneg((GEN) x[2]);
      break;

    case t_QUAD:
      z=cgetg(4,t_QUAD);
      copyifstack(x[1],z[1]);
      z[2]=gcmp0(gmael(x,1,3))? lcopy((GEN) x[2])
                              : ladd((GEN) x[2],(GEN) x[3]);
      z[3]=lneg((GEN) x[3]);
      break;

    case t_POL:
      lx=lgef(x); z=cgetg(lx,tx); z[1]=x[1];
      for (i=2; i<lx; i++) z[i]=lconj((GEN) x[i]);
      break;

    case t_SER:
      lx=lg(x); z=cgetg(lx,tx); z[1]=x[1];
      for (i=2; i<lx; i++) z[i]=lconj((GEN) x[i]);
      break;

    case t_RFRAC: case t_RFRACN: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=lconj((GEN) x[i]);
      break;

    default:
      err(typeer,"gconj");
      return NULL; /* not reached */
  }
  return z;
}

GEN
conjvec(GEN x,long prec)
{
  gpmem_t av,tetpil;
  long lx,s,i,tx=typ(x);
  GEN z,y,p1,p2,p;

  switch(tx)
  {
    case t_INT: case t_INTMOD: case t_FRAC: case t_FRACN:
      z=cgetg(2,t_COL); z[1]=lcopy(x); break;

    case t_COMPLEX: case t_QUAD:
      z=cgetg(3,t_COL); z[1]=lcopy(x); z[2]=lconj(x); break;

    case t_VEC: case t_COL:
      lx=lg(x); z=cgetg(lx,t_MAT);
      for (i=1; i<lx; i++) z[i]=(long)conjvec((GEN)x[i],prec);
      s=lg(z[1]);
      for (i=2; i<lx; i++)
	if (lg(z[i])!=s) err(talker,"incompatible field degrees in conjvec");
      break;

    case t_POLMOD:
      y=(GEN)x[1]; lx=lgef(y);
      if (lx<=3) return cgetg(1,t_COL);
      av=avma; p=NULL;
      for (i=2; i<lx; i++)
      {
	tx=typ(y[i]);
	if (tx==t_INTMOD) p=gmael(y,i,1);
	else
	  if (tx != t_INT && ! is_frac_t(tx))
	    err(polrationer,"conjvec");
      }
      if (!p)
      {
	p1=roots(y,prec); x = (GEN)x[2]; tetpil=avma;
	z=cgetg(lx-2,t_COL);
	for (i=1; i<=lx-3; i++)
	{
	  p2=(GEN)p1[i]; if (gcmp0((GEN)p2[2])) p2 = (GEN)p2[1];
	  z[i] = (long)poleval(x, p2);
	 }
	return gerepile(av,tetpil,z);
      }
      z=cgetg(lx-2,t_COL); z[1]=lcopy(x);
      for (i=2; i<=lx-3; i++) z[i] = lpui((GEN) z[i-1],p,prec);
      break;

    default:
      err(typeer,"conjvec");
      return NULL; /* not reached */
  }
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                            TRACES                               */
/*                                                                 */
/*******************************************************************/

GEN
assmat(GEN x)
{
  long lx,i,j;
  GEN y,p1,p2;

  if (typ(x)!=t_POL) err(notpoler,"assmat");
  if (gcmp0(x)) err(zeropoler,"assmat");

  lx=lgef(x)-2; y=cgetg(lx,t_MAT);
  for (i=1; i<lx-1; i++)
  {
    p1=cgetg(lx,t_COL); y[i]=(long)p1;
    for (j=1; j<lx; j++)
      p1[j] = (j==(i+1))? un: zero;
  }
  p1=cgetg(lx,t_COL); y[i]=(long)p1;
  if (gcmp1((GEN) x[lx+1]))
    for (j=1; j<lx; j++)
      p1[j] = lneg((GEN)x[j+1]);
  else
  {
    p2 = (GEN)x[lx+1]; gnegz(p2,p2);
    for (j=1; j<lx; j++)
      p1[j] = ldiv((GEN)x[j+1],p2);
    gnegz(p2,p2);
  }
  return y;
}

GEN
gtrace(GEN x)
{
  gpmem_t av, tetpil;
  long i,n,tx=typ(x),lx;
  GEN y,p1,p2;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return gmul2n(x,1);

    case t_COMPLEX:
      return gmul2n((GEN)x[1],1);

    case t_QUAD:
      p1=(GEN)x[1];
      if (!gcmp0((GEN) p1[3]))
      {
	av=avma; p2=gmul2n((GEN)x[2],1);
	tetpil=avma; return gerepile(av,tetpil,gadd((GEN)x[3],p2));
      }
      return gmul2n((GEN)x[2],1);

    case t_POL:
      lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=ltrace((GEN)x[i]);
      return y;

    case t_SER:
      lx=lg(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=ltrace((GEN)x[i]);
      return y;

    case t_POLMOD:
      av=avma; n=(lgef(x[1])-4);
      p1=polsym((GEN)x[1],n); p2=gzero;
      for (i=0; i<=n; i++)
        p2=gadd(p2,gmul(truecoeff((GEN)x[2],i),(GEN)p1[i+1]));
      return gerepileupto(av,p2);

    case t_RFRAC: case t_RFRACN:
      return gadd(x,gconj(x));

    case t_VEC: case t_COL:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=ltrace((GEN)x[i]);
      return y;

    case t_MAT:
      lx=lg(x); if (lx==1) return gzero;/*now lx>=2*/
      if (lx!=lg(x[1])) err(mattype1,"gtrace");
      av=avma; p1=gcoeff(x,1,1); if (lx==2) return gcopy(p1);
      for (i=2; i<lx-1; i++)
	p1=gadd(p1,gcoeff(x,i,i));
      tetpil=avma; return gerepile(av,tetpil,gadd(p1,gcoeff(x,i,i)));

  }
  err(typeer,"gtrace");
  return NULL; /* not reached */
}

/* Gauss reduction for positive definite matrix a
 * If a is not positive definite:
 *   if flag is zero: raise an error
 *   else: return NULL.
 */
GEN
sqred1intern(GEN a,long flag)
{
  gpmem_t av = avma, lim=stack_lim(av,1);
  GEN b,p;
  long i,j,k, n = lg(a);

  if (typ(a)!=t_MAT) err(typeer,"sqred1");
  if (n == 1) return cgetg(1, t_MAT);
  if (lg(a[1])!=n) err(mattype1,"sqred1");
  b=cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    GEN p1=cgetg(n,t_COL), p2=(GEN)a[j];

    b[j]=(long)p1;
    for (i=1; i<=j; i++) p1[i] = p2[i];
    for (   ; i<n ; i++) p1[i] = zero;
  }
  for (k=1; k<n; k++)
  {
    p = gcoeff(b,k,k);
    if (gsigne(p)<=0) /* not positive definite */
    {
      if (flag) { avma=av; return NULL; }
      err(talker,"not a positive definite matrix in sqred1");
    }
    p = ginv(p);
    for (i=k+1; i<n; i++)
      for (j=i; j<n; j++)
	coeff(b,i,j)=lsub(gcoeff(b,i,j),
	                  gmul(gmul(gcoeff(b,k,i),gcoeff(b,k,j)), p));
    for (j=k+1; j<n; j++)
      coeff(b,k,j)=lmul(gcoeff(b,k,j), p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"sqred1");
      b=gerepilecopy(av,b);
    }
  }
  return gerepilecopy(av,b);
}

GEN
sqred1(GEN a)
{
  return sqred1intern(a,0);
}

GEN
sqred3(GEN a)
{
  gpmem_t av = avma, lim = stack_lim(av,1);
  long i,j,k,l, n = lg(a);
  GEN p1,b;

  if (typ(a)!=t_MAT) err(typeer,"sqred3");
  if (lg(a[1])!=n) err(mattype1,"sqred3");
  av=avma; b=cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    p1=cgetg(n,t_COL); b[j]=(long)p1;
    for (i=1; i<n; i++) p1[i]=zero;
  }
  for (i=1; i<n; i++)
  {
    for (k=1; k<i; k++)
    {
      p1=gzero;
      for (l=1; l<k; l++)
	p1=gadd(p1, gmul(gmul(gcoeff(b,l,l),gcoeff(b,k,l)), gcoeff(b,i,l)));
      coeff(b,i,k)=ldiv(gsub(gcoeff(a,i,k),p1),gcoeff(b,k,k));
    }
    p1=gzero;
    for (l=1; l<i; l++)
      p1=gadd(p1, gmul(gcoeff(b,l,l), gsqr(gcoeff(b,i,l))));
    coeff(b,i,k)=lsub(gcoeff(a,i,i),p1);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"sqred3");
      b=gerepilecopy(av,b);
    }
  }
  return gerepilecopy(av,b);
}

/* Gauss reduction (arbitrary symetric matrix, only the part above the
 * diagonal is considered). If no_signature is zero, return only the
 * signature
 */
static GEN
sqred2(GEN a, long no_signature)
{
  GEN r,p,mun;
  gpmem_t av,av1,lim;
  long n,i,j,k,l,sp,sn,t;

  if (typ(a)!=t_MAT) err(typeer,"sqred2");
  n=lg(a); if (lg(a[1]) != n) err(mattype1,"sqred2");

  av=avma; mun=negi(gun); r=new_chunk(n);
  for (i=1; i<n; i++) r[i]=1;
  av1=avma; lim=stack_lim(av1,1); a=dummycopy(a);
  n--; t=n; sp=sn=0;
  while (t)
  {
    k=1; while (k<=n && (gcmp0(gcoeff(a,k,k)) || !r[k])) k++;
    if (k<=n)
    {
      p=gcoeff(a,k,k); if (gsigne(p)>0) sp++; else sn++;
      r[k]=0; t--;
      for (j=1; j<=n; j++)
	coeff(a,k,j)=r[j] ? ldiv(gcoeff(a,k,j),p) : zero;
	
      for (i=1; i<=n; i++) if (r[i])
	for (j=1; j<=n; j++)
	  coeff(a,i,j) = r[j] ? lsub(gcoeff(a,i,j),
	                             gmul(gmul(gcoeff(a,k,i),gcoeff(a,k,j)),p))
			      : zero;
      coeff(a,k,k)=(long)p;
    }
    else
    {
      for (k=1; k<=n; k++) if (r[k])
      {
	l=k+1; while (l<=n && (gcmp0(gcoeff(a,k,l)) || !r[l])) l++;
	if (l<=n)
	{
	  p=gcoeff(a,k,l); r[k]=r[l]=0; sp++; sn++; t-=2;
	  for (i=1; i<=n; i++) if (r[i])
	  {
	    for (j=1; j<=n; j++)
	      coeff(a,i,j) =
		r[j]? lsub(gcoeff(a,i,j),
			   gdiv(gadd(gmul(gcoeff(a,k,i),gcoeff(a,l,j)),
				     gmul(gcoeff(a,k,j),gcoeff(a,l,i))),
				p))
		    : zero;
	    coeff(a,k,i)=ldiv(gadd(gcoeff(a,k,i),gcoeff(a,l,i)),p);
	    coeff(a,l,i)=ldiv(gsub(gcoeff(a,k,i),gcoeff(a,l,i)),p);
	  }
	  coeff(a,k,l)=un; coeff(a,l,k)=(long)mun;
	  coeff(a,k,k)=lmul2n(p,-1); coeff(a,l,l)=lneg(gcoeff(a,k,k));
	  if (low_stack(lim, stack_lim(av1,1)))
	  {
	    if(DEBUGMEM>1) err(warnmem,"sqred2");
	    a=gerepilecopy(av1,a);
	  }
	  break;
	}
      }
      if (k>n) break;
    }
  }
  if (no_signature) return gerepilecopy(av,a);
  avma=av;
  a=cgetg(3,t_VEC); a[1]=lstoi(sp); a[2]=lstoi(sn); return a;
}

GEN
sqred(GEN a) { return sqred2(a,1); }

GEN
signat(GEN a) { return sqred2(a,0); }

/* Diagonalization of a REAL symetric matrix. Return a 2-component vector:
 * 1st comp = vector of eigenvalues
 * 2nd comp = matrix of eigenvectors
 */
GEN
jacobi(GEN a, long prec)
{
  gpmem_t av1, av2;
  long de,e,e1,e2,l,n,i,j,p,q;
  GEN c,s,t,u,ja,lambda,r,unr,x,y,x1,y1;

  if (typ(a)!=t_MAT) err(mattype1,"jacobi");
  ja=cgetg(3,t_VEC); l=lg(a); n=l-1;
  e1=HIGHEXPOBIT-1;
  lambda=cgetg(l,t_COL); ja[1]=(long)lambda;
  for (j=1; j<=n; j++)
  {
    lambda[j]=lgetr(prec);
    gaffect(gcoeff(a,j,j), (GEN)lambda[j]);
    e=expo(lambda[j]); if (e<e1) e1=e;
  }
  r=cgetg(l,t_MAT); ja[2]=(long)r;
  for (j=1; j<=n; j++)
  {
    r[j]=lgetg(l,t_COL);
    for (i=1; i<=n; i++)
      affsr(i==j, (GEN)(coeff(r,i,j)=lgetr(prec)));
  }
  av1=avma;

  e2=-HIGHEXPOBIT;p=q=1;
  c=cgetg(l,t_MAT);
  for (j=1; j<=n; j++)
  {
    c[j]=lgetg(j,t_COL);
    for (i=1; i<j; i++)
    {
      gaffect(gcoeff(a,i,j), (GEN)(coeff(c,i,j)=lgetr(prec)));
      e=expo(gcoeff(c,i,j)); if (e>e2) { e2=e; p=i; q=j; }
    }
  }
  a=c; unr = realun(prec);
  de=bit_accuracy(prec);

 /* e1 = min des expo des coeff diagonaux
  * e2 = max des expo des coeff extra-diagonaux
  * Test d'arret: e2 < e1-precision
  */
  while (e1-e2<de)
  {
    /*calcul de la rotation associee dans le plan
	  des p et q-iemes vecteurs de base   */
    av2=avma;
    x=divrr(subrr((GEN)lambda[q],(GEN)lambda[p]),shiftr(gcoeff(a,p,q),1));
    y=mpsqrt(addrr(unr,mulrr(x,x)));
    t=(gsigne(x)>0)? divrr(unr,addrr(x,y)) : divrr(unr,subrr(x,y));
    c=divrr(unr,mpsqrt(addrr(unr,mulrr(t,t))));
    s=mulrr(t,c); u=divrr(s,addrr(unr,c));

    /* Recalcul des transformees successives de a et de la matrice
	   cumulee (r) des rotations :  */

    for (i=1; i<p; i++)
    {
      x=gcoeff(a,i,p); y=gcoeff(a,i,q);
      x1=subrr(x,mulrr(s,addrr(y,mulrr(u,x))));
      y1=addrr(y,mulrr(s,subrr(x,mulrr(u,y))));
      affrr(x1,gcoeff(a,i,p)); affrr(y1,gcoeff(a,i,q));
    }
    for (i=p+1; i<q; i++)
    {
      x=gcoeff(a,p,i); y=gcoeff(a,i,q);
      x1=subrr(x,mulrr(s,addrr(y,mulrr(u,x))));
      y1=addrr(y,mulrr(s,subrr(x,mulrr(u,y))));
      affrr(x1,gcoeff(a,p,i)); affrr(y1,gcoeff(a,i,q));
    }
    for (i=q+1; i<=n; i++)
    {
      x=gcoeff(a,p,i); y=gcoeff(a,q,i);
      x1=subrr(x,mulrr(s,addrr(y,mulrr(u,x))));
      y1=addrr(y,mulrr(s,subrr(x,mulrr(u,y))));
      affrr(x1,gcoeff(a,p,i)); affrr(y1,gcoeff(a,q,i));
    }
    x=(GEN)lambda[p]; y=gcoeff(a,p,q); subrrz(x,mulrr(t,y),(GEN)lambda[p]);
    x=y; y=(GEN)lambda[q]; addrrz(y,mulrr(t,x),y);
    setexpo(x,expo(x)-de-1);

    for (i=1; i<=n; i++)
    {
      x=gcoeff(r,i,p); y=gcoeff(r,i,q);
      x1=subrr(x,mulrr(s,addrr(y,mulrr(u,x))));
      y1=addrr(y,mulrr(s,subrr(x,mulrr(u,y))));
      affrr(x1,gcoeff(r,i,p)); affrr(y1,gcoeff(r,i,q));
    }

    e2=expo(gcoeff(a,1,2)); p=1; q=2;
    for (j=1; j<=n; j++)
    {
      for (i=1; i<j; i++)
	if ((e=expo(gcoeff(a,i,j))) > e2) { e2=e; p=i; q=j; }
      for (i=j+1; i<=n; i++)
	if ((e=expo(gcoeff(a,j,i))) > e2) { e2=e; p=j; q=i; }
    }
    avma=av2;
  }
  avma=av1; return ja;
}

/*************************************************************************/
/**									**/
/**		    MATRICE RATIONNELLE --> ENTIERE			**/
/**									**/
/*************************************************************************/

GEN
matrixqz0(GEN x,GEN p)
{
  if (typ(p)!=t_INT) err(typeer,"matrixqz0");
  if (signe(p)>=0)  return matrixqz(x,p);
  if (!cmpsi(-1,p)) return matrixqz2(x);
  if (!cmpsi(-2,p)) return matrixqz3(x);
  err(flagerr,"matrixqz"); return NULL; /* not reached */
}

static int
ZV_isin(GEN x)
{
  long i,l = lg(x);
  for (i=1; i<l; i++)
    if (typ(x[i]) != t_INT) return 0;
  return 1;
}

GEN
matrixqz(GEN x, GEN p)
{
  gpmem_t av = avma, av1, lim;
  long i,j,j1,m,n,nfact;
  GEN p1,p2,p3;

  if (typ(x) != t_MAT) err(typeer,"matrixqz");
  n = lg(x)-1; if (!n) return gcopy(x);
  m = lg(x[1])-1;
  if (n > m) err(talker,"more rows than columns in matrixqz");
  if (n==m)
  {
    p1 = det(x);
    if (gcmp0(p1)) err(talker,"matrix of non-maximal rank in matrixqz");
    avma = av; return idmat(n);
  }
  /* m > n */
  p1 = x; x = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    x[j] = (long)primpart((GEN)p1[j]);
    if (!ZV_isin((GEN)p1[j])) err(talker, "not a rational matrix in matrixqz");
  }
  /* x integral */

  if (gcmp0(p))
  {
    p1 = gtrans(x); setlg(p1,n+1);
    p2 = det(p1); p1[n] = p1[n+1]; p2 = ggcd(p2,det(p1));
    if (!signe(p2))
      err(impl,"matrixqz when the first 2 dets are zero");
    if (gcmp1(p2)) return gerepilecopy(av,x);

    p1 = (GEN)factor(p2)[1];
  }
  else p1 = _vec(p);
  nfact = lg(p1)-1;
  av1 = avma; lim = stack_lim(av1,1);
  for (i=1; i<=nfact; i++)
  {
    p = (GEN)p1[i];
    for(;;)
    {
      p2 = FpM_ker(x, p);
      if (lg(p2)==1) break;

      p2 = centermod(p2,p); p3 = gdiv(gmul(x,p2), p);
      for (j=1; j<lg(p2); j++)
      {
	j1=n; while (gcmp0(gcoeff(p2,j1,j))) j1--;
	x[j1] = p3[j];
      }
      if (low_stack(lim, stack_lim(av1,1)))
      {
	if (DEBUGMEM>1) err(warnmem,"matrixqz");
	x = gerepilecopy(av1,x);
      }
    }
  }
  return gerepilecopy(av,x);
}

static GEN
Z_V_mul(GEN u, GEN A)
{
  if (gcmp1(u)) return A;
  if (gcmp_1(u)) return gneg(A);
  if (gcmp0(u)) return zerocol(lg(A)-1);
  return gmul(u,A);
}

static GEN
QV_lincomb(GEN u, GEN v, GEN A, GEN B)
{
  if (!signe(u)) return Z_V_mul(v,B);
  if (!signe(v)) return Z_V_mul(u,A);
  return gadd(Z_V_mul(u,A), Z_V_mul(v,B));
}

/* cf ZV_elem */
/* zero aj = Aij (!= 0)  using  ak = Aik (maybe 0), via linear combination of
 * A[j] and A[k] of determinant 1. */
static void
QV_elem(GEN aj, GEN ak, GEN A, long j, long k)
{
  GEN p1,u,v,d, D;

  if (gcmp0(ak)) { lswap(A[j],A[k]); return; }
  D = mpppcm(denom(aj), denom(ak));
  if (!is_pm1(D)) { aj = gmul(aj,D); ak = gmul(ak,D); }
  d = bezout(aj,ak,&u,&v);
  /* frequent special case (u,v) = (1,0) or (0,1) */
  if (!signe(u))
  { /* ak | aj */
    p1 = negi(divii(aj,ak));
    A[j]   = (long)QV_lincomb(gun, p1, (GEN)A[j], (GEN)A[k]);
    return;
  }
  if (!signe(v))
  { /* aj | ak */
    p1 = negi(divii(ak,aj));
    A[k]   = (long)QV_lincomb(gun, p1, (GEN)A[k], (GEN)A[j]);
    lswap(A[j], A[k]);
    return;
  }

  if (!is_pm1(d)) { aj = divii(aj,d); ak = divii(ak,d); }
  p1 = (GEN)A[k]; aj = negi(aj);
  A[k] = (long)QV_lincomb(u,v, (GEN)A[j],p1);
  A[j] = (long)QV_lincomb(aj,ak, p1,(GEN)A[j]);
}

extern GEN hnfall_i(GEN A, GEN *ptB, long remove);

static GEN
matrixqz_aux(GEN A)
{
  gpmem_t av = avma, lim = stack_lim(av,1);
  long i,j,k,n,m;
  GEN a;

  n = lg(A); if (n == 1) return cgetg(1,t_MAT);
  m = lg(A[1]);
  for (i=1; i<m; i++)
  {
    for (j=k=1; j<n; j++)
    {
      GEN a = gcoeff(A,i,j);
      if (gcmp0(a)) continue;

      k = j+1; if (k == n) k = 1;
      /* zero a = Aij  using  b = Aik */
      QV_elem(a, gcoeff(A,i,k), A, j,k);
    }
    a = gcoeff(A,i,k);
    if (!gcmp0(a))
    {
      a = denom(a);
      if (!is_pm1(a)) A[k] = lmul(a, (GEN)A[k]);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"matrixqz_aux");
      A = gerepilecopy(av,A);
    }
  }
  return m > 100? hnfall_i(A,NULL,1): hnf(A);
}

GEN
matrixqz2(GEN x)
{
  gpmem_t av = avma;
  if (typ(x)!=t_MAT) err(typeer,"matrixqz2");
  x = dummycopy(x);
  return gerepileupto(av, matrixqz_aux(x));
}

GEN
matrixqz3(GEN x)
{
  gpmem_t av = avma, av1, lim;
  long j,j1,k,m,n;
  GEN c;

  if (typ(x)!=t_MAT) err(typeer,"matrixqz3");
  n = lg(x); if (n==1) return gcopy(x);
  m = lg(x[1]); x = dummycopy(x);
  c = cgetg(n,t_VECSMALL);
  for (j=1; j<n; j++) c[j] = 0;
  av1 = avma; lim = stack_lim(av1,1);
  for (k=1; k<m; k++)
  {
    j=1; while (j<n && (c[j] || gcmp0(gcoeff(x,k,j)))) j++;
    if (j==n) continue;
   
    c[j]=k; x[j]=ldiv((GEN)x[j],gcoeff(x,k,j));
    for (j1=1; j1<n; j1++)
      if (j1!=j)
      {
        GEN t = gcoeff(x,k,j1);
        if (!gcmp0(t)) x[j1] = lsub((GEN)x[j1],gmul(t,(GEN)x[j]));
      }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"matrixqz3");
      x = gerepilecopy(av1,x);
    }
  }
  return gerepileupto(av, matrixqz_aux(x));
}

GEN
intersect(GEN x, GEN y)
{
  gpmem_t av,tetpil;
  long j, lx = lg(x);
  GEN z;

  if (typ(x)!=t_MAT || typ(y)!=t_MAT) err(typeer,"intersect");
  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);

  av=avma; z=ker(concatsp(x,y));
  for (j=lg(z)-1; j; j--) setlg(z[j],lx);
  tetpil=avma; return gerepile(av,tetpil,gmul(x,z));
}

/**************************************************************/
/**                                                          **/
/**		   HERMITE NORMAL FORM REDUCTION	     **/
/**							     **/
/**************************************************************/

GEN
mathnf0(GEN x, long flag)
{
  switch(flag)
  {
    case 0: return hnf(x);
    case 1: return hnfall(x);
    case 3: return hnfperm(x);
    case 4: return hnflll(x);
    default: err(flagerr,"mathnf");
  }
  return NULL; /* not reached */
}

static GEN
init_hnf(GEN x, GEN *denx, long *co, long *li, gpmem_t *av)
{
  if (typ(x) != t_MAT) err(typeer,"mathnf");
  *co=lg(x); if (*co==1) return NULL; /* empty matrix */
  *li=lg(x[1]); *denx=denom(x); *av=avma;

  if (gcmp1(*denx)) /* no denominator */
    { *denx = NULL; return dummycopy(x); }
  return gmul(x,*denx);
}

GEN
ZV_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) y[i] = signe(x[i])? licopy((GEN)x[i]): zero;
  return y;
}

GEN
ZM_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);

  for (i=1; i<lx; i++)
    y[i] = (long)ZV_copy((GEN)x[i]);
  return y;
}

/* return c * X. Not memory clean if c = 1 */
GEN
ZV_Z_mul(GEN c, GEN X)
{
  long i,m = lg(X);
  GEN A = new_chunk(m);
  if (is_pm1(c))
  {
    if (signe(c) > 0)
      { for (i=1; i<m; i++) A[i] = X[i]; }
    else
      { for (i=1; i<m; i++) A[i] = lnegi((GEN)X[i]); }
  }
  else /* c = 0 should be exceedingly rare */
    { for (i=1; i<m; i++) A[i] = lmulii(c,(GEN)X[i]); }
  A[0] = X[0]; return A;
}

/* X,Y columns; u,v scalars; everybody is integral. return A = u*X + v*Y
 * Not memory clean if (u,v) = (1,0) or (0,1) */
GEN
ZV_lincomb(GEN u, GEN v, GEN X, GEN Y)
{
  gpmem_t av;
  long i,lx,m;
  GEN p1,p2,A;

  if (!signe(u)) return ZV_Z_mul(v,Y);
  if (!signe(v)) return ZV_Z_mul(u,X);
  lx = lg(X); A = cgetg(lx,t_COL); m = lgefint(u)+lgefint(v)+4;
  if (is_pm1(v)) { swap(u,v); swap(X,Y); }
  if (is_pm1(u))
  {
    if (signe(u) > 0)
    {
      for (i=1; i<lx; i++)
      {
        p1=(GEN)X[i]; p2=(GEN)Y[i];
        if      (!signe(p1)) A[i] = lmulii(v,p2);
        else if (!signe(p2)) A[i] = licopy(p1);
        else
        {
          av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2)); /* HACK */
          p2 = mulii(v,p2);
          avma = av; A[i] = laddii(p1,p2);
        }
      }
    }
    else
    {
      for (i=1; i<lx; i++)
      {
        p1=(GEN)X[i]; p2=(GEN)Y[i];
        if      (!signe(p1)) A[i] = lmulii(v,p2);
        else if (!signe(p2)) A[i] = lnegi(p1);
        else
        {
          av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2)); /* HACK */
          p2 = mulii(v,p2);
          avma = av; A[i] = lsubii(p2,p1);
        }
      }
    }
  }
  else
    for (i=1; i<lx; i++)
    {
      p1=(GEN)X[i]; p2=(GEN)Y[i];
      if      (!signe(p1)) A[i] = lmulii(v,p2);
      else if (!signe(p2)) A[i] = lmulii(u,p1);
      else
      {
        av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2)); /* HACK */
        p1 = mulii(u,p1);
        p2 = mulii(v,p2);
        avma = av; A[i] = laddii(p1,p2);
      }
    }
  return A;
}

/* x = [A,U], nbcol(A) = nbcol(U), A integral. Return [AV, UV], with AV HNF */
GEN
hnf_special(GEN x, long remove)
{
  gpmem_t av0,av,tetpil,lim;
  long s,li,co,i,j,k,def,ldef;
  GEN p1,u,v,d,denx,a,b, x2,res;

  if (typ(x) != t_VEC || lg(x) !=3) err(typeer,"hnf_special");
  res = cgetg(3,t_VEC);
  av0 = avma;
  x2 = (GEN)x[2];
  x  = (GEN)x[1];
  x = init_hnf(x,&denx,&co,&li,&av);
  if (!x) return cgetg(1,t_MAT);

  lim = stack_lim(av,1);
  def=co-1; ldef=(li>co)? li-co: 0;
  if (lg(x2) != co) err(talker,"incompatible matrices in hnf_special");
  x2 = dummycopy(x2);
  for (i=li-1; i>ldef; i--)
  {
    for (j=def-1; j; j--)
    {
      a = gcoeff(x,i,j);
      if (!signe(a)) continue;

      k = (j==1)? def: j-1;
      b = gcoeff(x,i,k); d = bezout(a,b,&u,&v);
      if (!is_pm1(d)) { a = divii(a,d); b = divii(b,d); }
      p1 = (GEN)x[j]; b = negi(b);
      x[j] = (long)ZV_lincomb(a,b, (GEN)x[k], p1);
      x[k] = (long)ZV_lincomb(u,v, p1, (GEN)x[k]);
      p1 = (GEN)x2[j];
      x2[j]=  ladd(gmul(a, (GEN)x2[k]), gmul(b,p1));
      x2[k] = ladd(gmul(u,p1), gmul(v, (GEN)x2[k]));
      if (low_stack(lim, stack_lim(av,1)))
      {
        GEN *gptr[2]; gptr[0]=&x; gptr[1]=&x2;
        if (DEBUGMEM>1) err(warnmem,"hnf_special[1]. i=%ld",i);
        gerepilemany(av,gptr,2);
      }
    }
    p1 = gcoeff(x,i,def); s = signe(p1);
    if (s)
    {
      if (s < 0)
      { 
        x[def] = lneg((GEN)x[def]); p1 = gcoeff(x,i,def);
        x2[def]= lneg((GEN)x2[def]);
      }
      for (j=def+1; j<co; j++)
      {
	b = negi(gdivent(gcoeff(x,i,j),p1));
	x[j] = (long)ZV_lincomb(gun,b, (GEN)x[j], (GEN)x[def]);
        x2[j]= ladd((GEN)x2[j], gmul(b, (GEN)x2[def]));
      }
      def--;
    }
    else
      if (ldef && i==ldef+1) ldef--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[2]; gptr[0]=&x; gptr[1]=&x2;
      if (DEBUGMEM>1) err(warnmem,"hnf_special[2]. i=%ld",i);
      gerepilemany(av,gptr,2);
    }
  }
  if (remove)
  {                            /* remove null columns */
    for (i=1,j=1; j<co; j++)
      if (!gcmp0((GEN)x[j])) 
      {
        x[i] = x[j];
        x2[i] = x2[j]; i++;
      }
    setlg(x,i);
    setlg(x2,i);
  }
  tetpil=avma;
  x = denx? gdiv(x,denx): ZM_copy(x);
  x2 = gcopy(x2);
  {
    GEN *gptr[2]; gptr[0]=&x; gptr[1]=&x2;
    gerepilemanysp(av0,tetpil,gptr,2);
  }
  res[1] = (long)x;
  res[2] = (long)x2;
  return res;
}

/*******************************************************************/
/*                                                                 */
/*                SPECIAL HNF (FOR INTERNAL USE !!!)               */
/*                                                                 */
/*******************************************************************/
extern GEN imagecomplspec(GEN x, long *nlze);

static int
count(long **mat, long row, long len, long *firstnonzero)
{
  int j, n=0;

  for (j=1; j<=len; j++)
  {
    long p = mat[j][row];
    if (p)
    {
      if (labs(p)!=1) return -1;
      n++; *firstnonzero=j;
    }
  }
  return n;
}

static int
count2(long **mat, long row, long len)
{
  int j;
  for (j=len; j; j--)
    if (labs(mat[j][row]) == 1) return j;
  return 0;
}

static GEN
hnffinal(GEN matgen,GEN perm,GEN* ptdep,GEN* ptB,GEN* ptC)
{
  GEN p1,p2,U,H,Hnew,Bnew,Cnew,diagH1;
  GEN B = *ptB, C = *ptC, dep = *ptdep, depnew;
  gpmem_t av, lim;
  long i,j,k,s,i1,j1,zc;
  long co = lg(C);
  long col = lg(matgen)-1;
  long lnz, nlze, lig;

  if (col == 0) return matgen;
  lnz = lg(matgen[1])-1; /* was called lnz-1 - nr in hnfspec */
  nlze = lg(dep[1])-1;
  lig = nlze + lnz;
  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnffinal:\n");
    if (DEBUGLEVEL>6)
    {
      if (nlze) fprintferr("dep = %Z\n",dep);
      fprintferr("mit = %Z\n",matgen);
      fprintferr("B = %Z\n",B);
    }
  }
  p1 = hnflll(matgen);
  H = (GEN)p1[1]; /* lnz x lnz [disregarding initial 0 cols] */
  H += (lg(H)-1 - lnz); H[0] = evaltyp(t_MAT) | evallg(lnz+1);
  U = (GEN)p1[2]; /* col x col */
  /* Only keep the part above the H (above the 0s is 0 since the dep rows
   * are dependant from the ones in matgen) */
  zc = col - lnz; /* # of 0 columns, correspond to units */
  if (nlze) { dep = gmul(dep,U); dep += zc; }

  diagH1 = new_chunk(lnz+1); /* diagH1[i] = 0 iff H[i,i] != 1 (set later) */

  av = avma; lim = stack_lim(av,1);
  Cnew = cgetg(co,t_MAT);
  setlg(C, col+1); p1 = gmul(C,U);
  for (j=1; j<=col; j++) Cnew[j] = p1[j];
  for (   ; j<co ; j++)  Cnew[j] = C[j];
  if (DEBUGLEVEL>5) fprintferr("    hnflll done\n");

  /* Clean up B using new H */
  for (s=0,i=lnz; i; i--)
  {
    GEN h = gcoeff(H,i,i);
    if ( (diagH1[i] = gcmp1(h)) ) { h = NULL; s++; }
    for (j=col+1; j<co; j++)
    {
      GEN z = (GEN)B[j-col];
      p1 = (GEN)z[i+nlze]; if (h) p1 = gdivent(p1,h);
      for (k=1; k<=nlze; k++)
	z[k] = lsubii((GEN)z[k], mulii(p1, gcoeff(dep,k,i)));
      for (   ; k<=lig; k++)
	z[k] = lsubii((GEN)z[k], mulii(p1, gcoeff(H,k-nlze,i)));
      Cnew[j] = lsub((GEN)Cnew[j], gmul(p1, (GEN)Cnew[i+zc]));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[2]; gptr[0]=&Cnew; gptr[1]=&B;
      if(DEBUGMEM>1) err(warnmem,"hnffinal, i = %ld",i);
      gerepilemany(av,gptr,2);
    }
  }
  p1 = cgetg(lnz+1,t_VEC); p2 = perm + nlze;
  for (i1=0, j1=lnz-s, i=1; i<=lnz; i++) /* push the 1 rows down */
    if (diagH1[i])
      p1[++j1] = p2[i];
    else
      p2[++i1] = p2[i];
  for (i=i1+1; i<=lnz; i++) p2[i] = p1[i];
  if (DEBUGLEVEL>5) fprintferr("    first pass in hnffinal done\n");

  /* s = # extra redundant generators taken from H
   *          zc  col-s  co   zc = col ­ lnz
   *       [ 0 |dep |     ]    i = lnze + lnz - s = lig - s
   *  nlze [--------|  B' ]
   *       [ 0 | H' |     ]    H' = H minus the s rows with a 1 on diagonal
   *     i [--------|-----] lig-s           (= "1-rows")
   *       [   0    | Id  ]
   *       [        |     ] li */
  lig -= s; col -= s; lnz -= s;
  Hnew = cgetg(lnz+1,t_MAT);
  depnew = cgetg(lnz+1,t_MAT); /* only used if nlze > 0 */
  Bnew = cgetg(co-col,t_MAT);
  C = dummycopy(Cnew);
  for (j=1,i1=j1=0; j<=lnz+s; j++)
  {
    GEN z = (GEN)H[j];
    if (diagH1[j])
    { /* hit exactly s times */
      i1++; p1 = cgetg(lig+1,t_COL); Bnew[i1] = (long)p1;
      C[i1+col] = Cnew[j+zc];
      for (i=1; i<=nlze; i++) p1[i] = coeff(dep,i,j);
      p1 += nlze;
    }
    else
    {
      j1++; p1 = cgetg(lnz+1,t_COL); Hnew[j1] = (long)p1;
      C[j1+zc] = Cnew[j+zc];
      if (nlze) depnew[j1] = dep[j];
    }
    for (i=k=1; k<=lnz; i++)
      if (!diagH1[i]) p1[k++] = z[i];
  }
  for (j=s+1; j<co-col; j++)
  {
    GEN z = (GEN)B[j-s];
    p1 = cgetg(lig+1,t_COL); Bnew[j] = (long)p1;
    for (i=1; i<=nlze; i++) p1[i] = z[i];
    z += nlze; p1 += nlze;
    for (i=k=1; k<=lnz; i++)
      if (!diagH1[i]) p1[k++] = z[i];
  }
  if (DEBUGLEVEL>5)
  {
    fprintferr("Leaving hnffinal\n");
    if (DEBUGLEVEL>6)
    {
      if (nlze) fprintferr("dep = %Z\n",depnew);
      fprintferr("mit = %Z\nB = %Z\nC = %Z\n", Hnew, Bnew, C);
    }
  }
  if (nlze) *ptdep = depnew;
  *ptC = C;
  *ptB = Bnew; return Hnew;
}

/* for debugging */
static void
p_mat(long **mat, long *perm, long k0)
{
  gpmem_t av = avma;
  GEN p1, matj, matgen;
  long co = lg(mat);
  long li = lg(perm), i,j;

  fprintferr("Permutation: %Z\n",perm);
  matgen = cgetg(co,t_MAT);
  for (j=1; j<co; j++)
  {
    p1 = cgetg(li-k0,t_COL); matgen[j]=(long)p1;
    p1 -= k0; matj = mat[j];
    for (i=k0+1; i<li; i++) p1[i] = lstoi(matj[perm[i]]);
  }
  if (DEBUGLEVEL > 6) fprintferr("matgen = %Z\n",matgen);
  avma=av;
}

static GEN
col_dup(long n, GEN col)
{
   GEN c = new_chunk(n+1);
   memcpy(c,col,(n+1)*sizeof(long));
   return c;
}

/* HNF reduce a relation matrix (column operations + row permutation)
** Input:
**   mat = (li-1) x (co-1) matrix of long
**   C   = r x (co-1) matrix of GEN
**   perm= permutation vector (length li-1), indexing the rows of mat: easier
**     to maintain perm than to copy rows. For columns we can do it directly
**     using e.g. lswap(mat[i], mat[j])
**   k0 = integer. The k0 first lines of mat are dense, the others are sparse.
**     Also if k0=0, mat is modified in place [from mathnfspec], otherwise
**     it is left alone [from buchall]
** Output: cf ASCII art in the function body
**
** row permutations applied to perm
** column operations applied to C.
**/
GEN
hnfspec(long** mat0, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, long k0)
{
  gpmem_t av=avma,av2,lim;
  long *p,i,j,k,lk0,col,lig,*matj, **mat;
  long n,s,t,nlze,lnz,nr;
  GEN p1,p2,matb,matbnew,vmax,matt,T,extramat;
  GEN B,H,dep,permpro;
  GEN *gptr[4];
  long co = lg(mat0);
  long li = lg(perm); /* = lg(mat0[1]) */
  int updateT = 1;

  if (!k0) mat = mat0; /* in place */
  else
  { /* keep original mat0 safe, modify a copy */
    mat = (long**)new_chunk(co); mat[0] = mat0[0];
    for (j=1; j<co; j++) mat[j] = col_dup(li,mat0[j]);
  }

  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnfspec\n");
    p_mat(mat,perm,0);
  }
  matt = cgetg(co,t_MAT); /* dense part of mat (top) */
  for (j=1; j<co; j++)
  {
    p1=cgetg(k0+1,t_COL); matt[j]=(long)p1; matj = mat[j];
    for (i=1; i<=k0; i++) p1[i] = lstoi(matj[perm[i]]);
  }
  vmax = cgetg(co,t_VECSMALL);
  av2 = avma; lim = stack_lim(av2,1);

  i=lig=li-1; col=co-1; lk0=k0;
  if (k0 || (lg(*ptC) > 1 && lg((*ptC)[1]) > 1)) T = idmat(col);
  else
  { /* dummy ! */
    GEN z = cgetg(1,t_COL);
    T = cgetg(co, t_MAT); updateT = 0;
    for (j=1; j<co; j++) T[j] = (long)z;
  }
  /* Look for lines with a single non­0 entry, equal to ±1 */
  while (i > lk0)
    switch( count(mat,perm[i],col,&n) )
    {
      case 0: /* move zero lines between k0+1 and lk0 */
	lk0++; lswap(perm[i], perm[lk0]);
        i=lig; continue;

      case 1: /* move trivial generator between lig+1 and li */
	lswap(perm[i], perm[lig]);
        lswap(T[n], T[col]);
	swap(mat[n], mat[col]); p = mat[col];
	if (p[perm[lig]] < 0) /* = -1 */
	{ /* convert relation -g = 0 to g = 0 */
	  for (i=lk0+1; i<lig; i++) p[perm[i]] = -p[perm[i]];
          if (updateT)
          {
            p1 = (GEN)T[col];
            for (i=1; ; i++)
              if (signe((GEN)p1[i])) { p1[i] = lnegi((GEN)p1[i]); break; }
          }
	}
	lig--; col--; i=lig; continue;

      default: i--;
    }
  if (DEBUGLEVEL>5)
  {
    fprintferr("    after phase1:\n");
    p_mat(mat,perm,0);
  }

#define absmax(s,z) {long _z; _z = labs(z); if (_z > s) s = _z;}

#if 0 /* TODO: check, and put back in */
  /* Get rid of all lines containing only 0 and ± 1, keeping track of column
   * operations in T. Leave the rows 1..lk0 alone [up to k0, coeff
   * explosion, between k0+1 and lk0, row is 0]
   */
  s = 0;
  while (lig > lk0 && s < (HIGHBIT>>1))
  {
    for (i=lig; i>lk0; i--)
      if (count(mat,perm[i],col,&n) >= 0) break;
    if (i == lk0) break;

    /* only 0, ±1 entries, at least 2 of them non-zero */
    lswap(perm[i], perm[lig]);
    lswap(T[n], T[col]); p1 = (GEN)T[col];
    swap(mat[n], mat[col]); p = mat[col];
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      T[col] = lneg(p1);
    }
    for (j=1; j<n; j++)
    {
      matj = mat[j];
      if (! (t = matj[perm[lig]]) ) continue;
      if (t == 1)
      { /* t = 1 */
        for (i=lk0+1; i<=lig; i++)
          absmax(s, matj[perm[i]] -= p[perm[i]]);
        T[j] = lsub((GEN)T[j], p1);
      }
      else
      { /* t = -1 */
        for (i=lk0+1; i<=lig; i++)
          absmax(s, matj[perm[i]] += p[perm[i]]);
        T[j] = ladd((GEN)T[j], p1);
      }
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"hnfspec[1]");
      T = gerepilecopy(av2, T);
    }
  }
#endif
  /* As above with lines containing a ±1 (no other assumption).
   * Stop when single precision becomes dangerous */
  for (j=1; j<=col; j++)
  {
    matj = mat[j];
    for (s=0, i=lk0+1; i<=lig; i++) absmax(s, matj[i]);
    vmax[j] = s;
  }
  while (lig > lk0)
  {
    for (i=lig; i>lk0; i--)
      if ( (n = count2(mat,perm[i],col)) ) break;
    if (i == lk0) break;

    lswap(perm[i], perm[lig]);
    lswap(vmax[n], vmax[col]);
    swap(mat[n], mat[col]); p = mat[col];
    lswap(T[n], T[col]); p1 = (GEN)T[col];
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      p1 = gneg(p1); T[col] = (long)p1;
    }
    for (j=1; j<col; j++)
    {
      matj = mat[j];
      if (! (t = matj[perm[lig]]) ) continue;
      if (vmax[col] && (ulong)labs(t) >= (HIGHBIT-vmax[j]) / vmax[col])
        goto END2;

      for (s=0, i=lk0+1; i<=lig; i++)
        absmax(s, matj[perm[i]] -= t*p[perm[i]]);
      vmax[j] = s;
      T[j] = (long)ZV_lincomb(gun,stoi(-t), (GEN)T[j],p1);
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"hnfspec[2]");
      T = gerepilecopy(av2,T);
    }
  }

END2: /* clean up mat: remove everything to the right of the 1s on diagonal */
  /* go multiprecision first */
  matb = cgetg(co,t_MAT); /* bottom part (complement of matt) */
  for (j=1; j<co; j++)
  {
    p1 = cgetg(li-k0,t_COL); matb[j] = (long)p1;
    p1 -= k0; matj = mat[j];
    for (i=k0+1; i<li; i++) p1[i] = lstoi(matj[perm[i]]);
  }
  if (DEBUGLEVEL>5)
  {
    fprintferr("    after phase2:\n");
    p_mat(mat,perm,k0);
  }
  for (i=li-2; i>lig; i--)
  {
    long i1, i0 = i - k0, k = i + co-li;
    GEN Bk = (GEN)matb[k];
    GEN Tk = (GEN)T[k];
    for (j=k+1; j<co; j++)
    {
      p1=(GEN)matb[j]; p2=(GEN)p1[i0];
      if (! (s=signe(p2)) ) continue;

      p1[i0] = zero;
      if (is_pm1(p2))
      {
        if (s > 0)
        { /* p2 = 1 */
          for (i1=1; i1<i0; i1++)
            p1[i1] = lsubii((GEN)p1[i1], (GEN)Bk[i1]);
          T[j] = lsub((GEN)T[j], Tk);
        }
        else
        { /* p2 = -1 */
          for (i1=1; i1<i0; i1++)
            p1[i1] = laddii((GEN)p1[i1], (GEN)Bk[i1]);
          T[j] = ladd((GEN)T[j], Tk);
        }
      }
      else
      {
        for (i1=1; i1<i0; i1++)
          p1[i1] = lsubii((GEN)p1[i1], mulii(p2,(GEN) Bk[i1]));
        T[j] = (long)ZV_lincomb(gun,negi(p2), (GEN)T[j],Tk);
      }
    }
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"hnfspec[3], i = %ld", i);
      for (j=1; j<co; j++) setlg(matb[j], i0+1); /* bottom can be forgotten */
      gptr[0]=&T; gptr[1]=&matb; gerepilemany(av2,gptr,2);
    }
  }
  gptr[0]=&T; gptr[1]=&matb; gerepilemany(av2,gptr,2);
  if (DEBUGLEVEL>5)
  {
    fprintferr("    matb cleaned up (using Id block)\n");
    if (DEBUGLEVEL>6) outerr(matb);
  }

  nlze = lk0 - k0;  /* # of 0 rows */
  lnz = lig-nlze+1; /* 1 + # of non-0 rows (!= 0...0 1 0 ... 0) */
  if (updateT) matt = gmul(matt,T); /* update top rows */
  extramat = cgetg(col+1,t_MAT); /* = new C minus the 0 rows */
  for (j=1; j<=col; j++)
  {
    GEN z = (GEN)matt[j];
    GEN t = ((GEN)matb[j]) + nlze - k0;
    p2=cgetg(lnz,t_COL); extramat[j]=(long)p2;
    for (i=1; i<=k0; i++) p2[i] = z[i]; /* top k0 rows */
    for (   ; i<lnz; i++) p2[i] = t[i]; /* other non-0 rows */
  }
  permpro = imagecomplspec(extramat, &nr); /* lnz = lg(permpro) */

  if (nlze)
  { /* put the nlze 0 rows (trivial generators) at the top */
    p1 = new_chunk(lk0+1);
    for (i=1; i<=nlze; i++) p1[i] = perm[i + k0];
    for (   ; i<=lk0; i++)  p1[i] = perm[i - nlze];
    for (i=1; i<=lk0; i++)  perm[i] = p1[i];
  }
  /* sort other rows according to permpro (nr redundant generators first) */
  p1 = new_chunk(lnz); p2 = perm + nlze;
  for (i=1; i<lnz; i++) p1[i] = p2[permpro[i]];
  for (i=1; i<lnz; i++) p2[i] = p1[i];
  /* perm indexes the rows of mat
   *   |_0__|__redund__|__dense__|__too big__|_____done______|
   *   0  nlze                              lig             li
   *         \___nr___/ \___k0__/
   *         \____________lnz ______________/
   *
   *               col   co
   *       [dep     |     ]
   *    i0 [--------|  B  ] (i0 = nlze + nr)
   *       [matbnew |     ] matbnew has maximal rank = lnz-1 - nr
   * mat = [--------|-----] lig
   *       [   0    | Id  ]
   *       [        |     ] li */

  matbnew = cgetg(col+1,t_MAT); /* dense+toobig, maximal rank. For hnffinal */
  dep    = cgetg(col+1,t_MAT); /* rows dependant from the ones in matbnew */
  for (j=1; j<=col; j++)
  {
    GEN z = (GEN)extramat[j];
    p1 = cgetg(nlze+nr+1,t_COL); dep[j]=(long)p1;
    p2 = cgetg(lnz-nr,t_COL); matbnew[j]=(long)p2;
    for (i=1; i<=nlze; i++) p1[i]=zero;
    p1 += nlze; for (i=1; i<=nr; i++) p1[i] = z[permpro[i]];
    p2 -= nr;   for (   ; i<lnz; i++) p2[i] = z[permpro[i]];
  }

  /* redundant generators in terms of the genuine generators
   * (x_i) = - (g_i) B */
  B = cgetg(co-col,t_MAT);
  for (j=col+1; j<co; j++)
  {
    GEN y = (GEN)matt[j];
    GEN z = (GEN)matb[j];
    p1=cgetg(lig+1,t_COL); B[j-col]=(long)p1;
    for (i=1; i<=nlze; i++) p1[i] = z[i];
    p1 += nlze; z += nlze-k0;
    for (k=1; k<lnz; k++)
    {
      i = permpro[k];
      p1[k] = (i <= k0)? y[i]: z[i];
    }
  }
  if (updateT) *ptC = gmul(*ptC,T);
  *ptdep = dep;
  *ptB = B;
  H = hnffinal(matbnew,perm,ptdep,ptB,ptC);
  gptr[0]=ptC;
  gptr[1]=ptdep;
  gptr[2]=ptB;
  gptr[3]=&H; gerepilemany(av,gptr,4);
  if (DEBUGLEVEL)
    msgtimer("hnfspec [%ld x %ld] --> [%ld x %ld]",li-1,co-1, lig-1,col-1);
  return H;
}

/* HNF reduce x, apply same transforms to C */
GEN
mathnfspec(GEN x, GEN *ptperm, GEN *ptdep, GEN *ptB, GEN *ptC)
{
  long i,j,k,ly,lx = lg(x);
  GEN p1,p2,z,perm;
  if (lx == 1) return gcopy(x);
  ly = lg(x[1]);
  z = cgetg(lx,t_MAT);
  perm = cgetg(ly,t_VECSMALL); *ptperm = perm;
  for (i=1; i<ly; i++) perm[i] = i;
  for (i=1; i<lx; i++)
  {
    p1 = cgetg(ly,t_COL); z[i] = (long)p1;
    p2 = (GEN)x[i];
    for (j=1; j<ly; j++) 
    {
      if (is_bigint(p2[j])) goto TOOLARGE;
      p1[j] = itos((GEN)p2[j]);
    }
  }
  /*  [ dep |     ]
   *  [-----|  B  ]
   *  [  H  |     ]
   *  [-----|-----]
   *  [  0  | Id  ] */
  return hnfspec((long**)z,perm, ptdep, ptB, ptC, 0);

TOOLARGE:
  if (lg(*ptC) > 1 && lg((*ptC)[1]) > 1)
    err(impl,"mathnfspec with large entries");
  x = hnf(x); lx = lg(x); j = ly; k = 0;
  for (i=1; i<ly; i++)
  {
    if (gcmp1(gcoeff(x,i,i + lx-ly)))
      perm[--j] = i;
    else
      perm[++k] = i;
  }
  setlg(perm,k+1);
  x = rowextract_p(x, perm); /* upper part */
  setlg(perm,ly);
  *ptB = vecextract_i(x, j+lx-ly, lx-1);
  setlg(x, j);
  *ptdep = rowextract_i(x, 1, lx-ly);
  return rowextract_i(x, lx-ly+1, k); /* H */
}

/* add new relations to a matrix treated by hnfspec (extramat / extraC) */
GEN
hnfadd(GEN H, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, /* cf hnfspec */
       GEN extramat,GEN extraC)
{
  GEN p1,p2,p3,matb,extratop,Cnew,permpro;
  GEN B=*ptB, C=*ptC, dep=*ptdep, *gptr[4];
  gpmem_t av = avma;
  long i,j,lextra,colnew;
  long li = lg(perm);
  long co = lg(C);
  long lB = lg(B);
  long lig = li - lB;
  long col = co - lB;
  long lH = lg(H)-1;
  long nlze = lH? lg(dep[1])-1: lg(B[1])-1;

  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnfadd:\n");
    if (DEBUGLEVEL>6) fprintferr("extramat = %Z\n",extramat);
  }
 /*               col    co
  *       [ 0 |dep |     ]
  *  nlze [--------|  B  ]
  *       [ 0 | H  |     ]
  *       [--------|-----] lig
  *       [   0    | Id  ]
  *       [        |     ] li */
  lextra = lg(extramat)-1;
  extratop = cgetg(lextra+1,t_MAT); /* [1..lig] part (top) */
  p2 = cgetg(lextra+1,t_MAT); /* bottom */
  for (j=1; j<=lextra; j++)
  {
    GEN z = (GEN)extramat[j];
    p1=cgetg(lig+1,t_COL); extratop[j] = (long)p1;
    for (i=1; i<=lig; i++) p1[i] = z[i];
    p1=cgetg(lB,t_COL); p2[j] = (long)p1;
    p1 -= lig;
    for (   ; i<li; i++) p1[i] = z[i];
  }
  if (li-1 != lig)
  { /* zero out bottom part, using the Id block */
    GEN A = cgetg(lB,t_MAT);
    for (j=1; j<lB; j++) A[j] = C[j+col];
    extraC   = gsub(extraC,  gmul(A,p2));
    extratop = gsub(extratop,gmul(B,p2));
  }

  colnew = lH + lextra;
  extramat = cgetg(colnew+1,t_MAT);
  Cnew = cgetg(lB+colnew,t_MAT);
  for (j=1; j<=lextra; j++)
  {
    extramat[j] = extratop[j];
    Cnew[j] = extraC[j];
  }
  for (   ; j<=colnew; j++)
  {
    p1 = cgetg(lig+1,t_COL); extramat[j] = (long)p1;
    p2 = (GEN)dep[j-lextra]; for (i=1; i<=nlze; i++) p1[i] = p2[i];
    p2 = (GEN)  H[j-lextra]; for (   ; i<=lig ; i++) p1[i] = p2[i-nlze];
  }
  for (j=lextra+1; j<lB+colnew; j++)
    Cnew[j] = C[j-lextra+col-lH];
  if (DEBUGLEVEL>5)
  {
    fprintferr("    1st phase done\n");
    if (DEBUGLEVEL>6) fprintferr("extramat = %Z\n",extramat);
  }
  permpro = imagecomplspec(extramat, &nlze);
  p1 = new_chunk(lig+1);
  for (i=1; i<=lig; i++) p1[i] = perm[permpro[i]];
  for (i=1; i<=lig; i++) perm[i] = p1[i];

  matb = cgetg(colnew+1,t_MAT);
  dep = cgetg(colnew+1,t_MAT);
  for (j=1; j<=colnew; j++)
  {
    GEN z = (GEN)extramat[j];
    p1=cgetg(nlze+1,t_COL); dep[j]=(long)p1;
    p2=cgetg(lig+1-nlze,t_COL); matb[j]=(long)p2;
    p2 -= nlze;
    for (i=1; i<=nlze; i++) p1[i] = z[permpro[i]];
    for (   ; i<= lig; i++) p2[i] = z[permpro[i]];
  }
  p3 = cgetg(lB,t_MAT);
  for (j=1; j<lB; j++)
  {
    p2 = (GEN)B[j];
    p1 = cgetg(lig+1,t_COL); p3[j] = (long)p1;
    for (i=1; i<=lig; i++) p1[i] = p2[permpro[i]];
  }
  B = p3;
  if (DEBUGLEVEL>5) fprintferr("    2nd phase done\n");
  *ptdep = dep;
  *ptB = B;
  H = hnffinal(matb,perm,ptdep,ptB,&Cnew);
  p1 = cgetg(co+lextra,t_MAT);
  for (j=1; j <= col-lH; j++)   p1[j] = C[j];
  C = Cnew - (col-lH);
  for (   ; j < co+lextra; j++) p1[j] = C[j];

  gptr[0]=ptC; *ptC=p1;
  gptr[1]=ptdep;
  gptr[2]=ptB; 
  gptr[3]=&H; gerepilemany(av,gptr,4);
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>7) fprintferr("mit = %Z\nC = %Z\n",H,*ptC);
    msgtimer("hnfadd (%ld)",lextra);
  }
  return H;
}

static void
ZV_neg(GEN x)
{
  long i, lx = lg(x);
  for (i=1; i<lx ; i++) x[i]=lnegi((GEN)x[i]);
}

/* zero aj = Aij (!= 0)  using  ak = Aik (maybe 0), via linear combination of
 * A[j] and A[k] of determinant 1. If U != NULL, likewise update its columns */
static void
ZV_elem(GEN aj, GEN ak, GEN A, GEN U, long j, long k)
{
  GEN p1,u,v,d;

  if (!signe(ak)) { lswap(A[j],A[k]); if (U) lswap(U[j],U[k]); return; }
  d = bezout(aj,ak,&u,&v);
  /* frequent special case (u,v) = (1,0) or (0,1) */
  if (!signe(u))
  { /* ak | aj */
    p1 = negi(divii(aj,ak));
    A[j]   = (long)ZV_lincomb(gun, p1, (GEN)A[j], (GEN)A[k]);
    if (U)
      U[j] = (long)ZV_lincomb(gun, p1, (GEN)U[j], (GEN)U[k]);
    return;
  }
  if (!signe(v))
  { /* aj | ak */
    p1 = negi(divii(ak,aj));
    A[k]   = (long)ZV_lincomb(gun, p1, (GEN)A[k], (GEN)A[j]);
    lswap(A[j], A[k]);
    if (U) {
      U[k] = (long)ZV_lincomb(gun, p1, (GEN)U[k], (GEN)U[j]);
      lswap(U[j], U[k]);
    }
    return;
  }

  if (!is_pm1(d)) { aj = divii(aj,d); ak = divii(ak,d); }
  p1 = (GEN)A[k]; aj = negi(aj);
  A[k] = (long)ZV_lincomb(u,v, (GEN)A[j],p1);
  A[j] = (long)ZV_lincomb(aj,ak, p1,(GEN)A[j]);
  if (U)
  {
    p1 = (GEN)U[k];
    U[k] = (long)ZV_lincomb(u,v, (GEN)U[j],p1);
    U[j] = (long)ZV_lincomb(aj,ak, p1,(GEN)U[j]);
  }
}

/* reduce A[i,j] mod A[i,j0] for j=j0+1... via column operations */
static void
ZM_reduce(GEN A, GEN U, long i, long j0)
{
  long j, lA = lg(A);
  GEN d = gcoeff(A,i,j0);
  if (signe(d) < 0)
  {
    ZV_neg((GEN)A[j0]);
    if (U) ZV_neg((GEN)U[j0]);
    d = gcoeff(A,i,j0);
  }
  for (j=j0+1; j<lA; j++)
  {
    GEN q = truedvmdii(gcoeff(A,i,j), d, NULL);
    if (!signe(q)) continue;

    q = negi(q);
    A[j] = (long)ZV_lincomb(gun,q, (GEN)A[j], (GEN)A[j0]);
    if (U)
      U[j] = (long)ZV_lincomb(gun,q,(GEN)U[j],(GEN)U[j0]);
  }
}

/* remove: throw away lin.dep.columns */
GEN
hnf0(GEN A, int remove)
{
  gpmem_t av0 = avma, av, tetpil, lim;
  long s,li,co,i,j,k,def,ldef;
  GEN denx,a,p1;

  if (typ(A) == t_VEC) return hnf_special(A,remove);
  A = init_hnf(A,&denx,&co,&li,&av);
  if (!A) return cgetg(1,t_MAT);

  lim = stack_lim(av,1);
  def=co-1; ldef=(li>co)? li-co: 0;
  for (i=li-1; i>ldef; i--)
  {
    for (j=def-1; j; j--)
    {
      a = gcoeff(A,i,j);
      if (!signe(a)) continue;

      /* zero a = Aij  using  b = Aik */
      k = (j==1)? def: j-1;
      ZV_elem(a,gcoeff(A,i,k), A,NULL, j,k);

      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"hnf[1]. i=%ld",i);
        tetpil=avma; A=gerepile(av,tetpil,ZM_copy(A));
      }
    }
    p1 = gcoeff(A,i,def); s = signe(p1);
    if (s)
    {
      if (s < 0) ZV_neg((GEN)A[def]);
      ZM_reduce(A, NULL, i,def);
      def--;
    }
    else
      if (ldef) ldef--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"hnf[2]. i=%ld",i);
      tetpil=avma; A=gerepile(av,tetpil,ZM_copy(A));
    }
  }
  if (remove)
  {                            /* remove null columns */
    for (i=1,j=1; j<co; j++)
      if (!gcmp0((GEN)A[j])) A[i++] = A[j];
    setlg(A,i);
  }
  tetpil=avma;
  A = denx? gdiv(A,denx): ZM_copy(A);
  return gerepile(av0,tetpil,A);
}

GEN
hnf(GEN x) { return hnf0(x,1); }

/* dm = multiple of diag element (usually detint(x)) */
/* flag: don't/do append dm*matid. */
static GEN
allhnfmod(GEN x,GEN dm,int flag)
{
  gpmem_t av,tetpil,lim;
  long li,co,i,j,k,def,ldef,ldm;
  GEN a,b,w,p1,p2,d,u,v;

  if (typ(dm)!=t_INT) err(typeer,"allhnfmod");
  if (!signe(dm)) return hnf(x);
  if (typ(x)!=t_MAT) err(typeer,"allhnfmod");

  co=lg(x); if (co==1) return cgetg(1,t_MAT);
  li=lg(x[1]);
  av = avma; lim = stack_lim(av,1);
  x = dummycopy(x);

  if (flag)
  {
    if (li > co) err(talker,"nb lines > nb columns in hnfmod");
  }
  else
  { /* concatenate dm * Id to x */
    x = concatsp(x, idmat_intern(li-1,dm,gzero));
    co += li-1;
  }
  /* Avoid wasteful divisions. we only want to prevent coeff explosion, so
   * only reduce mod dm when lg(coeff) > ldm */
  ldm = lgefint(dm);
  def = co-1; ldef = 0;
  for (i=li-1; i>ldef; i--,def--)
    for (j=def-1; j; j--)
    {
      coeff(x,i,j) = lresii(gcoeff(x,i,j), dm);
      a = gcoeff(x,i,j);
      if (!signe(a)) continue;

      k = (j==1)? def: j-1;
      /* do not reduce the appended dm [hnfmodid] */
      if (flag || j != 1) coeff(x,i,k) = lresii(gcoeff(x,i,k), dm);
      ZV_elem(a,gcoeff(x,i,k), x,NULL, j,k);
      p1 = (GEN)x[j];
      p2 = (GEN)x[k];
      for (k=1; k<i; k++)
      {
        if (lgefint(p1[k]) > ldm) p1[k] = lresii((GEN)p1[k], dm);
        if (lgefint(p2[k]) > ldm) p2[k] = lresii((GEN)p2[k], dm);
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"allhnfmod[1]. i=%ld",i);
	tetpil=avma; x=gerepile(av,tetpil,ZM_copy(x));
      }
    }
  w = cgetg(li,t_MAT); b = dm;
  for (i=li-1; i>=1; i--)
  {
    d = bezout(gcoeff(x,i,i+def),b,&u,&v);
    w[i] = lmod(gmul(u,(GEN)x[i+def]), b);
    if (!signe(gcoeff(w,i,i))) coeff(w,i,i) = (long)d;
    if (flag && i > 1) b = diviiexact(b,d);
  }
  if (flag)
  { /* compute optimal value for dm */
    dm = gcoeff(w,1,1);
    for (i=2; i<li; i++) dm = mpppcm(dm, gcoeff(w,i,i));
    ldm = lgefint(dm);
  }
  for (i=li-2; i>=1; i--)
  {
    GEN diag = gcoeff(w,i,i);
    for (j=i+1; j<li; j++)
    {
      b = negi(truedvmdii(gcoeff(w,i,j), diag, NULL));
      p1 = ZV_lincomb(gun,b, (GEN)w[j], (GEN)w[i]);
      w[j] = (long)p1;
      for (k=1; k<i; k++)
        if (lgefint(p1[k]) > ldm) p1[k] = lresii((GEN)p1[k], dm);
      if (low_stack(lim, stack_lim(av,1)))
      {
        GEN *gptr[2]; gptr[0]=&w; gptr[1]=&dm;
        if (DEBUGMEM>1) err(warnmem,"allhnfmod[2]. i=%ld", i);
        gerepilemany(av,gptr,2); diag = gcoeff(w,i,i);
      }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,ZM_copy(w));
}

GEN
hnfmod(GEN x, GEN detmat) { return allhnfmod(x,detmat,1); }

GEN
hnfmodid(GEN x, GEN p) { return allhnfmod(x,p,0); }

/***********************************************************************/
/*                                                                     */
/*                 HNFLLL (Havas, Majewski, Mathews)                   */
/*                                                                     */
/***********************************************************************/

/* negate in place, except universal constants */
static GEN
mynegi(GEN x)
{
  static long mun[]={evaltyp(t_INT)|_evallg(3),evalsigne(-1)|evallgefint(3),1};
  long s = signe(x);

  if (!s) return gzero;
  if (is_pm1(x))
    return (s>0)? mun: gun;
  setsigne(x,-s); return x;
}

/* We assume y > 0 */
static GEN
divnearest(GEN x, GEN y)
{
  GEN r, q = dvmdii(x,y,&r);
  long s=signe(r), t;
  gpmem_t av = avma;

  if (!s) { cgiv(r); return q; }
  if (s<0) r = mynegi(r);

  y = shifti(y,-1); t = cmpii(r,y);
  avma=av; cgiv(r);
  if (t < 0 || (t == 0 && s > 0)) return q;
  return addsi(s,q);
}

static void
Minus(long j, GEN **lambda)
{
  long k, n = lg(lambda);

  for (k=1  ; k<j; k++) lambda[j][k] = mynegi(lambda[j][k]);
  for (k=j+1; k<n; k++) lambda[k][j] = mynegi(lambda[k][j]);
}

static void
neg_col(GEN M)
{
  long i;
  for (i = lg(M)-1; i; i--)
    M[i] = (long)mynegi((GEN)M[i]);
}

/* M_k = M_k + q M_i  (col operations) */
static void
elt_col(GEN Mk, GEN Mi, GEN q)
{
  long j;
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (j = lg(Mk)-1; j; j--)
        if (signe(Mi[j])) Mk[j] = laddii((GEN)Mk[j], (GEN)Mi[j]);
    }
    else
    {
      for (j = lg(Mk)-1; j; j--)
        if (signe(Mi[j])) Mk[j] = lsubii((GEN)Mk[j], (GEN)Mi[j]);
    }
  }
  else
    for (j = lg(Mk)-1; j; j--)
      if (signe(Mi[j])) Mk[j] = laddii((GEN)Mk[j], mulii(q, (GEN)Mi[j]));
}

/* index of first non-zero entry */
static long
findi(GEN M)
{
  long i, n = lg(M);
  for (i=1; i<n; i++)
    if (signe(M[i])) return i;
  return 0;
}

static long
findi_normalize(GEN Aj, GEN B, long j, GEN **lambda)
{
  long r = findi(Aj);
  if (r && signe(Aj[r]) < 0)
  {
    neg_col(Aj); if (B) neg_col((GEN)B[j]);
    Minus(j,lambda);
  }
  return r;
}

static void
reduce2(GEN A, GEN B, long k, long j, long *row, GEN **lambda, GEN *D)
{
  GEN q;
  long i, row0, row1;

  row[0] = row0 = findi_normalize((GEN)A[j], B,j,lambda);
  row[1] = row1 = findi_normalize((GEN)A[k], B,k,lambda);
  if (row0)
    q = truedvmdii(gcoeff(A,row0,k), gcoeff(A,row0,j), NULL);
  else if (absi_cmp(shifti(lambda[k][j], 1), D[j]) > 0)
    q = divnearest(lambda[k][j], D[j]);
  else
    return;

  if (signe(q))
  {
    GEN *Lk = lambda[k], *Lj = lambda[j];
    q = mynegi(q);
    if (row0) elt_col((GEN)A[k],(GEN)A[j],q);
    if (B) elt_col((GEN)B[k],(GEN)B[j],q);
    Lk[j] = addii(Lk[j], mulii(q,D[j]));
    if (is_pm1(q))
    {
      if (signe(q) > 0)
      {
        for (i=1; i<j; i++)
          if (signe(Lj[i])) Lk[i] = addii(Lk[i], Lj[i]);
      }
      else
      {
        for (i=1; i<j; i++)
          if (signe(Lj[i])) Lk[i] = subii(Lk[i], Lj[i]);
      }
    }
    else
    {
      for (i=1; i<j; i++)
        if (signe(Lj[i])) Lk[i] = addii(Lk[i], mulii(q,Lj[i]));
    }
  }
}

static void
hnfswap(GEN A, GEN B, long k, GEN **lambda, GEN *D)
{
  GEN t,p1,p2;
  long i,j,n = lg(A);

  lswap(A[k],A[k-1]);
  if (B) lswap(B[k],B[k-1]);
  for (j=k-2; j; j--) swap(lambda[k-1][j], lambda[k][j]);
  for (i=k+1; i<n; i++)
  {
    p1 = mulii(lambda[i][k-1], D[k]);
    p2 = mulii(lambda[i][k], lambda[k][k-1]);
    t = subii(p1,p2);

    p1 = mulii(lambda[i][k], D[k-2]);
    p2 = mulii(lambda[i][k-1], lambda[k][k-1]);
    lambda[i][k-1] = divii(addii(p1,p2), D[k-1]);

    lambda[i][k] = divii(t, D[k-1]);
  }
  p1 = mulii(D[k-2],D[k]);
  p2 = sqri(lambda[k][k-1]);
  D[k-1] = divii(addii(p1,p2), D[k-1]);
}

static GEN
fix_rows(GEN A)
{
  long i,j, h,n = lg(A);
  GEN cB,cA,B = cgetg(n,t_MAT);
  if (n == 1) return B;
  h = lg(A[1]);
  for (j=1; j<n; j++)
  {
    cB = cgetg(h, t_COL);
    cA = (GEN)A[j]; B[j] = (long)cB;
    for (i=h>>1; i; i--) { cB[h-i] = cA[i]; cB[i] = cA[h-i]; }
  }
  return B;
}

GEN
hnflll_i(GEN A, GEN *ptB)
{
  gpmem_t av = avma, lim = stack_lim(av,3);
  long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
  long row[2], do_swap,i,n,k;
  GEN z,B, **lambda, *D;
  GEN *gptr[4];

  if (typ(A) != t_MAT) err(typeer,"hnflll");
  n = lg(A);
  A = ZM_copy(fix_rows(A));
  B = ptB? idmat(n-1): NULL;
  D = (GEN*)cgetg(n+1,t_VEC); lambda = (GEN**) cgetg(n,t_MAT);
  D++;
  for (i=0; i<n; i++) D[i] = gun;
  for (i=1; i<n; i++) lambda[i] = (GEN*)zerocol(n-1);
  k = 2;
  while (k < n)
  {
    reduce2(A,B,k,k-1,row,lambda,D);
    if (row[0])
      do_swap = (!row[1] || row[0] <= row[1]);
    else if (!row[1])
    { /* row[0] == row[1] == 0 */
      gpmem_t av1 = avma;
      z = addii(mulii(D[k-2],D[k]), sqri(lambda[k][k-1]));
      do_swap = (cmpii(mulsi(n1,z), mulsi(m1,sqri(D[k-1]))) < 0);
      avma = av1;
    }
    else
      do_swap = 0;
    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k > 2) k--;
    }
    else
    {
      for (i=k-2; i; i--)
      {
        reduce2(A,B,k,i,row,lambda,D);
        if (low_stack(lim, stack_lim(av,3)))
        {
          GEN a = (GEN)lambda, b = (GEN)(D-1); /* gcc -Wall */
          gptr[0]=&A; gptr[1]=&a; gptr[2]=&b; gptr[3]=&B; 
          if (DEBUGMEM) err(warnmem,"hnflll (reducing), i = %ld",i);
          gerepilemany(av,gptr,B? 4: 3); lambda = (GEN**)a; D = (GEN*)(b+1);
        }
      }
      k++;
    }
    if (low_stack(lim, stack_lim(av,3)))
    {
      GEN a = (GEN)lambda, b = (GEN)(D-1); /* gcc -Wall */
      gptr[0]=&A; gptr[1]=&a; gptr[2]=&b; gptr[3]=&B; 
      if (DEBUGMEM) err(warnmem,"hnflll, k = %ld / %ld",k,n);
      gerepilemany(av,gptr,B? 4: 3); lambda = (GEN**)a; D = (GEN*)(b+1);
    }
  }
  /* handle trivial case: return negative diag coeff otherwise */
  if (n == 2) (void)findi_normalize((GEN)A[1], B,1,lambda);
  A = fix_rows(A);
  gptr[0] = &A; gptr[1] = &B;
  gerepilemany(av, gptr, B? 2: 1);
  if (B) *ptB = B;
  return A;
}

GEN
hnflll(GEN A)
{
  GEN B, z = cgetg(3, t_VEC);
  z[1] = (long)hnflll_i(A, &B);
  z[2] = (long)B; return z;
}

/* Variation on HNFLLL: Extended GCD */

static void
reduce1(GEN A, GEN B, long k, long j, GEN **lambda, GEN *D)
{
  GEN q;
  long i;

  if (signe(A[j]))
    q = divnearest((GEN)A[k],(GEN)A[j]);
  else if (absi_cmp(shifti(lambda[k][j], 1), D[j]) > 0)
    q = divnearest(lambda[k][j], D[j]);
  else
    return;

  if (signe(q))
  {
    GEN *Lk = lambda[k], *Lj = lambda[j];
    q = mynegi(q);
    A[k] = laddii((GEN)A[k], mulii(q,(GEN)A[j]));
    elt_col((GEN)B[k],(GEN)B[j],q);
    Lk[j] = addii(Lk[j], mulii(q,D[j]));
    for (i=1; i<j; i++)
      if (signe(Lj[i])) Lk[i] = addii(Lk[i], mulii(q,Lj[i]));
  }
}

GEN
extendedgcd(GEN A)
{
  long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
  gpmem_t av = avma;
  long do_swap,i,n,k;
  GEN z,B, **lambda, *D;

  n = lg(A);
  A = dummycopy(A);
  B = idmat(n-1);
  D = (GEN*)new_chunk(n); lambda = (GEN**) cgetg(n,t_MAT);
  for (i=0; i<n; i++) D[i] = gun;
  for (i=1; i<n; i++) lambda[i] = (GEN*)zerocol(n-1);
  k = 2;
  while (k < n)
  {
    reduce1(A,B,k,k-1,lambda,D);
    if (signe(A[k-1])) do_swap = 1;
    else if (!signe(A[k]))
    {
      gpmem_t av1 = avma;
      z = addii(mulii(D[k-2],D[k]), sqri(lambda[k][k-1]));
      do_swap = (cmpii(mulsi(n1,z), mulsi(m1,sqri(D[k-1]))) < 0);
      avma = av1;
    }
    else do_swap = 0;

    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k > 2) k--;
    }
    else
    {
      for (i=k-2; i; i--) reduce1(A,B,k,i,lambda,D);
      k++;
    }
  }
  if (signe(A[n-1]) < 0)
  {
    A[n-1] = (long)mynegi((GEN)A[n-1]);
    neg_col((GEN)B[n-1]);
  }
  z = cgetg(3,t_VEC);
  z[1] = A[n-1];
  z[2] = (long)B;
  return gerepilecopy(av, z);
}

/* HNF with permutation. TODO: obsolete, replace with hnflll. */
GEN
hnfperm(GEN A)
{
  GEN U,c,l,perm,d,u,p,q,y,b;
  gpmem_t av=avma,av1,tetpil,lim;
  long r,t,i,j,j1,k,m,n;

  if (typ(A) != t_MAT) err(typeer,"hnfperm");
  n = lg(A)-1;
  if (!n)
  {
    y = cgetg(4,t_VEC);
    y[1] = lgetg(1,t_MAT);
    y[2] = lgetg(1,t_MAT);
    y[3] = lgetg(1,t_VEC); return y;
  }
  m = lg(A[1])-1;
  c = cgetg(m+1,t_VECSMALL); for (i=1; i<=m; i++) c[i]=0;
  l = cgetg(n+1,t_VECSMALL); for (j=1; j<=n; j++) l[j]=0;
  perm = cgetg(m+1, t_VECSMALL);
  av1 = avma; lim = stack_lim(av1,1);
  U = idmat(n); A = dummycopy(A); /* U base change matrix : A0*U=A all along */
  for (r=0,k=1; k<=n; k++)
  {
    for (j=1; j<k; j++)
    {
      if (!l[j]) continue;
      t=l[j]; b=gcoeff(A,t,k);
      if (!signe(b)) continue;

      ZV_elem(b,gcoeff(A,t,j), A,U,k,j);
      d = gcoeff(A,t,j);
      if (signe(d) < 0)
      {
        ZV_neg((GEN)A[j]);
        ZV_neg((GEN)U[j]);
        d = gcoeff(A,t,j);
      }
      for (j1=1; j1<j; j1++)
      {
        if (!l[j1]) continue;
        q = truedvmdii(gcoeff(A,t,j1),d,NULL);
        if (!signe(q)) continue;

        q = negi(q);
        A[j1] = (long)ZV_lincomb(gun,q,(GEN)A[j1],(GEN)A[j]);
        U[j1] = (long)ZV_lincomb(gun,q,(GEN)U[j1],(GEN)U[j]);
      }
    }
    t=m; while (t && (c[t] || !signe(gcoeff(A,t,k)))) t--;
    if (t)
    {
      p = gcoeff(A,t,k);
      for (i=t-1; i; i--)
      {
        q = gcoeff(A,i,k);
	if (signe(q) && absi_cmp(p,q) > 0) { p=q; t=i; }
      }
      perm[++r]=l[k]=t; c[t]=k;
      if (signe(p) < 0)
      {
        ZV_neg((GEN)A[k]);
        ZV_neg((GEN)U[k]);
	p = gcoeff(A,t,k);
      }
      for (j=1; j<k; j++)
      {
        if (!l[j]) continue;
	q = truedvmdii(gcoeff(A,t,j),p,NULL);
	if (!signe(q)) continue;

        q = negi(q);
        A[j] = (long)ZV_lincomb(gun,q,(GEN)A[j],(GEN)A[k]);
        U[j] = (long)ZV_lincomb(gun,q,(GEN)U[j],(GEN)U[k]);
      }
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[2]; gptr[0]=&A; gptr[1]=&U;
      if (DEBUGMEM>1) err(warnmem,"hnfperm");
      gerepilemany(av1,gptr,2);
    }
  }
  if (r < m)
  {
    for (i=1,k=r; i<=m; i++)
      if (c[i]==0) perm[++k] = i;
  }

/* We have A0*U=A, U in Gl(n,Z)
 * basis for Im(A):  columns of A s.t l[j]>0 (r   cols)
 * basis for Ker(A): columns of U s.t l[j]=0 (n-r cols)
 */
  tetpil=avma; y=cgetg(4,t_VEC);
  p=cgetg(r+1,t_MAT); u=cgetg(n+1,t_MAT);
  for (t=1,k=r,j=1; j<=n; j++)
    if (l[j])
    {
      q=cgetg(m+1,t_COL); p[k]=(long)q;
      for (i=1; i<=m; i++) q[i]=lcopy(gcoeff(A,perm[m-i+1],j));
      u[k+n-r]=lcopy((GEN)U[j]);
      k--;
    }
    else u[t++]=lcopy((GEN)U[j]);
  y[1]=(long)p; y[2]=(long)u;
  q = cgetg(m+1,t_VEC); y[3]=(long)q;
  for (i=1; i<=m; i++) q[m-i+1]=lstoi(perm[i]);
  return gerepile(av,tetpil,y);
}

/*====================================================================
 *	    Forme Normale d'Hermite (Version par colonnes 31/01/94)
 *====================================================================*/
GEN
hnfall_i(GEN A, GEN *ptB, long remove)
{
  GEN B,c,h,x,p,a;
  gpmem_t av=avma,av1,tetpil,lim;
  long m,n,r,i,j,k,li;
  GEN *gptr[2]; 

  if (typ(A)!=t_MAT) err(typeer,"hnfall");
  n=lg(A)-1;
  if (!n)
  {
    if (ptB) *ptB = cgetg(1,t_MAT);
    return cgetg(1,t_MAT);
  }
  m = lg(A[1])-1;
  c = cgetg(m+1,t_VECSMALL); for (i=1; i<=m; i++) c[i]=0;
  h = cgetg(n+1,t_VECSMALL); for (j=1; j<=n; j++) h[j]=m;
  av1 = avma; lim = stack_lim(av1,1);
  A = dummycopy(A);
  B = ptB? idmat(n): NULL;
  r = n+1;
  for (li=m; li; li--)
  {
    for (j=1; j<r; j++)
    {
      for (i=h[j]; i>li; i--)
      {
        a = gcoeff(A,i,j);
	if (!signe(a)) continue;

        k = c[i]; /* zero a = Aij  using  Aik */
        ZV_elem(a,gcoeff(A,i,k), A,B,j,k);
        ZM_reduce(A,B, i,k);
        if (low_stack(lim, stack_lim(av1,1)))
        {
          tetpil = avma;
          A = ZM_copy(A); gptr[0]=&A;
          if (B) { B = ZM_copy(B); gptr[1]=&B; }
          if (DEBUGMEM>1) err(warnmem,"hnfall[1], li = %ld", li);
          gerepilemanysp(av1,tetpil,gptr,B? 2: 1);
        }	
      }
      x = gcoeff(A,li,j); if (signe(x)) break;
      h[j] = li-1;
    }
    if (j == r) continue;
    r--;
    if (j < r) /* A[j] != 0 */
    {
      lswap(A[j], A[r]);
      if (B) lswap(B[j], B[r]);
      h[j]=h[r]; h[r]=li; c[li]=r;
    }
    p = gcoeff(A,li,r);
    if (signe(p) < 0)
    {
      ZV_neg((GEN)A[r]);
      if (B) ZV_neg((GEN)B[r]);
      p = gcoeff(A,li,r);
    }
    ZM_reduce(A,B, li,r);
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[2]; gptr[0]=&A; gptr[1]=&B;
      if (DEBUGMEM>1) err(warnmem,"hnfall[2], li = %ld", li);
      gerepilemany(av1,gptr,B? 2: 1);
    }	
  }
  if (DEBUGLEVEL>5) fprintferr("\nhnfall, final phase: ");
  r--; /* first r cols are in the image the n-r (independent) last ones */
  for (j=1; j<=r; j++)
    for (i=h[j]; i; i--)
    { 
      a = gcoeff(A,i,j);
      if (!signe(a)) continue;

      k = c[i];
      ZV_elem(a,gcoeff(A,i,k), A,B, j,k);
      ZM_reduce(A,B, i,k);
      if (low_stack(lim, stack_lim(av1,1)))
      {
        tetpil = avma;
        A = ZM_copy(A); gptr[0]=&A;
        if (B) { B = ZM_copy(B); gptr[1]=&B; }
        if (DEBUGMEM>1) err(warnmem,"hnfall[3], j = %ld", j);
        gerepilemanysp(av1,tetpil,gptr, B? 2: 1);
      }	
    }
  if (DEBUGLEVEL>5) fprintferr("\n");
  /* remove the first r columns */
  if (remove) { A += r; A[0] = evaltyp(t_MAT) | evallg(n-r+1); }
  gptr[0] = &A; gptr[1] = &B;
  gerepilemany(av, gptr, B? 2: 1);
  if (B) *ptB = B;
  return A;
}

GEN
hnfall0(GEN A, long remove)
{
  GEN B, z = cgetg(3, t_VEC);
  z[1] = (long)hnfall_i(A, &B, remove);
  z[2] = (long)B; return z;
}

GEN
hnfall(GEN x) {return hnfall0(x,1);}

/***************************************************************/
/**							      **/
/**      	    SMITH NORMAL FORM REDUCTION	              **/
/**							      **/
/***************************************************************/

static GEN
col_mul(GEN x, GEN c)
{
  long s = signe(x);
  GEN xc = NULL;
  if (s)
  {
    if (!is_pm1(x)) xc = gmul(x,c);
    else xc = (s>0)? c: gneg_i(c);
  }
  return xc;
}

static void
do_zero(GEN x)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) x[i] = zero;
}

/* c1 <-- u.c1 + v.c2; c2 <-- a.c2 - b.c1 */
static void
update(GEN u, GEN v, GEN a, GEN b, GEN *c1, GEN *c2)
{
  GEN p1,p2;

  u = col_mul(u,*c1);
  v = col_mul(v,*c2);
  if (u) p1 = v? gadd(u,v): u;
  else   p1 = v? v: (GEN)NULL;

  a = col_mul(a,*c2);
  b = col_mul(gneg_i(b),*c1);
  if (a) p2 = b? gadd(a,b): a;
  else   p2 = b? b: (GEN)NULL;

  if (!p1) do_zero(*c1); else *c1 = p1;
  if (!p2) do_zero(*c2); else *c2 = p2;
}

static GEN
trivsmith(long all)
{
  GEN z;
  if (!all) return cgetg(1,t_VEC);
  z=cgetg(4,t_VEC);
  z[1]=lgetg(1,t_MAT);
  z[2]=lgetg(1,t_MAT);
  z[3]=lgetg(1,t_MAT); return z;
}

static void
snf_pile(ulong av, GEN *x, GEN *U, GEN *V)
{
  GEN *gptr[3];
  int c = 1; gptr[0]=x;
  if (*U) gptr[c++] = U;
  if (*V) gptr[c++] = V;
  gerepilemany(av,gptr,c);
}

/* Return the SNF of matrix x. If all != 0 return [d,u,v],
 * where d = u.x.v */
GEN
smithall(GEN x, GEN *ptU, GEN *ptV)
{
  gpmem_t av = avma, lim = stack_lim(av,1);
  long i,j,k,l,c,n,s1,s2;
  GEN p1,p2,p3,p4,b,u,v,d,U,V,mun,mdet,ys;

  if (typ(x)!=t_MAT) err(typeer,"smithall");
  if (DEBUGLEVEL>8) outerr(x);
  n = lg(x)-1;
  if (!n) {
    if (ptU) *ptU = cgetg(1,t_MAT);
    if (ptV) *ptV = cgetg(1,t_MAT);
    return cgetg(1,t_MAT);
  }
  if (lg(x[1]) != n+1) err(mattype1,"smithall");
  for (i=1; i<=n; i++)
    for (j=1; j<=n; j++)
      if (typ(coeff(x,i,j)) != t_INT)
        err(talker,"non integral matrix in smithall");

  U = ptU? gun: NULL;
  V = ptV? gun: NULL;
  x = dummycopy(x);
  if (ishnfall(x))
  {
    mdet = dethnf_i(x);
    if (V) V = idmat(n);
  }
  else
  {
    mdet = detint(x);
    if (signe(mdet))
    {
      p1 = hnfmod(x,mdet);
      if (V) V = gauss(x,p1);
    }
    else
    {
      p1 = hnfall_i(x, ptV, 0);
      if (ptV) V = *ptV;
    }
    x = p1;
  }
  if (U) U = idmat(n);
 
  p1=cgetg(n+1,t_VEC); for (i=1; i<=n; i++) p1[i]=lnegi(gcoeff(x,i,i));
  p2=sindexsort(p1);
  ys = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1=cgetg(n+1,t_COL); ys[j]=(long)p1;
    for (i=1; i<=n; i++) p1[i]=coeff(x,p2[i],p2[j]);
  }
  x = ys;
  if (U)
  {
    p1 = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++) p1[j]=U[p2[j]];
    U = p1;
  }
  if (V)
  {
    p1 = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++) p1[j]=V[p2[j]];
    V = p1;
  }
 
  if (signe(mdet))
  {
    p1 = hnfmod(x,mdet);
    if (V) V = gmul(V, gauss(x,p1));
  }
  else
  {
    p1 = hnfall_i(x,ptV,0);
    if (ptV) V = gmul(V, *ptV);
  }
  x = p1; mun = negi(gun);

  if (DEBUGLEVEL>7) fprintferr("starting SNF loop");
  for (i=n; i>1; i--)
  {
    if (DEBUGLEVEL>7) fprintferr("\ni = %ld: ",i);
    for(;;)
    {
      c = 0;
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(x,i,j); s1 = signe(p1);
	if (!s1) continue;
       
        p2=gcoeff(x,i,i);
        if (!absi_cmp(p1,p2))
        {
          s2=signe(p2);
          if (s1 == s2) { d=p1; u=gun; p4=gun; }
          else
          {
            if (s2>0) { u = gun; p4 = mun; }
            else      { u = mun; p4 = gun; }
            d=(s1>0)? p1: absi(p1);
          }
          v = gzero; p3 = u;
        }
        else { d=bezout(p2,p1,&u,&v); p3=divii(p2,d); p4=divii(p1,d); }
        for (k=1; k<=i; k++)
        {
          b=addii(mulii(u,gcoeff(x,k,i)),mulii(v,gcoeff(x,k,j)));
          coeff(x,k,j)=lsubii(mulii(p3,gcoeff(x,k,j)),
                              mulii(p4,gcoeff(x,k,i)));
          coeff(x,k,i)=(long)b;
        }
        if (V) update(u,v,p3,p4,(GEN*)(V+i),(GEN*)(V+j));
        if (low_stack(lim, stack_lim(av,1)))
        {
          if (DEBUGMEM>1) err(warnmem,"[1]: smithall");
          snf_pile(av, &x,&U,&V);
        }
      }
      if (DEBUGLEVEL>7) fprintferr("; ");
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(x,j,i); s1 = signe(p1);
	if (!s1) continue;
       
        p2=gcoeff(x,i,i);
        if (!absi_cmp(p1,p2))
        {
          s2 = signe(p2);
          if (s1 == s2) { d=p1; u=gun; p4=gun; }
          else
          {
            if (s2>0) { u = gun; p4 = mun; }
            else      { u = mun; p4 = gun; }
            d=(s1>0)? p1: absi(p1);
          }
          v = gzero; p3 = u;
        }
        else { d=bezout(p2,p1,&u,&v); p3=divii(p2,d); p4=divii(p1,d); }
        for (k=1; k<=i; k++)
        {
          b=addii(mulii(u,gcoeff(x,i,k)),mulii(v,gcoeff(x,j,k)));
          coeff(x,j,k)=lsubii(mulii(p3,gcoeff(x,j,k)),
                              mulii(p4,gcoeff(x,i,k)));
          coeff(x,i,k)=(long)b;
        }
        if (U) update(u,v,p3,p4,(GEN*)(U+i),(GEN*)(U+j));
        c = 1;
      }
      if (!c)
      {
	b = gcoeff(x,i,i);
	if (!signe(b)) break;
       
        for (k=1; k<i; k++)
        {
          for (l=1; l<i; l++)
            if (signe(resii(gcoeff(x,k,l),b))) break;
          if (l != i) break;
        }
        if (k == i) break;
       
        /* x[k,l] != 0 mod b */
        for (l=1; l<=i; l++)
          coeff(x,i,l) = laddii(gcoeff(x,i,l),gcoeff(x,k,l));
        if (U) U[i] = ladd((GEN)U[i],(GEN)U[k]);
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"[2]: smithall");
        snf_pile(av, &x,&U,&V);
      }
    }
  }
  if (DEBUGLEVEL>7) fprintferr("\n");
  for (k=1; k<=n; k++)
    if (signe(gcoeff(x,k,k)) < 0)
    {
      if (V) V[k]=lneg((GEN)V[k]);
      coeff(x,k,k) = lnegi(gcoeff(x,k,k));
    }
  if (!U && !V)
    return gerepileupto(av, mattodiagonal(x));
   
  if (U) U = gtrans_i(U);
  snf_pile(av, &x,&U,&V);
  if (ptU) *ptU = U;
  if (ptV) *ptV = V;
  return x;
}

GEN
smith(GEN x) { return smithall(x, NULL,NULL); }

GEN
smith2(GEN x)
{
  GEN z = cgetg(4, t_VEC);
  z[3] = (long)smithall(x, (GEN*)(z+1),(GEN*)(z+2));
  return z;
}

/* Assume z was computed by [g]smithall(). Remove the 1s on the diagonal */
GEN
smithclean(GEN z)
{
  long i,j,l,c;
  GEN u,v,y,d,p1;

  if (typ(z) != t_VEC) err(typeer,"smithclean");
  l = lg(z); if (l == 1) return cgetg(1,t_VEC);
  u=(GEN)z[1];
  if (l != 4 || typ(u) != t_MAT) 
  {
    if (typ(u) != t_INT) err(typeer,"smithclean");
    for (c=1; c<l; c++)
      if (gcmp1((GEN)z[c])) break;
    return gcopy_i(z, c);
  }
  v=(GEN)z[2]; d=(GEN)z[3]; l = lg(d);
  for (c=1; c<l; c++)
    if (gcmp1(gcoeff(d,c,c))) break;

  y=cgetg(4,t_VEC);
  y[1]=(long)(p1 = cgetg(l,t_MAT));
  for (i=1; i<l; i++) p1[i] = (long)gcopy_i((GEN)u[i], c);
  y[2]=(long)gcopy_i(v, c);
  y[3]=(long)(p1 = cgetg(c,t_MAT));
  for (i=1; i<c; i++)
  {
    GEN p2 = cgetg(c,t_COL); p1[i] = (long)p2;
    for (j=1; j<c; j++) p2[j] = i==j? lcopy(gcoeff(d,i,i)): zero;
  }
  return y;
}

static GEN
gsmithall(GEN x,long all)
{
  gpmem_t av,tetpil,lim;
  long i,j,k,l,c,n;
  GEN p1,p2,p3,p4,z,b,u,v,d,ml,mr;

  if (typ(x)!=t_MAT) err(typeer,"gsmithall");
  n=lg(x)-1;
  if (!n) return trivsmith(all);
  if (lg(x[1]) != n+1) err(mattype1,"gsmithall");
  av = avma; lim = stack_lim(av,1);
  x = dummycopy(x);
  if (all) { ml=idmat(n); mr=idmat(n); }
  for (i=n; i>=2; i--)
  {
    do
    {
      c=0;
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(x,i,j);
	if (signe(p1))
	{
	  p2=gcoeff(x,i,i);
          if (!signe(p2))
          {
            p3 = gzero; p4 = gun; u = gzero; v = gun;
          }
          else
          {
            v = gdiventres(p1,p2);
            if (gcmp0((GEN)v[2]))
              { d=p2; p4=(GEN)v[1]; v=gzero; p3=gun; u=gun; }
            else
              { d=gbezout(p2,p1,&u,&v); p3=gdiv(p2,d); p4=gdiv(p1,d); }
          }
	  for (k=1; k<=i; k++)
	  {
	    b=gadd(gmul(u,gcoeff(x,k,i)),gmul(v,gcoeff(x,k,j)));
	    coeff(x,k,j)=lsub(gmul(p3,gcoeff(x,k,j)),gmul(p4,gcoeff(x,k,i)));
	    coeff(x,k,i)=(long)b;
	  }
	  if (all) update(u,v,p3,p4,(GEN*)(mr+i),(GEN*)(mr+j));
	}
      }
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(x,j,i);
	if (signe(p1))
	{
	  p2 = gcoeff(x,i,i);
          if (!signe(p2))
          {
            p3 = gzero; p4 = gun; u = gzero; v = gun;
          }
          else
          {
            v = gdiventres(p1,p2);
            if (gcmp0((GEN)v[2]))
              { d=p2; p4=(GEN)v[1]; v=gzero; p3=gun; u=gun; }
            else
              { d=gbezout(p2,p1,&u,&v); p3=gdiv(p2,d); p4=gdiv(p1,d); }
          }
	  for (k=1; k<=i; k++)
	  {
	    b=gadd(gmul(u,gcoeff(x,i,k)),gmul(v,gcoeff(x,j,k)));
	    coeff(x,j,k)=lsub(gmul(p3,gcoeff(x,j,k)),gmul(p4,gcoeff(x,i,k)));
	    coeff(x,i,k)=(long)b;
	  }
	  if (all) update(u,v,p3,p4,(GEN*)(ml+i),(GEN*)(ml+j));
          c = 1;
	}
      }
      if (!c)
      {
	b = gcoeff(x,i,i);
	if (signe(b))
	  for (k=1; k<i; k++)
	    for (l=1; l<i; l++)
	      if (signe(gmod(gcoeff(x,k,l),b)))
              {
                for (l=1; l<=i; l++)
                  coeff(x,i,l) = ladd(gcoeff(x,i,l),gcoeff(x,k,l));
                if (all) ml[i] = ladd((GEN)ml[i],(GEN)ml[k]);
                k = l = i; c = 1;
              }
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) err(warnmem,"[5]: smithall");
	if (all)
	{
	  GEN *gptr[3]; gptr[0]=&x; gptr[1]=&ml; gptr[2]=&mr;
	  gerepilemany(av,gptr,3);
	}
	else x=gerepilecopy(av,x);
      }
    }
    while (c);
  }
  if (all)
  {
    for (k=1; k<=n; k++)
      if (signe(gcoeff(x,k,k)) < 0)
      { mr[k]=lneg((GEN)mr[k]); coeff(x,k,k)=lneg(gcoeff(x,k,k)); }
    tetpil=avma; z=cgetg(4,t_VEC);
    z[1]=ltrans(ml); z[2]=lcopy(mr); z[3]=lcopy(x);
  }
  else
  {
    tetpil=avma; z=cgetg(n+1,t_VEC);
    for (j=0,k=1; k<=n; k++) if (!signe(gcoeff(x,k,k))) z[++j]=zero;
    for (k=1; k<=n; k++)
      if (signe(p1=gcoeff(x,k,k))) z[++j]=(long)gabs(p1,0);
  }
  return gerepile(av,tetpil,z);
}

GEN
matsnf0(GEN x,long flag)
{
  gpmem_t av = avma;
  if (flag > 7) err(flagerr,"matsnf");
  if (typ(x) == t_VEC && flag & 4) return smithclean(x);
  if (flag & 2) x = flag&1 ? gsmith2(x): gsmith(x);
  else          x = flag&1 ?  smith2(x):  smith(x);
  if (flag & 4) x = gerepileupto(av, smithclean(x));
  return x;
}

GEN
gsmith(GEN x) { return gsmithall(x,0); }

GEN
gsmith2(GEN x) { return gsmithall(x,1); }
