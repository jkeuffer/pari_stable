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
  long av = avma, d;
  GEN p1, p2 = leading_term(p);

  if (!signe(x)) return gpowgs(polx[v], lgef(p)-3);
  if (typ(x) != t_POL) x = scalarpol(x,v);
  x = gneg_i(x); x[2] = ladd((GEN)x[2], polx[MAXVARN]);
  p1=subres_f(p, x, NULL);
  if (typ(p1) == t_POL && varn(p1)==MAXVARN)
    setvarn(p1,v);
  else
    p1 = gsubst(p1,MAXVARN,polx[v]);

  if (!gcmp1(p2) && (d=lgef(x)-3) > 0) p1 = gdiv(p1, gpuigs(p2,d));
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
  long l,tetpil,lx;
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
      p1=cgetg(5,t_POL);
      p1[1]=evalsigne(1) | evallgef(5) | evalvarn(v);
      p1[2]=lnorm(x); l=avma; p2=gtrace(x); tetpil=avma;
      p1[3]=lpile(l,tetpil,gneg(p2));
      p1[4]=un; return p1;

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
  long n,k,l=avma,tetpil;
  GEN  p1,p2,p3,p4,p5,p6;

  if ((p1 = easychar(x,v,NULL))) return p1;

  p1=gzero; p2=gun;
  n=lg(x)-1; if (n&1) p2=gneg_i(p2);
  p4=cgetg(3,t_RFRACN); p5=dummycopy(polx[v]); p4[2]=(long)p5;
  p6=cgeti(3); p6[1] = evalsigne(-1) | evallgefint(3);
  for (k=0; k<=n; k++)
  {
    p3=det(gsub(gscalmat(stoi(k),n), x));
    p4[1]=lmul(p3,p2); p6[2]=k;
    p1=gadd(p4,p1); p5[2]=(long)p6;
    if (k!=n) p2=gdivgs(gmulsg(k-n,p2),k+1);
  }
  p2=mpfact(n); tetpil=avma;
  return gerepile(l,tetpil,gdiv((GEN) p1[1],p2));
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
  long i,j,k,l,av,tetpil;
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
#define swap(x,y) { long _t=x; x=y; y=_t; }

GEN
hess(GEN x)
{
  long lx=lg(x),av=avma,tetpil,m,i,j;
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

      for (j=m-1; j<lx; j++) swap(coeff(x,i,j), coeff(x,m,j));
      swap(x[i], x[m]); p = ginv(p);
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
  tetpil=avma; return gerepile(av,tetpil,gcopy(x));
}

GEN
carhess(GEN x, long v)
{
  long av,tetpil,lx,r,i;
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
  long l,lx,i,tetpil, tx=typ(x);
  GEN p1,p2,y;

  switch(tx)
  {
    case t_INT:
      return sqri(x);

    case t_REAL:
      return mulrr(x,x);

    case t_FRAC: case t_FRACN:
      return gsqr(x);

    case t_COMPLEX:
      l=avma; p1=gsqr((GEN) x[1]); p2=gsqr((GEN) x[2]);
      tetpil=avma; return gerepile(l,tetpil,gadd(p1,p2));

    case t_QUAD:
      l=avma; p1=(GEN)x[1];
      p2=gmul((GEN) p1[2], gsqr((GEN) x[3]));
      p1 = gcmp0((GEN) p1[3])? gsqr((GEN) x[2])
                             : gmul((GEN) x[2], gadd((GEN) x[2],(GEN) x[3]));
      tetpil=avma; return gerepile(l,tetpil,gadd(p1,p2));

    case t_POL: case t_SER: case t_RFRAC: case t_RFRACN:
      l=avma; p1=gmul(gconj(x),x); tetpil=avma;
      return gerepile(l,tetpil,greal(p1));

    case t_POLMOD:
      p1=(GEN)x[1]; p2=leading_term(p1);
      if (gcmp1(p2) || gcmp0((GEN) x[2])) return subres(p1,(GEN) x[2]);
      l=avma; y=subres(p1,(GEN)x[2]); p1=gpuigs(p2,lgef(x[2])-3);
      tetpil=avma; return gerepile(l,tetpil,gdiv(y,p1));

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
  GEN y;
  long i,tx=typ(x),lx,av,lim;

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
  long av = avma;
  GEN y = gmul(x, realun(prec));
  if (typ(x) == t_POL)
    *++y = evaltyp(t_VEC) | evallg(lgef(x)-1);
  return gerepileupto(av, gnorml2(y));
}

GEN
gnorml1(GEN x,long prec)
{
  ulong av = avma;
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
  ulong av = avma;
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
  long lx,s,av,tetpil,i,tx=typ(x);
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
  long i,l,n,tx=typ(x),lx,tetpil;
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
	l=avma; p2=gmul2n((GEN)x[2],1);
	tetpil=avma; return gerepile(l,tetpil,gadd((GEN)x[3],p2));
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
      l=avma; n=(lgef(x[1])-4);
      p1=polsym((GEN)x[1],n); p2=gzero;
      for (i=0; i<=n; i++)
        p2=gadd(p2,gmul(truecoeff((GEN)x[2],i),(GEN)p1[i+1]));
      return gerepileupto(l,p2);

    case t_RFRAC: case t_RFRACN:
      return gadd(x,gconj(x));

    case t_VEC: case t_COL:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=ltrace((GEN)x[i]);
      return y;

    case t_MAT:
      lx=lg(x); if (lx==1) return gzero;/*now lx>=2*/
      if (lx!=lg(x[1])) err(mattype1,"gtrace");
      l=avma; p1=gcoeff(x,1,1); if (lx==2) return gcopy(p1);
      for (i=2; i<lx-1; i++)
	p1=gadd(p1,gcoeff(x,i,i));
      tetpil=avma; return gerepile(l,tetpil,gadd(p1,gcoeff(x,i,i)));

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
  GEN b,p;
  long av = avma,tetpil,i,j,k, lim=stack_lim(av,1), n=lg(a);

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
      tetpil=avma; b=gerepile(av,tetpil,gcopy(b));
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(b));
}

GEN
sqred1(GEN a)
{
  return sqred1intern(a,0);
}

GEN
sqred3(GEN a)
{
  long av=avma,tetpil,i,j,k,l, lim=stack_lim(av,1), n=lg(a);
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
      tetpil=avma; b=gerepile(av,tetpil,gcopy(b));
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(b));
}

/* Gauss reduction (arbitrary symetric matrix, only the part above the
 * diagonal is considered). If no_signature is zero, return only the
 * signature
 */
static GEN
sqred2(GEN a, long no_signature)
{
  GEN r,p,mun;
  long av,tetpil,av1,lim,n,i,j,k,l,sp,sn,t;

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
	    tetpil=avma; a=gerepile(av1,tetpil,gcopy(a));
	  }
	  break;
	}
      }
      if (k>n) break;
    }
  }
  if (no_signature) { tetpil=avma; return gerepile(av,tetpil,gcopy(a)); }
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
  long de,e,e1,e2,l,n,i,j,p,q,av1,av2;
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

GEN
matrixqz(GEN x, GEN p)
{
  long av=avma,av1,tetpil,i,j,j1,m,n,t,lim,nfact;
  GEN p1,p2,p3,unmodp;

  if (typ(x)!=t_MAT) err(typeer,"matrixqz");
  n=lg(x)-1; if (!n) return gcopy(x);
  m=lg(x[1])-1;
  if (n > m) err(talker,"more rows than columns in matrixqz");
  if (n==m)
  {
    p1=det(x);
    if (gcmp0(p1)) err(talker,"matrix of non-maximal rank in matrixqz");
    avma=av; return idmat(n);
  }
  p1=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p2=gun; p3=(GEN)x[j];
    for (i=1; i<=m; i++)
    {
      t=typ(p3[i]);
      if (t != t_INT && !is_frac_t(t))
        err(talker,"not a rational or integral matrix in matrixqz");
      p2=ggcd(p2,(GEN)p3[i]);
    }
    p1[j]=ldiv(p3,p2);
  }
  x=p1; unmodp=cgetg(3,t_INTMOD); unmodp[2]=un;

  if (gcmp0(p))
  {
    p1=cgetg(n+1,t_MAT); p2=gtrans(x);
    for (j=1; j<=n; j++) p1[j]=p2[j];
    p3=det(p1); p1[n]=p2[n+1]; p3=ggcd(p3,det(p1));
    if (!signe(p3))
      err(impl,"matrixqz when the first 2 dets are zero");
    if (gcmp1(p3))
      { tetpil=avma; return gerepile(av,tetpil,gcopy(x)); }

    p3=factor(p3); p1=(GEN)p3[1]; nfact=lg(p1)-1;
  }
  else
  {
    p1=cgetg(2,t_VEC); p1[1]=(long)p; nfact=1;
  }
  av1=avma; lim=stack_lim(av1,1);
  for (i=1; i<=nfact; i++)
  {
    p=(GEN)p1[i]; unmodp[1]=(long)p;
    for(;;)
    {
      p2=ker(gmul(unmodp,x));
      if (lg(p2)==1) break;

      p2=centerlift(p2); p3=gdiv(gmul(x,p2),p);
      for (j=1; j<lg(p2); j++)
      {
	j1=n; while (gcmp0(gcoeff(p2,j1,j))) j1--;
	x[j1] = p3[j];
      }
      if (low_stack(lim, stack_lim(av1,1)))
      {
	if (DEBUGMEM>1) err(warnmem,"matrixqz");
	tetpil=avma; x=gerepile(av1,tetpil,gcopy(x));
      }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(x));
}

static GEN
matrixqz_aux(GEN x, long m, long n)
{
  long av = avma, lim = stack_lim(av,1), tetpil,i,j,k,in[2];
  GEN p1;

  for (i=1; i<=m; i++)
  {
    for(;;)
    {
      long fl=0;

      for (j=1; j<=n; j++)
	if (!gcmp0(gcoeff(x,i,j)))
	  { in[fl]=j; fl++; if (fl==2) break; }
      if (j>n) break;

      j=(gcmp(gabs(gcoeff(x,i,in[0]),DEFAULTPREC),
	      gabs(gcoeff(x,i,in[1]),DEFAULTPREC)) > 0)? in[1]: in[0];
      p1=gcoeff(x,i,j);
      for (k=1; k<=n; k++)
	if (k!=j)
	  x[k]=lsub((GEN)x[k],gmul(ground(gdiv(gcoeff(x,i,k),p1)),(GEN)x[j]));
    }

    j=1; while (j<=n && gcmp0(gcoeff(x,i,j))) j++;
    if (j<=n)
    {
      p1=denom(gcoeff(x,i,j));
      if (!gcmp1(p1)) x[j]=lmul(p1,(GEN)x[j]);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"matrixqz_aux");
      tetpil=avma; x=gerepile(av,tetpil,gcopy(x));
    }
  }
  return hnf(x);
}

GEN
matrixqz2(GEN x)
{
  long av = avma,m,n;

  if (typ(x)!=t_MAT) err(typeer,"matrixqz2");
  n=lg(x)-1; if (!n) return gcopy(x);
  m=lg(x[1])-1; x=dummycopy(x);
  return gerepileupto(av, matrixqz_aux(x,m,n));
}

GEN
matrixqz3(GEN x)
{
  long av=avma,av1,j,j1,k,m,n,lim;
  GEN c;

  if (typ(x)!=t_MAT) err(typeer,"matrixqz3");
  n=lg(x)-1; if (!n) return gcopy(x);
  m=lg(x[1])-1; x=dummycopy(x); c=new_chunk(n+1);
  for (j=1; j<=n; j++) c[j]=0;
  av1=avma; lim=stack_lim(av1,1);
  for (k=1; k<=m; k++)
  {
    j=1; while (j<=n && (c[j] || gcmp0(gcoeff(x,k,j)))) j++;
    if (j<=n)
    {
      c[j]=k; x[j]=ldiv((GEN)x[j],gcoeff(x,k,j));
      for (j1=1; j1<=n; j1++)
	if (j1!=j) x[j1]=lsub((GEN)x[j1],gmul(gcoeff(x,k,j1),(GEN)x[j]));
      if (low_stack(lim, stack_lim(av1,1)))
      {
	long tetpil = avma;
	if(DEBUGMEM>1) err(warnmem,"matrixqz3");
	x=gerepile(av1,tetpil,gcopy(x));
      }
    }
  }
  return gerepileupto(av, matrixqz_aux(x,m,n));
}

GEN
intersect(GEN x, GEN y)
{
  long av,tetpil,j, lx = lg(x);
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
    case 2: return hnfhavas(x);
    case 3: return hnfperm(x);
    case 4: return hnflll(x);
    default: err(flagerr,"mathnf");
  }
  return NULL; /* not reached */
}

static GEN
init_hnf(GEN x, GEN *denx, long *co, long *li, long *av)
{
  if (typ(x) != t_MAT) err(typeer,"mathnf");
  *co=lg(x); if (*co==1) return NULL; /* empty matrix */
  *li=lg(x[1]); *denx=denom(x); *av=avma;

  if (gcmp1(*denx)) /* no denominator */
    { *denx = NULL; return dummycopy(x); }
  return gmul(x,*denx);
}

/* return c * X */
#ifdef INLINE
INLINE
#endif
GEN
int_col_mul(GEN c, GEN X)
{
  long i,m = lg(X);
  GEN A = new_chunk(m);
  for (i=1; i<m; i++) A[i] = lmulii(c,(GEN)X[i]);
  A[0] = X[0]; return A;
}

/* X,Y columns; u,v scalars; everybody is integral. return A = u*X + v*Y */
GEN
lincomb_integral(GEN u, GEN v, GEN X, GEN Y)
{
  long av,i,lx,m;
  GEN p1,p2,A;

  if (!signe(u)) return int_col_mul(v,Y);
  if (!signe(v)) return int_col_mul(u,X);
  lx = lg(X); A = cgetg(lx,t_COL); m = lgefint(u)+lgefint(v)+4;
  if (gcmp1(u))
  {
    for (i=1; i<lx; i++)
    {
      p1=(GEN)X[i]; p2=(GEN)Y[i];
      if      (!signe(p1)) A[i] = lmulii(v,p2);
      else if (!signe(p2)) A[i] = licopy(p1);
      else
      {
        av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2));
        p2 = mulii(v,p2);
        avma = av; A[i] = laddii(p1,p2);
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
        av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2));
        p1 = mulii(u,p1);
        p2 = mulii(v,p2);
        avma = av; A[i] = laddii(p1,p2);
      }
    }
  return A;
}

GEN
hnf_special(GEN x, long remove)
{
  long av0, s,li,co,av,tetpil,i,j,k,def,ldef,lim;
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
      while (j && !signe(gcoeff(x,i,j))) j--;
      if (!j) break;
      k = (j==1)? def: j-1;
      a = gcoeff(x,i,j);
      b = gcoeff(x,i,k); d = bezout(a,b,&u,&v);
      if (!is_pm1(d)) { a = divii(a,d); b = divii(b,d); }
      if (DEBUGLEVEL>5) { outerr(u); outerr(v); }
      p1 = (GEN)x[j]; b = negi(b);
      x[j] = (long)lincomb_integral(a,b, (GEN)x[k], p1);
      x[k] = (long)lincomb_integral(u,v, p1, (GEN)x[k]);
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
	x[j] = (long)lincomb_integral(gun,b, (GEN)x[j], (GEN)x[def]);
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
  x = denx? gdiv(x,denx): gcopy(x);
  x2 = gcopy(x2);
  {
    GEN *gptr[2]; gptr[0]=&x; gptr[1]=&x2;
    gerepilemanysp(av0,tetpil,gptr,2);
  }
  res[1] = (long)x;
  res[2] = (long)x2;
  return res;
}

GEN
hnf0(GEN x, long remove)       /* remove: throw away lin.dep.columns, GN */
{
  long av0 = avma, s,li,co,av,tetpil,i,j,k,def,ldef,lim;
  GEN p1,u,v,d,denx,a,b;

  if (typ(x) == t_VEC) return hnf_special(x,remove);
  x = init_hnf(x,&denx,&co,&li,&av);
  if (!x) return cgetg(1,t_MAT);

  lim = stack_lim(av,1);
  def=co-1; ldef=(li>co)? li-co: 0;
  for (i=li-1; i>ldef; i--)
  {
    for (j=def-1; j; j--)
    {
      while (j && !signe(gcoeff(x,i,j))) j--;
      if (!j) break;
      k = (j==1)? def: j-1;
      a = gcoeff(x,i,j);
      b = gcoeff(x,i,k); if (!signe(b)) { swap(x[j],x[k]); continue; }
      d = bezout(a,b,&u,&v);
      if (!is_pm1(d)) { a = divii(a,d); b = divii(b,d); }
      if (DEBUGLEVEL>5) { outerr(u); outerr(v); }
      p1 = (GEN)x[j];
      x[j] = (long)lincomb_integral(a,negi(b), (GEN)x[k],p1);
      x[k] = (long)lincomb_integral(u,v, p1,(GEN)x[k]);
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"hnf[1]. i=%ld",i);
        tetpil=avma; x=gerepile(av,tetpil,gcopy(x));
      }
    }
    p1 = gcoeff(x,i,def); s = signe(p1);
    if (s)
    {
      if (s < 0) { x[def] = lneg((GEN)x[def]); p1 = gcoeff(x,i,def); }
      for (j=def+1; j<co; j++)
      {
	b = negi(gdivent(gcoeff(x,i,j),p1));
	x[j] = (long)lincomb_integral(gun,b, (GEN)x[j], (GEN)x[def]);
      }
      def--;
    }
    else
      if (ldef && i==ldef+1) ldef--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"hnf[2]. i=%ld",i);
      tetpil=avma; x=gerepile(av,tetpil,gcopy(x));
    }
  }
  if (remove)
  {                            /* remove null columns */
    for (i=1,j=1; j<co; j++)
      if (!gcmp0((GEN)x[j])) x[i++] = x[j];
    setlg(x,i);
  }
  tetpil=avma;
  x = denx? gdiv(x,denx): gcopy(x);
  return gerepile(av0,tetpil,x);
}

GEN
hnf(GEN x) { return hnf0(x,1); }

#define cmod(x,u,us2) \
  {GEN a=modii((GEN)x,u); if (cmpii(a,us2)>0) a=subii(a,u); x=(long)a;}

/* dm = multiple of diag element (usually detint(x)) */
/* flag: don't/do append dm*matid. */
static GEN
allhnfmod(GEN x,GEN dm,long flag)
{
  long li,co,av0,av,tetpil,i,j,k,def,ldef,lim,ldm;
  GEN a,b,w,p1,p2,d,u,v,dms2;

  if (typ(dm)!=t_INT) err(typeer,"allhnfmod");
  if (!signe(dm)) return hnf(x);
  if (typ(x)!=t_MAT) err(typeer,"allhnfmod");
  if (DEBUGLEVEL>6) fprintferr("Enter hnfmod");

  co=lg(x); if (co==1) return cgetg(1,t_MAT);
  av0=avma; lim=stack_lim(av0,1);
  dms2=shifti(dm,-1); li=lg(x[1]);
  av=avma;

  if (flag)
  {
    p1 = cgetg(co,t_MAT); for (i=1; i<co; i++) p1[i]=x[i];
    if (li > co) err(talker,"nb lines > nb columns in hnfmod");
    x = p1;
  }
  else
  { /* concatenate dm * Id to x */
    x = concatsp(x, idmat_intern(li-1,dm,gzero));
    for (i=1; i<co; i++) x[i] = lmod((GEN)x[i], dm);
    co += li-1;
  }
  def=co-1; ldef=0;
  for (i=li-1; i>ldef; i--,def--)
  {
    if (DEBUGLEVEL>6) { fprintferr(" %ld",i); flusherr(); }
    for (j=def-1; j; j--)
    {
      while (j && !signe(gcoeff(x,i,j))) j--;
      if (!j) break;
      if (DEBUGLEVEL>8) { fprintferr(" %ld",j); flusherr(); }
      k = (j==1)? def: j-1;
      a = gcoeff(x,i,j);
      b = gcoeff(x,i,k); if (!signe(b)) { swap(x[j], x[k]); continue; }
      d = bezout(a,b,&u,&v);
      if (!is_pm1(d)) { a = divii(a,d); b = divii(b,d); }
      p1 = lincomb_integral(u,v, (GEN)x[j], (GEN)x[k]);
      p2 = lincomb_integral(a, negi(b), (GEN)x[k], (GEN)x[j]);
      x[k] = (long)p1;
      x[j] = (long)p2;
      for (k=1; k<=i; k++)
      {
        cmod(p1[k], dm, dms2);
        cmod(p2[k], dm, dms2);
      }
      if (low_stack(lim, stack_lim(av0,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"allhnfmod[1]. i=%ld",i);
	tetpil=avma; x=gerepile(av,tetpil,gcopy(x));
      }
    }
  }
  w=cgetg(li,t_MAT); b=dm;
  for (i=li-1; i>=1; i--)
  {
    d = bezout(gcoeff(x,i,i+def),b,&u,&v);
    w[i] = lmod(gmul(u,(GEN)x[i+def]), b);
    if (!signe(gcoeff(w,i,i))) coeff(w,i,i)=(long)d;
    if (i > 1 && flag) b=divii(b,d);
  }
  ldm = lgefint(dm);
  for (i=li-2; i>=1; i--)
  {
    GEN diag = gcoeff(w,i,i);
    for (j=i+1; j<li; j++)
    {
      b = negi(gdivent(gcoeff(w,i,j), diag));
      p1 = lincomb_integral(gun,b, (GEN)w[j], (GEN)w[i]);
      w[j] = (long)p1;
      for (k=1; k<i; k++)
      {
        p2 = (GEN)p1[k];
        if (lgefint(p2) > ldm) p1[k] = lmodii(p2, dm);
      }
      if (low_stack(lim, stack_lim(av0,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"allhnfmod[2]. i=%ld", i);
        tetpil=avma; w=gerepile(av,tetpil,gcopy(w));
        diag = gcoeff(w,i,i);
      }
    }
  }
  if (DEBUGLEVEL>6) { fprintferr("\nEnd hnfmod\n"); flusherr(); }
  tetpil=avma; return gerepile(av0,tetpil,gcopy(w));
}
#undef cmod

GEN
hnfmod(GEN x, GEN detmat) { return allhnfmod(x,detmat,1); }

GEN
hnfmodid(GEN x, GEN p) { return allhnfmod(x,p,0); }

/* Return [y,U,V] such that y=V.x.U, V permutation vector, U unimodular
 * matrix, and y in HNF form
 */
GEN
hnfhavas(GEN x)
{
  long av0=avma, av,av1,tetpil,li,co,i,j,k,def,ldef,lim,imin,jmin,vpk;
  long jpro,com,vi;
  GEN p1,p2,z,u,denx,vperm,mat1,col2,lil2,s,pmin,apro,bpro,cpro;

  if (DEBUGLEVEL>6)
    { fprintferr("Entering hnfhavas: AVMA = %ld\n",avma); flusherr(); }
  if (typ(x)!=t_MAT) err(typeer,"hnfhavas");
  co=lg(x);
  if (co==1)
  {
    z=cgetg(4,t_VEC); z[1]=lgetg(1,t_MAT);
    z[2]=lgetg(1,t_MAT); z[3]=lgetg(1,t_VEC);
    return z;
  }
  li=lg(x[1]); denx=denom(x);
  vperm=new_chunk(li); for (i=1; i<li; i++) vperm[i]=i;

  av=avma; lim=stack_lim(av,1); u=idmat(co-1);
  x = gcmp1(denx)? dummycopy(x): gmul(denx,x);
  def=co; ldef=(li>co)?li-co+1:1;
  imin = jmin = 0; cpro = NULL; /* for gcc -Wall */
  for (i=li-1; i>=ldef; i--)
  {
    def--; av1=avma; mat1=cgetg(def+1,t_MAT); col2=cgetg(def+1,t_COL);
    for (j=1; j<=def; j++)
    {
      p1=cgetg(i+1,t_COL); mat1[j]=(long)p1; s=gzero;
      for (k=1; k<=i; k++)
      {
	p2=gsqr(gcoeff(x,vperm[k],j));
	p1[k]=(long)p2; s=gadd(s,p2);
      }
      col2[j]=(long)s;
    }
    lil2=cgetg(i+1,t_COL);
    for (k=1; k<=i; k++)
    {
      s=gzero;
      for (j=1; j<=def; j++) s=gadd(s,gcoeff(mat1,k,j));
      lil2[k]=(long)s;
    }

    pmin = NULL;
    for (k=i; k>=1; k--)
    {
      while (k>=1 && !signe(lil2[k])) k--;
      if (!k) goto comterm;
      vpk=vperm[k];
      if (!pmin || cmpii((GEN)lil2[k],pmin) <= 0)
      {
	j=1; while (!signe(gcoeff(x,vpk,j))) j++;
	if (!pmin)
	{
	  imin=k; jmin=j; pmin=mulii((GEN)lil2[k],(GEN)col2[j]);
	  cpro=absi(gcoeff(x,vpk,j));
	}
	jpro=j; apro=absi(gcoeff(x,vpk,j)); j++;
	for (; j<=def; j++)
	{
	  com=cmpii((GEN)col2[j],(GEN)col2[jpro]);
	  if (signe(gcoeff(x,vpk,j)) && com <=0)
	  {
	    if (com<0) { jpro=j; apro=absi(gcoeff(x,vpk,j)); }
	    else
	    {
	      bpro=absi(gcoeff(x,vpk,j));
	      if (cmpii(bpro,apro)<0) { jpro=j; apro=bpro; }
	    }
	  }
	}
	p1=mulii((GEN)lil2[k],(GEN)col2[jpro]);
	com=cmpii(p1,pmin);
	if (com<0 || (com==0 && cmpii(apro,cpro)<0))
	{
	  imin=k; jmin=jpro; pmin=p1; cpro=apro;
	}
      }
    }
    avma=av1;
    if (jmin!=def)
    {
      p1=(GEN)x[def]; x[def]=x[jmin]; x[jmin]=(long)p1;
      p1=(GEN)u[def]; u[def]=u[jmin]; u[jmin]=(long)p1;
    }
    if (imin!=i) { vpk=vperm[i]; vperm[i]=vperm[imin]; vperm[imin]=vpk; }
    vi=vperm[i];
    for(;;)
    {
      GEN p3,p12,p13;

      if (signe(gcoeff(x,vi,def))<0)
      {
	x[def]=lneg((GEN)x[def]); u[def]=lneg((GEN)u[def]);
      }
      p1=gcoeff(x,vi,def); p12=shifti(p1,-1); p13=negi(p12);
      for (j=1; j<def; j++)
      {
	p2=dvmdii(gcoeff(x,vi,j),p1,&p3);
	if (cmpii(p3,p13)<0) p2=addis(p2,-1);
	else { if (cmpii(p3,p12)>0) p2=addis(p2,1); }
	if (DEBUGLEVEL>5) outerr(p2);
        setsigne(p2,-signe(p2));
	x[j]=ladd((GEN)x[j],gmul(p2,(GEN)x[def]));
	u[j]=ladd((GEN)u[j],gmul(p2,(GEN)u[def]));
      }
      j=1; while (!signe(gcoeff(x,vi,j))) j++;
      if (j<def)
      {
	pmin=gnorml2((GEN)x[j]); jmin=j; apro=absi(gcoeff(x,vi,j));
	j++;
	for (; j<def; j++)
	{
	  if (signe(gcoeff(x,vi,j)))
	  {
	    p1=gnorml2((GEN)x[j]);
            com=cmpii(p1,pmin);
	    if (com<0)
	    {
	      pmin=p1; jmin=j;
	    }
	    else if (com==0)
	    {
	      bpro=absi(gcoeff(x,vi,j));
              if (cmpii(bpro,apro)<0)
	      {
	        pmin=p1; jmin=j; apro=bpro;
	      }
	    }
	  }
	}
	p1=(GEN)x[def]; x[def]=x[jmin]; x[jmin]=(long)p1;
	p1=(GEN)u[def]; u[def]=u[jmin]; u[jmin]=(long)p1;
      }
      else break;
    }
    vi=vperm[i]; p1=gcoeff(x,vi,def);
    for (j=def+1; j<co; j++)
    {
      p2=gdivent(gcoeff(x,vi,j),p1); setsigne(p2,-signe(p2));
      if (DEBUGLEVEL>5) outerr(p2);
      x[j]=ladd((GEN)x[j],gmul(p2,(GEN)x[def]));
      u[j]=ladd((GEN)u[j],gmul(p2,(GEN)u[def]));
    }

    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[2];
      if (DEBUGMEM>1) err(warnmem,"hnfhavas");
      gptr[0]=&x; gptr[1]=&u;
      gerepilemany(av,gptr,2);
    }
  }

comterm:
  tetpil=avma; z=cgetg(4,t_VEC); p1=cgetg(co,t_MAT);
  if (gcmp1(denx))
  {
    for (j=1; j<co; j++)
    {
      p2=cgetg(li,t_COL); p1[j]=(long)p2;
      for (i=1; i<li; i++)
	p2[i] = lcopy(gcoeff(x,vperm[i],j));
    }
  }
  else
  {
    for (j=1; j<co; j++)
    {
      p2=cgetg(li,t_COL); p1[j]=(long)p2;
      for (i=1; i<li; i++)
	p2[i] = ldiv(gcoeff(x,vperm[i],j),denx);
    }
  }
  z[1]=(long)p1; z[2]=lcopy(u);
  p1=cgetg(li,t_VEC); for (i=1; i<li; i++) p1[i]=lstoi(vperm[i]);
  z[3]=(long)p1; return gerepile(av0,tetpil,z);
}

/***********************************************************************/
/*                                                                     */
/*                 HNFLLL (Havas, Majewski, Mathews)                   */
/*                                                                     */
/***********************************************************************/

/* negate in place, except universal constants */
static GEN
mynegi(GEN x)
{
  static long mun[]={evaltyp(t_INT)|m_evallg(3),evalsigne(-1)|evallgefint(3),1};
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
  long av = avma, s=signe(r), t;

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

static void
reduce2(GEN A, GEN B, long k, long j, long *row, GEN **lambda, GEN *D)
{
  GEN q;
  long i, row0, row1;

  row0 = findi((GEN)A[j]);
  if (row0 && signe(gcoeff(A,row0,j)) < 0)
  {
    neg_col((GEN)A[j]);
    neg_col((GEN)B[j]); Minus(j,lambda);
  }

  row1 = findi((GEN)A[k]);
  if (row1 && signe(gcoeff(A,row1,k)) < 0)
  {
    neg_col((GEN)A[k]);
    neg_col((GEN)B[k]); Minus(k,lambda);
  }

  row[0]=row0; row[1]=row1;
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
    elt_col((GEN)B[k],(GEN)B[j],q);
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

  swap(A[k],A[k-1]);
  swap(B[k],B[k-1]);
  for (j=k-2; j; j--)
  {
    p1 = lambda[k-1][j];
    lambda[k-1][j] = lambda[k][j];
    lambda[k][j] = p1;
  }
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
hnflll(GEN A)
{
  long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
  long av = avma, lim = stack_lim(av,3), do_swap,i,n,k, row[2];
  GEN z,B, **lambda, *D;

  if (typ(A) != t_MAT) err(typeer,"hnflll");
  n = lg(A); B = idmat(n-1); A = gcopy(fix_rows(A));
  D = (GEN*) cgetg(n+1, t_VEC); D++; /* hack: need a "sentinel" D[0] */
  if (n == 2) /* handle trivial case: return negative diag coeff otherwise */
  {
    i = findi((GEN)A[1]);
    if (i && signe(gcoeff(A,i,1)) < 0)
    {
      neg_col((GEN)A[1]);
      neg_col((GEN)B[1]);
    }
  }
  lambda = (GEN**) cgetg(n,t_MAT);
  for (i=1; i<n; i++) { D[i] = gun; lambda[i] = (GEN*)zerocol(n-1); }
  D[0] = gun; k = 2;
  while (k < n)
  {
    reduce2(A,B,k,k-1,row,lambda,D);
    if (row[0])
      do_swap = (!row[1] || row[0] <= row[1]);
    else if (row[1])
      do_swap = 0;
    else
    { /* row[0] == row[1] == 0*/
      long av1=avma;
      z = addii(mulii(D[k-2],D[k]), sqri(lambda[k][k-1]));
      z = mulsi(n1,z);
      do_swap = (cmpii(z, mulsi(m1,sqri(D[k-1]))) < 0);
      avma=av1;
    }
    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k>2) k--;
    }
    else
    {
      for (i=k-2; i; i--) reduce2(A,B,k,i,row,lambda,D);
      k++;
    }
    if (low_stack(lim, stack_lim(av,3)))
    {
      GEN a = (GEN)lambda, b = (GEN)(D-1); /* gcc -Wall */
      GEN *gptr[4]; gptr[0]=&A; gptr[1]=&B; gptr[2]=&a; gptr[3]=&b;
      if (DEBUGMEM) err(warnmem,"hnflll, k = %ld / %ld",k,n);
      gerepilemany(av,gptr,4); lambda = (GEN**)a; D = (GEN*)(b+1);
    }
  }
  for (i=1; i<n; i++)
    if (!gcmp0((GEN)A[i])) break;
  i--; A += i; A[0] = evaltyp(t_MAT)|evallg(n-i);
  A = fix_rows(A);
  z = cgetg(3,t_VEC);
  z[1] = (long)A;
  z[2] = (long)B; return gerepileupto(av, gcopy(z));
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

  if (! gcmp0(q))
  {
    q = mynegi(q);
    A[k] = laddii((GEN)A[k], mulii(q,(GEN)A[j]));
    elt_col((GEN)B[k],(GEN)B[j],q);
    lambda[k][j] = addii(lambda[k][j], mulii(q,D[j]));
    for (i=1; i<j; i++)
      if (signe(lambda[j][i]))
        lambda[k][i] = addii(lambda[k][i], mulii(q,lambda[j][i]));
  }
}

GEN
extendedgcd(GEN A)
{
  long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
  long av = avma, tetpil, do_swap,i,j,n,k;
  GEN p1,p2,B, **lambda, *D;

  n = lg(A); B = idmat(n-1); A = gcopy(A);
  D = (GEN*) cgeti(n); lambda = (GEN**) cgetg(n,t_MAT);
  for (i=0; i<n; i++) D[i] = gun;
  for (i=1; i<n; i++)
  {
    lambda[i] = (GEN*) cgetg(n,t_COL);
    for(j=1;j<n;j++) lambda[i][j] = gzero;
  }
  k = 2;
  while (k < n)
  {
    reduce1(A,B,k,k-1,lambda,D);
    if (signe(A[k-1])) do_swap = 1;
    else if (!signe(A[k]))
    {
      long av1=avma;
      p1 = addii(mulii(D[k-2],D[k]), sqri(lambda[k][k-1]));
      p1 = mulsi(n1,p1);
      p2 = mulsi(m1,sqri(D[k-1]));
      do_swap = (cmpii(p1,p2) < 0);
      avma=av1;
    }
    else do_swap = 0;

    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k>2) k--;
    }
    else
    {
      for (i=k-2; i; i--) reduce1(A,B,k,i,lambda,D);
      k++;
    }
  }
  if (signe(A[n-1])<0)
  {
    A[n-1] = (long)mynegi((GEN)A[n-1]);
    neg_col((GEN)B[n-1]);
  }
  tetpil = avma;
  p1 = cgetg(3,t_VEC);
  p1[1]=lcopy((GEN)A[n-1]);
  p1[2]=lcopy(B);
  return gerepile(av,tetpil,p1);
}

/* HNF with permutation */
GEN
hnfperm(GEN A)
{
  GEN U,c,l,perm,d,u,v,p,q,y,a,b,p1;
  long r,t,i,j,j1,k,m,n,av=avma,av1,tetpil,lim;

  if (typ(A)!=t_MAT) err(typeer,"hnfperm");
  n=lg(A)-1;
  if (!n)
  {
    y=cgetg(4,t_VEC);
    y[1]=lgetg(1,t_MAT);
    y[2]=lgetg(1,t_MAT);
    y[3]=lgetg(1,t_VEC); return y;
  }
  m=lg(A[1])-1;
  c=new_chunk(m+1); for (i=1; i<=m; i++) c[i]=0;
  l=new_chunk(n+1); for (j=1; j<=n; j++) l[j]=0;
  perm=new_chunk(m+1);
  av1=avma; lim=stack_lim(av1,1);
  U=idmat(n); A=dummycopy(A);
/* U base change matrix : A0*U=A all along */

  for (r=0,k=1; k<=n; k++)
  {
    for (j=1; j<k; j++) if (l[j])
    {
      t=l[j]; b=gcoeff(A,t,k);
      if (signe(b) == 0) continue;

      a=gcoeff(A,t,j); d=bezout(a,b,&u,&v);
      if (!is_pm1(d)) { a=divii(a,d); b=divii(b,d); }
      p1 = (GEN)A[j]; b = negi(b);
      A[j] = (long)lincomb_integral(u,v, p1,(GEN)A[k]);
      A[k] = (long)lincomb_integral(a,b, (GEN)A[k],p1);
      p1 = (GEN)U[j];
      U[j] = (long)lincomb_integral(u,v, p1,(GEN)U[k]);
      U[k] = (long)lincomb_integral(a,b, (GEN)U[k],p1);
      for (j1=1; j1<j; j1++) if (l[j1])
      {
        q=truedvmdii(gcoeff(A,t,j1),d,NULL);
        if (signe(q))
        {
          q = negi(q);
          A[j1] = (long)lincomb_integral(gun,q,(GEN)A[j1],(GEN)A[j]);
          U[j1] = (long)lincomb_integral(gun,q,(GEN)U[j1],(GEN)U[j]);
        }
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
	for (i=1; i<=m; i++) coeff(A,i,k)= lnegi(gcoeff(A,i,k));
	for (i=1; i<=n; i++) coeff(U,i,k)= lnegi(gcoeff(U,i,k));
	p=gcoeff(A,t,k);
      }
      for (j=1; j<k; j++) if (l[j])
      {
	q=truedvmdii(gcoeff(A,t,j),p,NULL);
	if (signe(q))
	{
          q = negi(q);
          A[j]=(long)lincomb_integral(gun,q,(GEN)A[j],(GEN)A[k]);
          U[j]=(long)lincomb_integral(gun,q,(GEN)U[j],(GEN)U[k]);
	}
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

GEN
colint_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) y[i] = signe(x[i])? licopy((GEN)x[i]): zero;
  return y;
}

GEN
matint_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);

  for (i=1; i<lx; i++)
    y[i] = (long)colint_copy((GEN)x[i]);
  return y;
}

/*====================================================================
 *	    Forme Normale d'Hermite (Version par colonnes 31/01/94)
 *====================================================================*/
GEN
hnfall0(GEN A, long remove)
{
  GEN U,c,h,x,y,u,v,p,q,d,a,b,p1;
  long m,n,r,i,j,j1,k,li,z,av=avma,av1,tetpil,lim;

  if (typ(A)!=t_MAT) err(typeer,"hnfall");
  n=lg(A)-1;
  if (!n)
  {
    y=cgetg(3,t_VEC);
    y[1]=lgetg(1,t_MAT);
    y[2]=lgetg(1,t_MAT); return y;
  }
  m=lg(A[1])-1;
  c=new_chunk(m+1); for (i=1; i<=m; i++) c[i]=0;
  h=new_chunk(n+1); for (j=1; j<=n; j++) h[j]=m;
  av1=avma; lim=stack_lim(av1,1);
  A=dummycopy(A); U=idmat(n); r=n+1;
  for (li=m; li; li--)
  {
    for (j=1; j<r; j++)
    {
      for (i=h[j]; i>li; i--)
      {
        b = gcoeff(A,i,j);
	if (signe(b))
	{
	  k=c[i]; a=gcoeff(A,i,k); /* annuler bij A l'aide de p=bik */
	  d=bezout(a,b,&u,&v);
	  if (DEBUGLEVEL>5)
            { fprintferr("(u,v) = (%Z, %Z); ",u,v); flusherr(); }
	  if (!is_pm1(d)) { a=divii(a,d); b =divii(b,d); }
          p1 = (GEN)A[k]; b = negi(b);
          A[k] = (long)lincomb_integral(u,v, p1,(GEN)A[j]);
          A[j] = (long)lincomb_integral(a,b, (GEN)A[j],p1);
          p1 = (GEN)U[k];
          U[k] = (long)lincomb_integral(u,v, p1,(GEN)U[j]);
          U[j] = (long)lincomb_integral(a,b, (GEN)U[j],p1);
	  for (j1=k+1; j1<=n; j1++)
	  {
	    q=truedvmdii(gcoeff(A,i,j1),d,NULL);
	    if (signe(q))
	    {
              q = negi(q);
              A[j1]=(long)lincomb_integral(gun,q,(GEN)A[j1],(GEN)A[k]);
              U[j1]=(long)lincomb_integral(gun,q,(GEN)U[j1],(GEN)U[k]);
	    }
	  }
          if (low_stack(lim, stack_lim(av1,1)))
          {
            GEN *gptr[2]; tetpil = avma;
            A = matint_copy(A); gptr[0]=&A;
            U = matint_copy(U); gptr[1]=&U;
            if (DEBUGMEM>1) err(warnmem,"hnfall[1], li = %ld", li);
            gerepilemanysp(av1,tetpil,gptr,2);
          }	
	}
      }
      x=gcoeff(A,li,j);
      if (signe(x))
      {
        r--;
        if (j<r)
        {
          z=A[j]; A[j]=A[r]; A[r]=z;
          z=U[j]; U[j]=U[r]; U[r]=z;
          h[j]=h[r]; h[r]=li; c[li]=r;
        }
        if (signe(gcoeff(A,li,r))<0)
        {
          p1=(GEN)A[r]; for (i=1; i<=li; i++) p1[i]=lnegi((GEN)p1[i]);
          p1=(GEN)U[r]; for (i=1; i<=n ; i++) p1[i]=lnegi((GEN)p1[i]);
        }
        p=gcoeff(A,li,r);
        for (j=r+1; j<=n; j++)
        {
          q = truedvmdii(gcoeff(A,li,j),p,NULL);
          if (signe(q))
          {
            q = negi(q);
            A[j]=(long)lincomb_integral(gun,q,(GEN)A[j],(GEN)A[r]);
            U[j]=(long)lincomb_integral(gun,q,(GEN)U[j],(GEN)U[r]);
          }
        }
        if (low_stack(lim, stack_lim(av1,1)))
        {
          GEN *gptr[2]; gptr[0]=&A; gptr[1]=&U;
          if (DEBUGMEM>1) err(warnmem,"hnfall[2], li = %ld", li);
          gerepilemany(av1,gptr,2);
        }	
        break;
      }
      h[j]=li-1;
    }
  }
  if (DEBUGLEVEL>5) fprintferr("\nhnfall, final phase: ");
  r--; /* first r cols are in the image the n-r (independent) last ones */
  for (j=1; j<=r; j++)
    for (i=h[j]; i; i--)
      if (signe(b=gcoeff(A,i,j)))
      {
	k=c[i]; a=gcoeff(A,i,k);
	d=bezout(a,b,&u,&v);
	if (!is_pm1(d)) { a=divii(a,d); b=divii(b,d); }
        if (DEBUGLEVEL>5)
          { fprintferr("(u,v) = (%Z, %Z); ",u,v); flusherr(); }
        p1 = (GEN)A[k]; b = negi(b);
        A[k] = (long)lincomb_integral(u,v, p1,(GEN)A[j]);
        A[j] = (long)lincomb_integral(a,b, (GEN)A[j],p1);
        p1 = (GEN)U[k];
        U[k] = (long)lincomb_integral(u,v, p1,(GEN)U[j]);
        U[j] = (long)lincomb_integral(a,b, (GEN)U[j],p1);
	for (j1=k+1; j1<=n; j1++)
	{
	  q=truedvmdii(gcoeff(A,i,j1),d,NULL);
	  if (signe(q))
	  {
            q = negi(q);
            A[j1] = (long)lincomb_integral(gun,q,(GEN)A[j1],(GEN)A[k]);
            U[j1] = (long)lincomb_integral(gun,q,(GEN)U[j1],(GEN)U[k]);
	  }
	}
        if (low_stack(lim, stack_lim(av1,1)))
        {
          GEN *gptr[2]; tetpil = avma;
          A = matint_copy(A); gptr[0]=&A;
          U = matint_copy(U); gptr[1]=&U;
          if (DEBUGMEM>1) err(warnmem,"hnfall[3], j = %ld", j);
          gerepilemanysp(av1,tetpil,gptr,2);
        }	
      }
  if (DEBUGLEVEL>5) fprintferr("\n");
  tetpil=avma; y=cgetg(3,t_VEC);
  if (remove)
  { /* remove the first r columns */
    A += r; A[0] = evaltyp(t_MAT) | evallg(n-r+1);
  }
  y[1]=lcopy(A); y[2]=lcopy(U);
  return gerepile(av,tetpil,y);
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

/* Return the smith normal form d of matrix x. If all != 0 return [d,u,v],
 * where d = u.x.v
 */
static GEN
smithall(GEN x, long all)
{
  long av,tetpil,i,j,k,l,c,fl,n,s1,s2,lim;
  GEN p1,p2,p3,p4,z,b,u,v,d,ml,mr,mun,mdet,ys;

  if (typ(x)!=t_MAT) err(typeer,"smithall");
  if (DEBUGLEVEL>=9) outerr(x);
  n=lg(x)-1;
  if (!n) return trivsmith(all);
  if (lg(x[1]) != n+1) err(mattype1,"smithall");
  for (i=1; i<=n; i++)
    for (j=1; j<=n; j++)
      if (typ(coeff(x,i,j)) != t_INT)
        err(talker,"non integral matrix in smithall");

  av = avma; lim = stack_lim(av,1);
  x = dummycopy(x); mdet = detint(x);
  if (ishnfall(x)) { if (all) { ml=idmat(n); mr=idmat(n); } }
  else
  {
    if (signe(mdet))
    {
      p1=hnfmod(x,mdet);
      if (all) { ml=idmat(n); mr=gauss(x,p1); }
    }
    else
    {
      if (all)
      {
        p1 = hnfall0(x,0);
        ml = idmat(n); mr = (GEN)p1[2]; p1 = (GEN)p1[1];
      }
      else
        p1 = hnf0(x,0);
    }
    x = p1;
  }
  p1=cgetg(n+1,t_VEC); for (i=1; i<=n; i++) p1[i]=lnegi(gcoeff(x,i,i));
  p2=sindexsort(p1); ys=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1=cgetg(n+1,t_COL); ys[j]=(long)p1;
    for (i=1; i<=n; i++) p1[i]=coeff(x,p2[i],p2[j]);
  }
  x = ys;
  if (all)
  {
    p3=cgetg(n+1,t_MAT); p4=cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++) { p3[j]=ml[p2[j]]; p4[j]=mr[p2[j]]; }
    ml=p3; mr=p4;
  }
  if (signe(mdet))
  {
    p1 = hnfmod(x,mdet);
    if (all) mr=gmul(mr,gauss(x,p1));
  }
  else
  {
    if (all)
    {
      p1 = hnfall0(x,0);
      mr = gmul(mr,(GEN)p1[2]); p1 = (GEN)p1[1];
    }
    else
      p1 = hnf0(x,0);
  }
  x=p1; mun = negi(gun);

  if (DEBUGLEVEL>7) {fprintferr("starting SNF loop");flusherr();}
  for (i=n; i>=2; i--)
  {
    if (DEBUGLEVEL>7) {fprintferr("\ni = %ld: ",i);flusherr();}
    for(;;)
    {
      c = 0;
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(x,i,j); s1 = signe(p1);
	if (s1)
	{
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
	  if (all) update(u,v,p3,p4,(GEN*)(mr+i),(GEN*)(mr+j));
          if (low_stack(lim, stack_lim(av,1)))
	  {
	    if (DEBUGMEM>1) err(warnmem,"[1]: smithall");
	    if (all)
	    {
	      GEN *gptr[3]; gptr[0]=&x; gptr[1]=&ml; gptr[2]=&mr;
	      gerepilemany(av,gptr,3);
	    }
	    else x=gerepileupto(av,gcopy(x));
	  }
	}
      }
      if (DEBUGLEVEL>=8) {fprintferr("; ");flusherr();}
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(x,j,i); s1 = signe(p1);
	if (s1)
	{
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
	  if (all) update(u,v,p3,p4,(GEN*)(ml+i),(GEN*)(ml+j));
	  c = 1;
	}
      }
      if (!c)
      {
	b=gcoeff(x,i,i); fl=1;
	if (signe(b))
	{
	  for (k=1; k<i && fl; k++)
	    for (l=1; l<i && fl; l++)
	      fl = (int)!signe(resii(gcoeff(x,k,l),b));
          /* cast to (int) necessary for gcc-2.95 on sparcv9-64 (IS) */
	  if (!fl)
	  {
	    k--;
	    for (l=1; l<=i; l++)
	      coeff(x,i,l)=laddii(gcoeff(x,i,l),gcoeff(x,k,l));
	    if (all) ml[i]=ladd((GEN)ml[i],(GEN)ml[k]);
	  }
	}
        if (fl) break;
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) err(warnmem,"[2]: smithall");
	if (all)
	{
	  GEN *gptr[3]; gptr[0]=&x; gptr[1]=&ml; gptr[2]=&mr;
	  gerepilemany(av,gptr,3);
	}
	else x=gerepileupto(av,gcopy(x));
      }
    }
  }
  if (DEBUGLEVEL>7) {fprintferr("\n");flusherr();}
  if (all)
  {
    for (k=1; k<=n; k++)
      if (signe(gcoeff(x,k,k))<0)
        { mr[k]=lneg((GEN)mr[k]); coeff(x,k,k)=lnegi(gcoeff(x,k,k)); }
    tetpil=avma; z=cgetg(4,t_VEC);
    z[1]=ltrans(ml); z[2]=lcopy(mr); z[3]=lcopy(x);
    return gerepile(av,tetpil,z);
  }
  tetpil=avma; z=cgetg(n+1,t_VEC); j=n;
  for (k=n; k; k--)
    if (signe(gcoeff(x,k,k))) z[j--]=labsi(gcoeff(x,k,k));
  for (   ; j; j--) z[j]=zero;
  return gerepile(av,tetpil,z);
}

GEN
smith(GEN x) { return smithall(x,0); }

GEN
smith2(GEN x) { return smithall(x,1); }

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
  long av,tetpil,i,j,k,l,c,n, lim;
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
	tetpil=avma;
	if (all)
	{
	  GEN *gptr[3]; gptr[0]=&x; gptr[1]=&ml; gptr[2]=&mr;
	  gerepilemany(av,gptr,3);
	}
	else x=gerepile(av,tetpil,gcopy(x));
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
  long av = avma;
  if (flag > 7) err(flagerr,"matsnf");
  if (typ(x) == t_VEC && flag & 4) return smithclean(x);
  if (flag & 2) x = gsmithall(x,flag & 1);
  else          x = smithall(x, flag & 1);
  if (flag & 4) x = smithclean(x);
  return gerepileupto(av, x);
}

GEN
gsmith(GEN x) { return gsmithall(x,0); }

GEN
gsmith2(GEN x) { return gsmithall(x,1); }
