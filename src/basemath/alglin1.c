/********************************************************************/
/**                                                                **/
/**                         LINEAR ALGEBRA                         **/
/**                          (first part)                          **/
/**                                                                **/
/********************************************************************/
/* $Id$ */
#include "pari.h"

/*******************************************************************/
/*                                                                 */
/*                         TRANSPOSE                               */
/*                                                                 */
/*******************************************************************/

GEN
gtrans(GEN x)
{
  long i,j,lx,dx, tx=typ(x);
  GEN y,p1;

  if (! is_matvec_t(tx)) err(typeer,"gtrans");
  switch(tx)
  {
    case t_VEC:
      y=gcopy(x); settyp(y,t_COL); break;

    case t_COL:
      y=gcopy(x); settyp(y,t_VEC); break;

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      dx=lg(x[1]); y=cgetg(dx,tx);
      for (i=1; i<dx; i++)
      {
	p1=cgetg(lx,t_COL); y[i]=(long)p1;
	for (j=1; j<lx; j++) p1[j]=lcopy(gcoeff(x,i,j));
      }
      break;

    default: y=gcopy(x); break;
  }
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                    CONCATENATION & EXTRACTION                   */
/*                                                                 */
/*******************************************************************/

static GEN
strconcat(GEN x, GEN y)
{
  long flx=0,fly=0,l;
  char *sx,*sy,*str;

  if (typ(x)==t_STR) sx = GSTR(x); else { flx=1; sx = GENtostr(x); }
  if (typ(y)==t_STR) sy = GSTR(y); else { fly=1; sy = GENtostr(y); }
  l = strlen(sx) + strlen(sy) + 1;
  l = (l+BYTES_IN_LONG) >> TWOPOTBYTES_IN_LONG;
  x = cgetg(l+1, t_STR); str = GSTR(x);
  strcpy(str,sx);
  strcat(str,sy);
  if (flx) free(sx);
  if (fly) free(sy);
  return x;
}

GEN
concatsp(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y),lx=lg(x),ly=lg(y),i;
  GEN z,p1;

  if (tx==t_LIST || ty==t_LIST) return listconcat(x,y);
  if (tx==t_STR  || ty==t_STR)  return strconcat(x,y);

  if (tx==t_MAT && lx==1)
  {
    if (ty!=t_VEC || ly==1) return gtomat(y);
    err(concater);
  }
  if (ty==t_MAT && ly==1)
  {
    if (tx!=t_VEC || lx==1) return gtomat(x);
    err(concater);
  }

  if (! is_matvec_t(tx))
  {
    if (! is_matvec_t(ty))
    {
      z=cgetg(3,t_VEC); z[1]=(long)x; z[2]=(long)y;
      return z;
    }
    z=cgetg(ly+1,ty);
    if (ty != t_MAT) p1 = x;
    else
    {
      if (lg(y[1])!=2) err(concater);
      p1=cgetg(2,t_COL); p1[1]=(long)x;
    }
    for (i=2; i<=ly; i++) z[i]=y[i-1];
    z[1]=(long)p1; return z;
  }
  if (! is_matvec_t(ty))
  {
    z=cgetg(lx+1,tx);
    if (tx != t_MAT) p1 = y;
    else
    {
      if (lg(x[1])!=2) err(concater);
      p1=cgetg(2,t_COL); p1[1]=(long)y;
    }
    for (i=1; i<lx; i++) z[i]=x[i];
    z[lx]=(long)p1; return z;
  }

  if (tx == ty)
  {
    if (tx == t_MAT && lg(x[1]) != lg(y[1])) err(concater);
    z=cgetg(lx+ly-1,tx);
    for (i=1; i<lx; i++) z[i]=x[i];
    for (i=1; i<ly; i++) z[lx+i-1]=y[i];
    return z;
  }

  switch(tx)
  {
    case t_VEC:
      switch(ty)
      {
	case t_COL:
	  if (lx<=2) return (lx==1)? y: concatsp((GEN) x[1],y);
          if (ly>=3) break;
          return (ly==1)? x: concatsp(x,(GEN) y[1]);
	case t_MAT:
	  z=cgetg(ly,ty); if (lx != ly) break;
	  for (i=1; i<ly; i++) z[i]=(long)concatsp((GEN) x[i],(GEN) y[i]);
          return z;
      }
      break;

    case t_COL:
      switch(ty)
      {
	case t_VEC:
	  if (lx<=2) return (lx==1)? y: concatsp((GEN) x[1],y);
	  if (ly>=3) break;
	  return (ly==1)? x: concatsp(x,(GEN) y[1]);
	case t_MAT:
	  if (lx != lg(y[1])) break;
	  z=cgetg(ly+1,ty); z[1]=(long)x;
	  for (i=2; i<=ly; i++) z[i]=y[i-1];
          return z;
      }
      break;

    case t_MAT:
      switch(ty)
      {
	case t_VEC:
	  z=cgetg(lx,tx); if (ly != lx) break;
	  for (i=1; i<lx; i++) z[i]=(long)concatsp((GEN) x[i],(GEN) y[i]);
          return z;
	case t_COL:
	  if (ly != lg(x[1])) break;
	  z=cgetg(lx+1,tx); z[lx]=(long)y;
	  for (i=1; i<lx; i++) z[i]=x[i];
          return z;
      }
      break;
  }
  err(concater);
  return NULL; /* not reached */
}

GEN
concat(GEN x, GEN y)
{
  long tx = typ(x), lx,ty,ly,i;
  GEN z,p1;

  if (!y)
  {
    long av = avma, tetpil;
    if (tx == t_LIST)
      { lx = lgef(x); i = 2; }
    else if (tx == t_VEC)
      { lx = lg(x); i = 1; }
    else
    {
      err(concater);
      return NULL; /* not reached */
    }
    if (i>=lx) err(talker,"trying to concat elements of an empty vector");
    y = (GEN)x[i++];
    for (; i<lx; i++) y = concatsp(y, (GEN)x[i]);
    tetpil = avma; return gerepile(av,tetpil,gcopy(y));
  }
  ty = typ(y);
  if (tx==t_LIST || ty==t_LIST) return listconcat(x,y);
  if (tx==t_STR  || ty==t_STR)  return strconcat(x,y);
  lx=lg(x); ly=lg(y);

  if (tx==t_MAT && lx==1)
  {
    if (ty!=t_VEC || ly==1) return gtomat(y);
    err(concater);
  }
  if (ty==t_MAT && ly==1)
  {
    if (tx!=t_VEC || lx==1) return gtomat(x);
    err(concater);
  }

  if (! is_matvec_t(tx))
  {
    if (! is_matvec_t(ty))
    {
      z=cgetg(3,t_VEC); z[1]=lcopy(x); z[2]=lcopy(y);
      return z;
    }
    z=cgetg(ly+1,ty);
    if (ty != t_MAT) p1 = gcopy(x);
    else
    {
      if (lg(y[1])!=2) err(concater);
      p1=cgetg(2,t_COL); p1[1]=lcopy(x);
    }
    for (i=2; i<=ly; i++) z[i]=lcopy((GEN) y[i-1]);
    z[1]=(long)p1; return z;
  }
  if (! is_matvec_t(ty))
  {
    z=cgetg(lx+1,tx);
    if (tx != t_MAT) p1 = gcopy(y);
    else
    {
      if (lg(x[1])!=2) err(concater);
      p1=cgetg(2,t_COL); p1[1]=lcopy(y);
    }
    for (i=1; i<lx; i++) z[i]=lcopy((GEN) x[i]);
    z[lx]=(long)p1; return z;
  }

  if (tx == ty)
  {
    if (tx == t_MAT && lg(x[1]) != lg(y[1])) err(concater);
    z=cgetg(lx+ly-1,tx);
    for (i=1; i<lx; i++) z[i]=lcopy((GEN) x[i]);
    for (i=1; i<ly; i++) z[lx+i-1]=lcopy((GEN) y[i]);
    return z;
  }

  switch(tx)
  {
    case t_VEC:
      switch(ty)
      {
	case t_COL:
	  if (lx<=2) return (lx==1)? gcopy(y): concat((GEN) x[1],y);
          if (ly>=3) break;
          return (ly==1)? gcopy(x): concat(x,(GEN) y[1]);
	case t_MAT:
	  z=cgetg(ly,ty); if (lx != ly) break;
	  for (i=1; i<ly; i++) z[i]=lconcat((GEN) x[i],(GEN) y[i]);
          return z;
      }
      break;

    case t_COL:
      switch(ty)
      {
	case t_VEC:
	  if (lx<=2) return (lx==1)? gcopy(y): concat((GEN) x[1],y);
	  if (ly>=3) break;
	  return (ly==1)? gcopy(x): concat(x,(GEN) y[1]);
	case t_MAT:
	  if (lx != lg(y[1])) break;
	  z=cgetg(ly+1,ty); z[1]=lcopy(x);
	  for (i=2; i<=ly; i++) z[i]=lcopy((GEN) y[i-1]);
          return z;
      }
      break;

    case t_MAT:
      switch(ty)
      {
	case t_VEC:
	  z=cgetg(lx,tx); if (ly != lx) break;
	  for (i=1; i<lx; i++) z[i]=lconcat((GEN) x[i],(GEN) y[i]);
          return z;
	case t_COL:
	  if (ly != lg(x[1])) break;
	  z=cgetg(lx+1,tx); z[lx]=lcopy(y);
	  for (i=1; i<lx; i++) z[i]=lcopy((GEN) x[i]);
          return z;
      }
      break;
  }
  err(concater);
  return NULL; /* not reached */
}

static long
str_to_long(char *s, char **pt)
{
  long a = atol(s);
  while (isspace((int)*s)) s++;
  if (*s == '-' || *s == '+') s++;
  while (isdigit((int)*s) || isspace((int)*s)) s++;
  *pt = s; return a;
}

static int
get_range(char *s, long *a, long *b, long *cmpl, long lx)
{
  long max = lx - 1;

  *a = 1; *b = max;
  if (*s == '^') { *cmpl = 1; s++; } else *cmpl = 0;
  if (*s == 0) return 0;
  if (*s != '.')
  {
    *a = str_to_long(s, &s);
    if (*a < 0) *a += lx;
    if (*a<1 || *a>max) return 0;
  }
  if (*s == '.')
  {
    s++; if (*s != '.') return 0;
    do s++; while (isspace((int)*s));
    if (*s)
    {
      *b = str_to_long(s, &s);
      if (*b < 0) *b += lx;
      if (*b<1 || *b>max || *s) return 0;
    }
    return 1;
  }
  if (*s) return 0;
  *b = *a; return 1;
}

GEN
vecextract_i(GEN A, long y1, long y2)
{
  long i,lB = y2 - y1 + 2;
  GEN B = cgetg(lB, typ(A));
  for (i=1; i<lB; i++) B[i] = A[y1-1+i];
  return B;
}

GEN
rowextract_i(GEN A, long x1, long x2)
{
  long i, lB = lg(A);
  GEN B = cgetg(lB, typ(A));
  for (i=1; i<lB; i++) B[i] = (long)vecextract_i((GEN)A[i],x1,x2);
  return B;
}

GEN
vecextract_p(GEN A, GEN p)
{
  long i,lB = lg(p);
  GEN B = cgetg(lB, typ(A));
  for (i=1; i<lB; i++) B[i] = A[p[i]];
  return B;
}

GEN
rowextract_p(GEN A, GEN p)
{
  long i, lB = lg(A);
  GEN B = cgetg(lB, typ(A));
  for (i=1; i<lB; i++) B[i] = (long)vecextract_p((GEN)A[i],p);
  return B;
}

GEN
extract(GEN x, GEN l)
{
  long av,i,j, tl = typ(l), tx = typ(x), lx = lg(x);
  GEN y;

  if (! is_matvec_t(tx)) err(typeer,"extract");
  if (tl==t_INT)
  {
    /* extract components of x as per the bits of mask l */
    if (!signe(l)) return cgetg(1,tx);
    av=avma; y = (GEN) gpmalloc(lx*sizeof(long));
    i = j = 1; while (!mpodd(l)) { l=shifti(l,-1); i++; }
    while (signe(l) && i<lx)
    {
      if (mod2(l)) y[j++] = x[i];
      i++; l=shifti(l,-1);
    }
    if (signe(l)) err(talker,"mask too large in vecextract");
    y[0] = evaltyp(tx) | evallg(j);
    avma=av; x = gcopy(y); free(y); return x;
  }
  if (tl==t_STR)
  {
    char *s = GSTR(l);
    long first, last, cmpl;
    if (! get_range(s, &first, &last, &cmpl, lx))
      err(talker, "incorrect range in extract");
    if (lx == 1) return gcopy(x);
    if (cmpl)
    {
      if (first <= last)
      {
        y = cgetg(lx - (last - first + 1),tx);
        for (j=1; j<first; j++) y[j] = lcopy((GEN)x[j]);
        for (i=last+1; i<lx; i++,j++) y[j] = lcopy((GEN)x[i]);
      }
      else
      {
        y = cgetg(lx - (first - last + 1),tx);
        for (j=1,i=lx-1; i>first; i--,j++) y[j] = lcopy((GEN)x[i]);
        for (i=last-1; i>0; i--,j++) y[j] = lcopy((GEN)x[i]);
      }
    }
    else
    {
      if (first <= last)
      {
        y = cgetg(last-first+2,tx);
        for (i=first,j=1; i<=last; i++,j++) y[j] = lcopy((GEN)x[i]);
      }
      else
      {
        y = cgetg(first-last+2,tx);
        for (i=first,j=1; i>=last; i--,j++) y[j] = lcopy((GEN)x[i]);
      }
    }
    return y;
  }

  if (is_vec_t(tl))
  {
    long ll=lg(l); y=cgetg(ll,tx);
    for (i=1; i<ll; i++)
    {
      j = itos((GEN) l[i]);
      if (j>=lx || j<=0) err(talker,"no such component in vecextract");
      y[i] = lcopy((GEN) x[j]);
    }
    return y;
  }
  if (tl == t_VECSMALL)
  {
    long ll=lg(l); y=cgetg(ll,tx);
    for (i=1; i<ll; i++)
    {
      j = l[i];
      if (j>=lx || j<=0) err(talker,"no such component in vecextract");
      y[i] = lcopy((GEN) x[j]);
    }
    return y;
  }
  err(talker,"incorrect mask in vecextract");
  return NULL; /* not reached */
}

GEN
matextract(GEN x, GEN l1, GEN l2)
{
  long av = avma, tetpil;

  if (typ(x)!=t_MAT) err(typeer,"matextract");
  x = extract(gtrans(extract(x,l2)),l1); tetpil=avma;
  return gerepile(av,tetpil, gtrans(x));
}

GEN
extract0(GEN x, GEN l1, GEN l2)
{
  if (! l2) return extract(x,l1);
  return matextract(x,l1,l2);
}

/*******************************************************************/
/*                                                                 */
/*                     SCALAR-MATRIX OPERATIONS                    */
/*                                                                 */
/*******************************************************************/

/* create the square nxn matrix equal to z*Id */
static GEN
gscalmat_proto(GEN z, GEN myzero, long n, int flag)
{
  long i,j;
  GEN y = cgetg(n+1,t_MAT);
  if (n < 0) err(talker,"negative size in scalmat");
  if (flag) z = (flag==1)? stoi((long)z): gcopy(z);
  for (i=1; i<=n; i++)
  {
    y[i]=lgetg(n+1,t_COL);
    for (j=1; j<=n; j++)
      coeff(y,j,i) = (i==j)? (long)z: (long)myzero;
  }
  return y;
}

GEN
gscalmat(GEN x, long n) { return gscalmat_proto(x,gzero,n,2); }

GEN
gscalsmat(long x, long n) { return gscalmat_proto((GEN)x,gzero,n,1); }

GEN
idmat(long n) { return gscalmat_proto(gun,gzero,n,0); }

GEN
idmat_intern(long n,GEN myun,GEN z) { return gscalmat_proto(myun,z,n,0); }

GEN
gscalcol_proto(GEN z, GEN myzero, long n)
{
  GEN y = cgetg(n+1,t_COL);
  long i;

  if (n)
  {
    y[1]=(long)z;
    for (i=2; i<=n; i++) y[i]=(long)myzero;
  }
  return y;
}

GEN
zerocol(long n)
{
  GEN y = cgetg(n+1,t_COL);
  long i; for (i=1; i<=n; i++) y[i]=zero;
  return y;
}

GEN
zerovec(long n)
{
  GEN y = cgetg(n+1,t_VEC);
  long i; for (i=1; i<=n; i++) y[i]=zero;
  return y;
}


GEN
gscalcol(GEN x, long n) 
{ 
  GEN y=gscalcol_proto(gzero,gzero,n); 
  if (n) y[1]=lcopy(x); 
  return y;
}

GEN
gscalcol_i(GEN x, long n) { return gscalcol_proto(x,gzero,n); }

GEN
gtomat(GEN x)
{
  long tx,lx,i;
  GEN y,p1;

  if (!x) return cgetg(1, t_MAT);
  tx = typ(x);
  if (! is_matvec_t(tx))
  {
    y=cgetg(2,t_MAT); p1=cgetg(2,t_COL); y[1]=(long)p1;
    p1[1]=lcopy(x); return y;
  }
  switch(tx)
  {
    case t_VEC:
      lx=lg(x); y=cgetg(lx,t_MAT);
      for (i=1; i<lx; i++)
      {
	p1=cgetg(2,t_COL); y[i]=(long)p1;
	p1[1]=lcopy((GEN) x[i]);
      }
      break;
    case t_COL:
      y=cgetg(2,t_MAT); y[1]=lcopy(x); break;
    default: /* case t_MAT: */
      y=gcopy(x); break;
  }
  return y;
}

long
isdiagonal(GEN x)
{
  long nco,i,j;

  if (typ(x)!=t_MAT) err(typeer,"isdiagonal");
  nco=lg(x)-1; if (!nco) return 1;
  if (nco != lg(x[1])-1) return 0;

  for (j=1; j<=nco; j++)
  {
    GEN *col = (GEN*) x[j];
    for (i=1; i<=nco; i++)
      if (i!=j && !gcmp0(col[i])) return 0;
  }
  return 1;
}

/* create the diagonal matrix, whose diagonal is given by x */
GEN
diagonal(GEN x)
{
  long i,j,lx,tx=typ(x);
  GEN y,p1;

  if (! is_matvec_t(tx)) return gscalmat(x,1);
  if (tx==t_MAT)
  {
    if (isdiagonal(x)) return gcopy(x);
    err(talker,"incorrect object in diagonal");
  }
  lx=lg(x); y=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    p1=cgetg(lx,t_COL); y[j]=(long)p1;
    for (i=1; i<lx; i++)
      p1[i] = (i==j)? lcopy((GEN) x[i]): zero;
  }
  return y;
}

/* compute m*diagonal(d) */
GEN
matmuldiagonal(GEN m, GEN d)
{
  long j=typ(d),lx=lg(m);
  GEN y;

  if (typ(m)!=t_MAT) err(typeer,"matmuldiagonal");
  if (! is_vec_t(j) || lg(d)!=lx)
    err(talker,"incorrect vector in matmuldiagonal");
  y=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) y[j] = lmul((GEN) d[j],(GEN) m[j]);
  return y;
}

/* compute m*n assuming the result is a diagonal matrix */
GEN
matmultodiagonal(GEN m, GEN n)
{
  long lx,i,j;
  GEN s,y;

  if (typ(m)!=t_MAT || typ(n)!=t_MAT) err(typeer,"matmultodiagonal");
  lx=lg(n); y=idmat(lx-1);
  if (lx == 1)
    { if (lg(m) != 1) err(consister,"matmultodiagonal"); }
  else
    { if (lg(m) != lg(n[1])) err(consister,"matmultodiagonal"); }
  for (i=1; i<lx; i++)
  {
    s = gzero;
    for (j=1; j<lx; j++)
      s = gadd(s,gmul(gcoeff(m,i,j),gcoeff(n,j,i)));
    coeff(y,i,i) = (long)s;
  }
  return y;
}

/* [m[1,1], ..., m[l,l]] */
GEN
mattodiagonal(GEN m)
{
  long i, lx = lg(m);
  GEN y = cgetg(lx,t_VEC);

  if (typ(m)!=t_MAT) err(typeer,"mattodiagonal");
  if (lx == 1) return y;
  for (i=1; i<lx; i++) y[i] = lcopy(gcoeff(m,i,i));
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                    ADDITION SCALAR + MATRIX                     */
/*                                                                 */
/*******************************************************************/

/* create the square matrix x*Id + y */
GEN
gaddmat(GEN x, GEN y)
{
  long ly,dy,i,j;
  GEN z;

  ly=lg(y); if (ly==1) err(operf,"+",typ(x),t_MAT);
  dy=lg(y[1]);
  if (typ(y)!=t_MAT || ly!=dy) err(mattype1,"gaddmat");
  z=cgetg(ly,t_MAT);
  for (i=1; i<ly; i++)
  {
    z[i]=lgetg(dy,t_COL);
    for (j=1; j<dy; j++)
      coeff(z,j,i) = i==j? ladd(x,gcoeff(y,j,i)): lcopy(gcoeff(y,j,i));
  }
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                       Solve A*X=B (Gauss pivot)                 */
/*                                                                 */
/*******************************************************************/
#define swap(x,y) { long _t=x; x=y; y=_t; }

/* Assume x is a non-empty matrix. Return 0 if maximal pivot should not be
 * used, and the matrix precision (min real precision of coeffs) otherwise.
 */
static long
matprec(GEN x)
{
  long tx,i,j,l, k = VERYBIGINT, lx = lg(x), ly = lg(x[1]);
  GEN p1;
  for (i=1; i<lx; i++)
    for (j=1; j<ly; j++)
    {
      p1 = gmael(x,i,j); tx = typ(p1);
      if (!is_scalar_t(tx)) return 0;
      l = precision(p1); if (l && l<k) k = l;
    }
  return (k==VERYBIGINT)? 0: k;
}

/* As above, returning 1 if the precision would be non-zero, 0 otherwise */
static long
use_maximal_pivot(GEN x)
{
  long tx,i,j, lx = lg(x), ly = lg(x[1]);
  GEN p1;
  for (i=1; i<lx; i++)
    for (j=1; j<ly; j++)
    {
      p1 = gmael(x,i,j); tx = typ(p1);
      if (!is_scalar_t(tx)) return 0;
      if (precision(p1)) return 1;
    }
  return 0;
}

static GEN
check_b(GEN b, long nbli)
{
  GEN col;
  if (!b) return idmat(nbli);
  b = dummycopy(b);
  col = (typ(b) == t_MAT)? (GEN)b[1]: b;
  if (nbli == lg(col)-1) return b;
  err(talker,"incompatible matrix dimensions in gauss");
  return NULL; /* not reached */
}

/* C = A^(-1)B where A, B, C are integral and A is upper triangular */
GEN
gauss_triangle_i(GEN A, GEN B)
{
  long n = lg(A)-1, i,j,k;
  GEN p, m, c = cgetg(n+1,t_MAT);

  if (!n) return c;
  p = gcoeff(A,n,n);
  for (k=1; k<=n; k++)
  {
    GEN u = cgetg(n+1, t_COL), b = (GEN)B[k];
    c[k] = (long)u;
    u[n] = ldivii((GEN) b[n],p);
    for (i=n-1; i>0; i--)
    {
      long av = avma;
      m = negi((GEN)b[i]);
      for (j=i+1; j<=n; j++)
        m = addii(m, mulii(gcoeff(A,i,j),(GEN) u[j]));
      u[i] = (long)gerepileuptoint(av, divii(negi(m), gcoeff(A,i,i)));
    }
  }
  return c;
}

GEN
gauss_get_col(GEN a, GEN b, GEN p, long nbli)
{
  GEN m, u=cgetg(nbli+1,t_COL);
  long i,j;

  u[nbli] = ldiv((GEN) b[nbli],p);
  for (i=nbli-1; i>0; i--)
  {
    m = gneg_i((GEN)b[i]);
    for (j=i+1; j<=nbli; j++)
      m = gadd(m, gmul(gcoeff(a,i,j),(GEN) u[j]));
    u[i] = ldiv(gneg_i(m), gcoeff(a,i,i));
  }
  return u;
}

/* Gauss pivot.
 * Compute a^(-1)*b, where nblig(a) = nbcol(a) = nblig(b).
 * b is a matrix or column vector, NULL meaning: take the identity matrix
 * Be careful, if a or b is empty, the result is the empty matrix...
 */
GEN
gauss(GEN a, GEN b)
{
  long inexact,ismat,nbli,nbco,i,j,k,av,tetpil,lim;
  GEN p,m,u;
  /* nbli: nb lines of b = nb columns of a */
  /* nbco: nb columns of b (if matrix) */

  if (typ(a)!=t_MAT) err(mattype1,"gauss");
  if (b && typ(b)!=t_COL && typ(b)!=t_MAT) err(typeer,"gauss");
  if (lg(a) == 1)
  {
    if (b && lg(b)!=1) err(consister,"gauss");
    if (DEBUGLEVEL)
      err(warner,"in Gauss lg(a)=%ld lg(b)=%ld",lg(a),b?lg(b):-1);
    return cgetg(1,t_MAT);
  }
  av=avma; lim=stack_lim(av,1);
  nbli = lg(a)-1; if (nbli!=lg(a[1])-1) err(mattype1,"gauss");
  a = dummycopy(a);
  b = check_b(b,nbli);
  nbco = lg(b)-1;
  inexact = use_maximal_pivot(a);
  ismat   = (typ(b)==t_MAT);
  if(DEBUGLEVEL>4)
    fprintferr("Entering gauss with inexact=%ld ismat=%ld\n",inexact,ismat);

  for (i=1; i<nbli; i++)
  {
    /* k is the line where we find the pivot */
    p=gcoeff(a,i,i); k=i;
    if (inexact) /* maximal pivot */
    {
      long e, ex = gexpo(p);
      for (j=i+1; j<=nbli; j++)
      {
        e = gexpo(gcoeff(a,j,i));
        if (e > ex) { ex=e; k=j; }
      }
      if (gcmp0(gcoeff(a,k,i))) err(matinv1);
    }
    else if (gcmp0(p)) /* first non-zero pivot */
    {
      do k++; while (k<=nbli && gcmp0(gcoeff(a,k,i)));
      if (k>nbli) err(matinv1);
    }

    /* if (k!=i), exchange the lines s.t. k = i */
    if (k != i)
    {
      for (j=i; j<=nbli; j++) swap(coeff(a,i,j), coeff(a,k,j));
      if (ismat)
      {
        for (j=1; j<=nbco; j++) swap(coeff(b,i,j), coeff(b,k,j));
      }
      else
        swap(b[i],b[k]);
      p = gcoeff(a,i,i);
    }

    for (k=i+1; k<=nbli; k++)
    {
      m=gcoeff(a,k,i);
      if (!gcmp0(m))
      {
	m = gneg_i(gdiv(m,p));
	for (j=i+1; j<=nbli; j++)
	{
	  u = gmul(m,gcoeff(a,i,j));
	  coeff(a,k,j) = ladd(gcoeff(a,k,j),u);
	}
	if (ismat) for (j=1; j<=nbco; j++)
	{
	  u = gmul(m,gcoeff(b,i,j));
	  coeff(b,k,j) = ladd(gcoeff(b,k,j),u);
	}
	else
	{
	  u = gmul(m,(GEN) b[i]);
	  b[k] = ladd((GEN) b[k],u);
	}
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[2];
      if(DEBUGMEM>1) err(warnmem,"gauss. i=%ld",i);
      gptr[0]=&a; gptr[1]=&b;
      gerepilemany(av,gptr,2);
    }
  }

  if(DEBUGLEVEL>4) fprintferr("Solving the triangular system\n");
  p=gcoeff(a,nbli,nbli);
  if (!inexact && gcmp0(p)) err(matinv1);
  if (!ismat) u = gauss_get_col(a,b,p,nbli);
  else
  {
    long av1 = avma;
    lim = stack_lim(av1,1); u=cgetg(nbco+1,t_MAT);
    for (j=2; j<=nbco; j++) u[j] = zero; /* dummy */
    for (j=1; j<=nbco; j++)
    {
      u[j] = (long)gauss_get_col(a,(GEN)b[j],p,nbli);
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"gauss[2]. j=%ld", j);
        tetpil=avma; u = gerepile(av1,tetpil,gcopy(u));
      }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(u));
}

/* x a matrix with integer coefficients. Return a multiple of the determinant
 * of the lattice generated by the columns of x (to be used with hnfmod)
 */
GEN
detint(GEN x)
{
  GEN pass,c,v,det1,piv,pivprec,vi,p1;
  long i,j,k,rg,n,m,m1,av=avma,av1,lim;

  if (typ(x)!=t_MAT) err(typeer,"detint");
  n=lg(x)-1; if (!n) return gun;
  m1=lg(x[1]); m=m1-1; lim=stack_lim(av,1);
  c=new_chunk(m1); for (k=1; k<=m; k++) c[k]=0;
  av1=avma; pass=cgetg(m1,t_MAT);
  for (j=1; j<=m; j++)
  {
    p1=cgetg(m1,t_COL); pass[j]=(long)p1;
    for (i=1; i<=m; i++) p1[i]=zero;
  }
  for (k=1; k<=n; k++)
    for (j=1; j<=m; j++)
      if (typ(gcoeff(x,j,k)) != t_INT)
        err(talker,"not an integer matrix in detint");
  v=cgetg(m1,t_COL);
  det1=gzero; piv=pivprec=gun;
  for (rg=0,k=1; k<=n; k++)
  {
    long t = 0;
    for (i=1; i<=m; i++)
      if (!c[i])
      {
	vi=mulii(piv,gcoeff(x,i,k));
	for (j=1; j<=m; j++)
	  if (c[j]) vi=addii(vi,mulii(gcoeff(pass,i,j),gcoeff(x,j,k)));
	v[i]=(long)vi; if (!t && signe(vi)) t=i;
      }
    if (t)
    {
      if (rg == m-1)
        { det1=mppgcd((GEN)v[t],det1); c[t]=0; }
      else
      {
        rg++; pivprec = piv; piv=(GEN)v[t]; c[t]=k;
	for (i=1; i<=m; i++)
	  if (!c[i])
	  {
            GEN p2 = negi((GEN)v[i]);
	    for (j=1; j<=m; j++)
	      if (c[j] && j!=t)
	      {
	        p1 = addii(mulii(gcoeff(pass,i,j), piv),
	 	 	   mulii(gcoeff(pass,t,j), p2));
                if (rg>1) p1 = divii(p1,pivprec);
	        coeff(pass,i,j) = (long)p1;
	      }
	    coeff(pass,i,t) = (long)p2;
	  }
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[5];
      if(DEBUGMEM>1) err(warnmem,"detint. k=%ld",k);
      gptr[0]=&det1; gptr[1]=&piv; gptr[2]=&pivprec;
      gptr[3]=&pass; gptr[4]=&v; gerepilemany(av1,gptr,5);
    }
  }
  return gerepileupto(av, absi(det1));
}

static void
gerepile_gauss_keep(GEN x, long m, long n, long k, long t, long av)
{
  long tetpil = avma,dec,u,A,i;

  if (DEBUGMEM > 1) err(warnmem,"gauss_pivot_keep. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++) copyifstack(coeff(x,u,k), coeff(x,u,k));
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++) copyifstack(coeff(x,u,i), coeff(x,u,i));

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  for (u=t+1; u<=m; u++)
  {
    A=coeff(x,u,k);
    if (A<av && A>=bot) coeff(x,u,k)+=dec;
  }
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
    {
      A=coeff(x,u,i);
      if (A<av && A>=bot) coeff(x,u,i)+=dec;
    }
}

static void
gerepile_gauss_keep_mod_p(GEN x, GEN p, long m, long n, long k, long t, long av)
{
  long tetpil = avma,dec,u,A,i;

  if (DEBUGMEM > 1) err(warnmem,"gauss_pivot_keep. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (isonstack(coeff(x,u,k))) coeff(x,u,k) = lmodii(gcoeff(x,u,k),p);
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
      if (isonstack(coeff(x,u,i))) coeff(x,u,i) = lmodii(gcoeff(x,u,i),p);

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  for (u=t+1; u<=m; u++)
  {
    A=coeff(x,u,k);
    if (A<av && A>=bot) coeff(x,u,k)+=dec;
  }
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
    {
      A=coeff(x,u,i);
      if (A<av && A>=bot) coeff(x,u,i)+=dec;
    }
}

/* special gerepile for huge matrices */

static void
gerepile_gauss(GEN x,long m,long n,long k,long t,long av, long j, GEN c)
{
  long tetpil = avma,dec,u,A,i;

  if (DEBUGMEM > 1) err(warnmem,"gauss_pivot. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u]) copyifstack(coeff(x,u,k), coeff(x,u,k));
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++) copyifstack(coeff(x,u,i), coeff(x,u,i));

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u])
    {
      A=coeff(x,u,k);
      if (A<av && A>=bot) coeff(x,u,k)+=dec;
    }
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++)
      {
        A=coeff(x,u,i);
        if (A<av && A>=bot) coeff(x,u,i)+=dec;
      }
}

/*******************************************************************/
/*                                                                 */
/*                    KERNEL of an m x n matrix                    */
/*          return n - rk(x) linearly independant vectors          */
/*                                                                 */
/*******************************************************************/

/* x has INTEGER coefficients */
GEN
keri(GEN x)
{
  GEN c,d,y,p,pp;
  long i,j,k,r,t,n,m,av,av0,tetpil,lim;

  if (typ(x)!=t_MAT) err(typeer,"keri");
  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);

  av0=avma; m=lg(x[1])-1; r=0;
  pp=cgetg(n+1,t_COL);
  x=dummycopy(x); p=gun;
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=new_chunk(n+1); av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    j=1;
    while (j<=m && (c[j] || !signe(gcoeff(x,j,k))) ) j++;
    if (j>m)
    {
      r++; d[k]=0;
      for(j=1; j<k; j++)
	if (d[j]) coeff(x,d[j],k) = lclone(gcoeff(x,d[j],k));
      pp[k]=lclone(p);
    }
    else
    {
      GEN p0 = p;
      long av1;

      c[j]=k; d[k]=j; p = gcoeff(x,j,k);

      for (t=1; t<=m; t++)
	if (t!=j)
	{
	  GEN q=gcoeff(x,t,k), p1,p2;
	  for (i=k+1; i<=n; i++)
	  {
	    av1=avma; (void)new_chunk(lgefint(p0));
	    p1=mulii(q,gcoeff(x,j,i));
	    p2=mulii(p,gcoeff(x,t,i));
	    p1=subii(p2,p1); avma=av1;
	    coeff(x,t,i) = ldivii(p1,p0);
	  }
	  if (low_stack(lim, stack_lim(av,1)))
          {
            p1 = gclone(p);
            gerepile_gauss_keep(x,m,n,k,t,av);
            p = gcopy(p1); gunclone(p1);
          }
	}
    }
  }
  if (!r) { avma=av0; y=cgetg(1,t_MAT); return y; }

  /* non trivial kernel */
  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    p = cgetg(n+1, t_COL);
    y[j]=(long)p; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
	c=gcoeff(x,d[i],k);
	p[i] = (long) forcecopy(c); gunclone(c);
      }
      else
	p[i] = zero;
    p[k]=lnegi((GEN)pp[k]); gunclone((GEN)pp[k]);
    for (i=k+1; i<=n; i++) p[i]=zero;
  }
  return gerepile(av0,tetpil,y);
}

GEN
deplin(GEN x)
{
  long i,j,k,t,nc,nl, av=avma;
  GEN y,q,c,l,d;

  if (typ(x) != t_MAT) err(typeer,"deplin");
  nc=lg(x)-1; if (!nc) err(talker,"empty matrix in deplin");
  nl=lg(x[1])-1;
  c=new_chunk(nl+1);
  l=new_chunk(nc+1);
  d=cgetg(nl+1,t_VEC);
  for (i=1; i<=nl; i++) { d[i]=un; c[i]=0; }
  k=1; t=1;
  while (t<=nl && k<=nc)
  {
    for (j=1; j<k; j++)
     for (i=1; i<=nl; i++)
      if (i!=l[j])
       coeff(x,i,k)=lsub(gmul((GEN) d[j],gcoeff(x,i,k)),
                         gmul(gcoeff(x,i,j),gcoeff(x,l[j],k)));
    t=1;
    while ( t<=nl && (c[t] || gcmp0(gcoeff(x,t,k))) ) t++;
    if (t<=nl)
    {
      d[k]=coeff(x,t,k);
      c[t]=k; l[k++]=t;
    }
  }
  if (k>nc)
  {
    avma=av; y=cgetg(nc+1,t_COL);
    for (j=1; j<=nc; j++) y[j]=zero;
    return y;
  }
  y=cgetg(nc+1,t_COL);
  y[1]=(k>1)? coeff(x,l[1],k): un;
  for (q=gun,j=2; j<k; j++)
  {
    q=gmul(q,(GEN) d[j-1]);
    y[j]=lmul(gcoeff(x,l[j],k),q);
  }
  if (k>1) y[k]=lneg(gmul(q,(GEN) d[k-1]));
  for (j=k+1; j<=nc; j++) y[j]=zero;
  d=content(y); t=avma;
  return gerepile(av,t,gdiv(y,d));
}

/*******************************************************************/
/*                                                                 */
/*         GAUSS REDUCTION OF MATRICES  (m lines x n cols)         */
/*           (kernel, image, complementary image, rank)            */
/*                                                                 */
/*******************************************************************/
static long gauss_ex;
static int (*gauss_is_zero)(GEN);

static int
real0(GEN x)
{
  return gcmp0(x) || (gexpo(x) < gauss_ex);
}

static void
gauss_get_prec(GEN x, long prec)
{
  long pr = matprec(x);

  if (!pr) { gauss_is_zero = &gcmp0; return; }
  if (pr > prec) prec = pr;

  gauss_ex = - (long)(0.85 * bit_accuracy(prec));
  gauss_is_zero = &real0;
}

/* return the transform of x under a standard Gauss pivot. r = dim ker(x).
 * d[k] contains the index of the first non-zero pivot in column k
 */
static GEN
gauss_pivot_keep(GEN x, long prec, GEN *dd, long *rr)
{
  GEN c,d,p,mun;
  long i,j,k,r,t,n,m,av,lim;

  if (typ(x)!=t_MAT) err(typeer,"gauss_pivot");
  n=lg(x)-1; if (!n) { *dd=NULL; *rr=0; return cgetg(1,t_MAT); }

  gauss_get_prec(x,prec); m=lg(x[1])-1; r=0;
  x=dummycopy(x); mun=negi(gun);
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=(GEN)gpmalloc((n+1)*sizeof(long));
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    j=1; while (j<=m && (c[j] || gauss_is_zero(gcoeff(x,j,k)))) j++;
    if (j>m)
    {
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) coeff(x,d[j],k) = lclone(gcoeff(x,d[j],k));
    }
    else
    {
      c[j]=k; d[k]=j; p = gdiv(mun,gcoeff(x,j,k));
      coeff(x,j,k) = (long)mun;
      for (i=k+1; i<=n; i++)
	coeff(x,j,i) = lmul(p,gcoeff(x,j,i));
      for (t=1; t<=m; t++)
	if (t!=j)
	{
	  p=gcoeff(x,t,k); coeff(x,t,k)=zero;
	  for (i=k+1; i<=n; i++)
	    coeff(x,t,i) = ladd(gcoeff(x,t,i),gmul(p,gcoeff(x,j,i)));
          if (low_stack(lim, stack_lim(av,1)))
            gerepile_gauss_keep(x,m,n,k,t,av);
	}
    }
  }
  *dd=d; *rr=r; return x;
}

/* r = dim ker(x).
 * d[k] contains the index of the first non-zero pivot in column k
 */
static void
gauss_pivot(GEN x, long prec, GEN *dd, long *rr)
{
  GEN c,d,mun,p;
  long i,j,k,r,t,n,m,av,lim;

  if (typ(x)!=t_MAT) err(typeer,"gauss_pivot");
  n=lg(x)-1; if (!n) { *dd=NULL; *rr=0; return; }

  gauss_get_prec(x,prec); m=lg(x[1])-1; r=0;
  x=dummycopy(x); mun=negi(gun);
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=(GEN)gpmalloc((n+1)*sizeof(long)); av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    j=1; while (j<=m && (c[j] || gauss_is_zero(gcoeff(x,j,k)))) j++;
    if (j>m) { r++; d[k]=0; }
    else
    {
      c[j]=k; d[k]=j; p = gdiv(mun,gcoeff(x,j,k));
      for (i=k+1; i<=n; i++)
	coeff(x,j,i) = lmul(p,gcoeff(x,j,i));

      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          p=gcoeff(x,t,k); coeff(x,t,k)=zero;
          for (i=k+1; i<=n; i++)
            coeff(x,t,i) = ladd(gcoeff(x,t,i), gmul(p,gcoeff(x,j,i)));
          if (low_stack(lim, stack_lim(av,1)))
            gerepile_gauss(x,m,n,k,t,av,j,c);
        }
      for (i=k; i<=n; i++) coeff(x,j,i) = zero; /* dummy */
    }
  }
  *dd=d; *rr=r;
}

static GEN
ker0(GEN x, long prec)
{
  GEN d,y;
  long i,j,k,r,n, av = avma, tetpil;

  x=gauss_pivot_keep(x,prec,&d,&r);
  if (!r)
  {
    avma=av; if (d) free(d);
    return cgetg(1,t_MAT);
  }
  n = lg(x)-1; tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN p = cgetg(n+1,t_COL);

    y[j]=(long)p; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
	GEN p1=gcoeff(x,d[i],k);
	p[i] = (long)forcecopy(p1); gunclone(p1);
      }
      else
	p[i] = zero;
    p[k]=un; for (i=k+1; i<=n; i++) p[i]=zero;
  }
  free(d); return gerepile(av,tetpil,y);
}

GEN
ker(GEN x) /* Programme pour types exacts */
{
  return ker0(x,0);
}

GEN
matker0(GEN x,long flag)
{
  return flag? keri(x): ker(x);
}

static GEN
image0(GEN x, long prec)
{
  GEN d,y;
  long j,k,r, av = avma;

  gauss_pivot(x,prec,&d,&r);

  /* r = dim ker(x) */
  if (!r) { avma=av; if (d) free(d); return gcopy(x); }

  /* r = dim Im(x) */
  r = lg(x)-1 - r; avma=av;
  y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) y[j++] = lcopy((GEN)x[k]);
  free(d); return y;
}

GEN
image(GEN x) /* Programme pour types exacts */
{
  return image0(x,0);
}

GEN
imagereel(GEN x, long prec) /* Programme pour types inexacts */
{
  return image0(x,prec);
}

static GEN
imagecompl0(GEN x, long prec)
{
  GEN d,y;
  long j,i,r,av = avma;

  gauss_pivot(x,prec,&d,&r);
  avma=av; y=cgetg(r+1,t_VEC);
  for (i=j=1; j<=r; i++)
    if (!d[i]) y[j++]=lstoi(i);
  if (d) free(d); return y;
}

/* for hnfspec: imagecompl(trans(x)) + image(trans(x)) */
static GEN
imagecomplspec(GEN x, long *nlze)
{
  GEN d,y;
  long i,j,k,l,r,av = avma;

  x = gtrans(x); l = lg(x);
  gauss_pivot(x,0,&d,&r);
  avma=av; y = cgetg(l,t_VECSMALL);
  for (i=j=1, k=r+1; i<l; i++)
    if (d[i]) y[k++]=i; else y[j++]=i;
  *nlze = r;
  if (d) free(d); return y;
}

GEN
imagecompl(GEN x) /* Programme pour types exacts */
{
  return imagecompl0(x,0);
}

static GEN
sinverseimage(GEN mat, GEN y)
{
  long av=avma,tetpil,i, nbcol = lg(mat);
  GEN col,p1 = cgetg(nbcol+1,t_MAT);

  if (nbcol==1) return NULL;
  if (lg(y) != lg(mat[1])) err(consister,"inverseimage");

  p1[nbcol] = (long)y;
  for (i=1; i<nbcol; i++) p1[i]=mat[i];
  p1 = ker(p1); i=lg(p1)-1;
  if (!i) return NULL;

  col = (GEN)p1[i]; p1 = (GEN) col[nbcol];
  if (gcmp0(p1)) return NULL;

  p1 = gneg_i(p1); setlg(col,nbcol); tetpil=avma;
  return gerepile(av,tetpil, gdiv(col, p1));
}

/* Calcule l'image reciproque de v par m */
GEN
inverseimage(GEN m,GEN v)
{
  long av=avma,j,lv,tv=typ(v);
  GEN y,p1;

  if (typ(m)!=t_MAT) err(typeer,"inverseimage");
  if (tv==t_COL)
  {
    p1 = sinverseimage(m,v);
    if (p1) return p1;
    avma = av; return cgetg(1,t_MAT);
  }
  if (tv!=t_MAT) err(typeer,"inverseimage");

  lv=lg(v)-1; y=cgetg(lv+1,t_MAT);
  for (j=1; j<=lv; j++)
  {
    p1 = sinverseimage(m,(GEN)v[j]);
    if (!p1) { avma = av; return cgetg(1,t_MAT); }
    y[j] = (long)p1;
  }
  return y;
}

/* x is an n x k matrix, rank(x) = k <= n. Return an invertible n x n matrix
 * whose first k columns are given by x. If rank(x)<k, the result may be wrong
 */
GEN
suppl_intern(GEN x, GEN myid)
{
  long av = avma, lx = lg(x), n,i,j;
  GEN y,p1;
  stackzone *zone;

  if (typ(x) != t_MAT) err(typeer,"suppl");
  if (lx==1) err(talker,"empty matrix in suppl");
  n=lg(x[1]); if (lx>n) err(suppler2);
  if (lx == n) return gcopy(x);

  zone  = switch_stack(NULL, n*n);
  switch_stack(zone,1);
  y = myid? dummycopy(myid): idmat(n-1);
  switch_stack(zone,0);
  gauss_get_prec(x,0);
  for (i=1; i<lx; i++)
  {
    p1 = gauss(y,(GEN)x[i]); j=i;
    while (j<n && gauss_is_zero((GEN)p1[j])) j++;
    if (j>=n) err(suppler2);
    p1=(GEN)y[i]; y[i]=x[i]; if (i!=j) y[j]=(long)p1;
  }
  avma = av; y = gcopy(y);
  free(zone); return y;
}

GEN
suppl(GEN x)
{
  return suppl_intern(x,NULL);
}

GEN
image2(GEN x)
{
  long av=avma,tetpil,k,n,i;
  GEN p1,p2;

  if (typ(x)!=t_MAT) err(typeer,"image2");
  k=lg(x)-1; if (!k) return gcopy(x);
  n=lg(x[1])-1; p1=ker(x); k=lg(p1)-1;
  if (k) { p1=suppl(p1); n=lg(p1)-1; }
  else p1=idmat(n);

  tetpil=avma; p2=cgetg(n-k+1,t_MAT);
  for (i=k+1; i<=n; i++) p2[i-k]=lmul(x,(GEN) p1[i]);
  return gerepile(av,tetpil,p2);
}

GEN
matimage0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return image(x);
    case 1: return image2(x);
    default: err(flagerr,"matimage");
  }
  return NULL; /* not reached */
}

long
rank(GEN x)
{
  long av = avma, r;
  GEN d;

  gauss_pivot(x,0,&d,&r);
  /* yield r = dim ker(x) */

  avma=av; if (d) free(d);
  return lg(x)-1 - r;
}

GEN
indexrank(GEN x)
{
  long av = avma, i,j,n,r;
  GEN res,d,p1,p2;

  /* yield r = dim ker(x) */
  gauss_pivot(x,0,&d,&r);

  /* now r = dim Im(x) */
  n = lg(x)-1; r = n - r;

  avma=av; res=cgetg(3,t_VEC);
  p1=cgetg(r+1,t_VEC); res[1]=(long)p1;
  p2=cgetg(r+1,t_VEC); res[2]=(long)p2;
  if (d)
  {
    for (i=0,j=1; j<=n; j++)
      if (d[j]) { i++; p1[i]=d[j]; p2[i]=j; }
    free(d);
    qsort(p1+1,r,sizeof(long),(QSCOMP)pari_compare_long);
  }
  for (i=1;i<=r;i++) { p1[i]=lstoi(p1[i]); p2[i]=lstoi(p2[i]); }
  return res;
}

/*******************************************************************/
/*                                                                 */
/*                    LINEAR ALGEBRA MODULO P                      */
/*                                                                 */
/*******************************************************************/
#ifdef LONG_IS_64BIT
#  define MASK (0x7fffffff00000000UL)
#else
#  define MASK (0x7fff0000UL)
#endif
GEN
FpM_mul(GEN x, GEN y, GEN p)
{
  long i,j,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(ly,t_MAT);
  if (lx != lg(y[1])) err(operi,"* [mod p]",t_MAT,t_MAT);
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
      ulong av;
      GEN p1,p2;
      int k;
      p1=gzero; av=avma;
      for (k=1; k<lx; k++)
      {
	p2=mulii(gcoeff(x,i,k),gcoeff(y,k,j));
	p1=addii(p1,p2);
      }
      coeff(z,i,j)=lpileupto(av,p?modii(p1,p):p1);
    }
  }
  return z;
}

static GEN
ker_mod_p_small(GEN x, GEN pp, long nontriv)
{
  GEN y,c,d;
  long a,i,j,k,r,t,n,m,av0,tetpil, p = pp[2], piv;

  n = lg(x)-1;
  m=lg(x[1])-1; r=0; av0 = avma;
  x = dummycopy(x);
  for (i=1; i<=n; i++)
  {
    GEN p1 = (GEN)x[i];
    for (j=1; j<=m; j++) p1[j] = itos((GEN)p1[j]);
  }
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=new_chunk(n+1);
  a=0; /* for gcc -Wall */
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        a = coeff(x,j,k) % p;
        if (a) break;
      }
    if (j>m)
    {
      if (nontriv) { avma=av0; return NULL; }
      r++; d[k]=0;
    }
    else
    {
      c[j]=k; d[k]=j;
      {
        long av1 = avma;
        GEN p1 = mpinvmod(stoi(a), pp);
        piv = -itos(p1); avma = av1;
      }
      coeff(x,j,k) = -1;
      for (i=k+1; i<=n; i++)
	coeff(x,j,i) = (piv * coeff(x,j,i)) % p;
      for (t=1; t<=m; t++)
	if (t!=j)
	{
	  piv = coeff(x,t,k) % p;
          if (piv)
          {
            coeff(x,t,k) = 0;
            for (i=k+1; i<=n; i++)
            {
              a = coeff(x,t,i) + piv * coeff(x,j,i);
              if (a & MASK) a %= p;
              coeff(x,t,i) = a;
            }
          }
	}
    }
  }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN c = cgetg(n+1,t_COL);

    y[j]=(long)c; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        long a = coeff(x,d[i],k) % p;
        if (a < 0) a += p;
	c[i] = lstoi(a);
      }
      else
	c[i] = zero;
    c[k]=un; for (i=k+1; i<=n; i++) c[i]=zero;
  }
  return gerepile(av0,tetpil,y);
}

static GEN
ker_mod_p_i(GEN x, GEN p, long nontriv)
{
  GEN y,c,d,piv,mun;
  long i,j,k,r,t,n,m,av0,av,lim,tetpil;

  if (typ(x)!=t_MAT) err(typeer,"ker_mod_p");
  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  if (!is_bigint(p) && p[2] < (MAXHALFULONG>>1))
    return ker_mod_p_small(x, p, nontriv);

  m=lg(x[1])-1; r=0; av0 = avma;
  x=dummycopy(x); mun=negi(gun);
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=new_chunk(n+1);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        coeff(x,j,k) = lmodii(gcoeff(x,j,k), p);
        if (signe(coeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (nontriv) { avma = av0; return NULL; }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) coeff(x,d[j],k) = lclone(gcoeff(x,d[j],k));
    }
    else
    {
      c[j]=k; d[k]=j; piv = negi(mpinvmod(gcoeff(x,j,k), p));
      coeff(x,j,k) = (long)mun;
      for (i=k+1; i<=n; i++)
	coeff(x,j,i) = lmodii(mulii(piv,gcoeff(x,j,i)), p);
      for (t=1; t<=m; t++)
	if (t!=j)
	{
	  piv = modii(gcoeff(x,t,k), p);
          if (signe(piv))
          {
            coeff(x,t,k)=zero;
            for (i=k+1; i<=n; i++)
              coeff(x,t,i) = laddii(gcoeff(x,t,i),mulii(piv,gcoeff(x,j,i)));
            if (low_stack(lim, stack_lim(av,1)))
              gerepile_gauss_keep_mod_p(x,p,m,n,k,t,av);
          }
	}
    }
  }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN c = cgetg(n+1,t_COL);

    y[j]=(long)c; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
	GEN p1=gcoeff(x,d[i],k);
	c[i] = lmodii(p1, p); gunclone(p1);
      }
      else
	c[i] = zero;
    c[k]=un; for (i=k+1; i<=n; i++) c[i]=zero;
  }
  return gerepile(av0,tetpil,y);
}

static void
gauss_pivot_mod_p(GEN x, GEN p, GEN *dd, long *rr)
{
  GEN c,d,piv;
  long i,j,k,r,t,n,m,av,lim;

  if (typ(x)!=t_MAT) err(typeer,"gauss_pivot_mod_p");
  n=lg(x)-1; if (!n) { *dd=NULL; *rr=0; return; }

  m=lg(x[1])-1; r=0;
  x=dummycopy(x);
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=(GEN)gpmalloc((n+1)*sizeof(long)); av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        coeff(x,j,k) = lmodii(gcoeff(x,j,k), p);
        if (signe(coeff(x,j,k))) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      c[j]=k; d[k]=j; piv = negi(mpinvmod(gcoeff(x,j,k), p));
      for (i=k+1; i<=n; i++)
	coeff(x,j,i) = lmodii(mulii(piv,gcoeff(x,j,i)), p);
      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          piv=gcoeff(x,t,k);
          if (signe(piv))
          {
            coeff(x,t,k)=zero;
            for (i=k+1; i<=n; i++)
              coeff(x,t,i) = laddii(gcoeff(x,t,i), mulii(piv,gcoeff(x,j,i)));
            if (low_stack(lim, stack_lim(av,1)))
              gerepile_gauss(x,m,n,k,t,av,j,c);
          }
        }
      for (i=k; i<=n; i++) coeff(x,j,i) = zero; /* dummy */
    }
  }
  *dd=d; *rr=r;
}

GEN
ker_mod_p(GEN x, GEN p)
{
  return ker_mod_p_i(x, p, 0);
}

int
ker_trivial_mod_p(GEN x, GEN p)
{
  return ker_mod_p_i(x, p, 1)==NULL;
}

GEN
image_mod_p(GEN x, GEN p)
{
  GEN d,y;
  long j,k,r, av = avma;

  gauss_pivot_mod_p(x,p,&d,&r);

  /* r = dim ker(x) */
  if (!r) { avma=av; if (d) free(d); return gcopy(x); }

  /* r = dim Im(x) */
  r = lg(x)-1 - r; avma=av;
  y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) y[j++] = lcopy((GEN)x[k]);
  free(d); return y;
}
static GEN
sinverseimage_mod_p(GEN mat, GEN y, GEN p)
{
  long av=avma,i, nbcol = lg(mat);
  GEN col,p1 = cgetg(nbcol+1,t_MAT),res;

  if (nbcol==1) return NULL;
  if (lg(y) != lg(mat[1])) err(consister,"inverseimage_mod_p");

  p1[nbcol] = (long)y;
  for (i=1; i<nbcol; i++) p1[i]=mat[i];
  p1 = ker_mod_p(p1,p); i=lg(p1)-1;
  if (!i) return NULL;

  col = (GEN)p1[i]; p1 = (GEN) col[nbcol];
  if (gcmp0(p1)) return NULL;

  p1 = mpinvmod(negi(p1),p);
  setlg(col,nbcol);
  for(i=1;i<nbcol;i++)
    col[i]=lmulii((GEN)col[i],p1);
  res=cgetg(nbcol,t_COL);
  for(i=1;i<nbcol;i++)
    res[i]=lmodii((GEN)col[i],p);
  return gerepileupto(av,res);
}
/* Calcule l'image reciproque de v par m */
GEN
inverseimage_mod_p(GEN m, GEN v, GEN p)
{
  long av=avma,j,lv,tv=typ(v);
  GEN y,p1;

  if (typ(m)!=t_MAT) err(typeer,"inverseimage");
  if (tv==t_COL)
  {
    p1 = sinverseimage_mod_p(m,v,p);
    if (p1) return p1;
    avma = av; return cgetg(1,t_MAT);
  }
  if (tv!=t_MAT) err(typeer,"inverseimage");

  lv=lg(v)-1; y=cgetg(lv+1,t_MAT);
  for (j=1; j<=lv; j++)
  {
    p1 = sinverseimage_mod_p(m,(GEN)v[j],p);
    if (!p1) { avma = av; return cgetg(1,t_MAT); }
    y[j] = (long)p1;
  }
  return y;
}
/************************************************************** 
 Rather stupid implementation of linear algebra in finite fields
 **************************************************************/
static GEN Fq_add(GEN x, GEN y, GEN T, GEN p)
{
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
  case 0:
    return modii(addii(x,y),p);
  case 1:
    return Fp_add_pol_scal(x,y,p);
  case 2:
    return Fp_add_pol_scal(y,x,p);
  case 3:
    return Fp_add(x,y,p);
  } 
  return NULL;
}
static GEN Fq_mul(GEN x, GEN y, GEN T, GEN p)
{
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
  case 0:
    return modii(mulii(x,y),p);
  case 1:
    return Fp_mul_pol_scal(x,y,p);
  case 2:
    return Fp_mul_pol_scal(y,x,p);
  case 3:
    return Fp_mul_mod_pol(x,y,T,p);
  }
  return NULL;
}
static GEN Fq_neg_inv(GEN x, GEN T, GEN p)
{
  switch(typ(x)==t_POL)
  {
  case 0:
    return mpinvmod(negi(x),p);
  case 1:
    return Fp_inv_mod_pol(Fp_neg(x,p),T,p);
  }

  return NULL;
}
static GEN Fq_res(GEN x, GEN T, GEN p)
{
  ulong ltop=avma;
  switch(typ(x)==t_POL)
  {
  case 0:
    return modii(x,p);
  case 1:
    return gerepileupto(ltop,Fp_res(Fp_pol_red(x,p),T,p));
  }
  return NULL;
}
static void
Fq_gerepile_gauss_keep(GEN x, GEN T, GEN p, long m, long n, long k, long t, long av)
{
  long tetpil = avma,dec,u,A,i;

  if (DEBUGMEM > 1) err(warnmem,"gauss_pivot_keep. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (isonstack(coeff(x,u,k))) coeff(x,u,k) = (long) Fq_res(gcoeff(x,u,k),T,p);
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
      if (isonstack(coeff(x,u,i))) coeff(x,u,i) = (long) Fq_res(gcoeff(x,u,i),T,p);

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  for (u=t+1; u<=m; u++)
  {
    A=coeff(x,u,k);
    if (A<av && A>=bot) coeff(x,u,k)+=dec;
  }
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
    {
      A=coeff(x,u,i);
      if (A<av && A>=bot) coeff(x,u,i)+=dec;
    }
}

static GEN
Fq_ker_i(GEN x, GEN T, GEN p, long nontriv)
{
  GEN y,c,d,piv,mun;
  long i,j,k,r,t,n,m,av0,av,lim,tetpil;

  if (typ(x)!=t_MAT) err(typeer,"ker_mod_p");
  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  /*if (!is_bigint(p) && p[2] < (MAXHALFULONG>>1))
    return ker_mod_p_small(x, p, nontriv);*/

  m=lg(x[1])-1; r=0; av0 = avma;
  x=dummycopy(x); mun=negi(gun);
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=new_chunk(n+1);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        coeff(x,j,k) = (long) Fq_res(gcoeff(x,j,k), T, p);
        if (signe(coeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (nontriv) { avma = av0; return NULL; }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) coeff(x,d[j],k) = lclone(gcoeff(x,d[j],k));
    }
    else
    {
      c[j]=k; d[k]=j; piv = Fq_neg_inv(gcoeff(x,j,k), T, p);
      coeff(x,j,k) = (long)mun;
      for (i=k+1; i<=n; i++)
	coeff(x,j,i) = (long) Fq_mul(piv,gcoeff(x,j,i), T, p);
      for (t=1; t<=m; t++)
	if (t!=j)
	{
	  piv = Fq_res(gcoeff(x,t,k), T, p);
          if (signe(piv))
          {
            coeff(x,t,k)=zero;
            for (i=k+1; i<=n; i++)
              coeff(x,t,i) = (long)Fq_add(gcoeff(x,t,i),Fq_mul(piv,gcoeff(x,j,i), T, p), T, p);
            if (low_stack(lim, stack_lim(av,1)))
              Fq_gerepile_gauss_keep(x,T,p,m,n,k,t,av);
          }
	}
    }
  }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN c = cgetg(n+1,t_COL);

    y[j]=(long)c; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
	GEN p1=gcoeff(x,d[i],k);
	c[i] = (long) Fq_res(p1, T, p); gunclone(p1);
      }
      else
	c[i] = zero;
    c[k]=un; for (i=k+1; i<=n; i++) c[i]=zero;
  }
  return gerepile(av0,tetpil,y);
}
GEN
Fq_ker(GEN x, GEN T, GEN p)
{
  return Fq_ker_i(x, T, p, 0);
}

/*******************************************************************/
/*                                                                 */
/*                        EIGENVECTORS                             */
/*   (independent eigenvectors, sorted by increasing eigenvalue)   */
/*                                                                 */
/*******************************************************************/

GEN
eigen(GEN x, long prec)
{
  GEN y,z,rr,p,ssesp,r1,r2,r3;
  long i,k,l,ly,av,tetpil,nbrac,ex, n = lg(x);

  if (typ(x)!=t_MAT) err(typeer,"eigen");
  if (n != 1 && n != lg(x[1])) err(mattype1,"eigen");
  if (n<=2) return gcopy(x);

  av=avma; ex = 16 - bit_accuracy(prec);
  y=cgetg(n,t_MAT); z=dummycopy(x);
  p=caradj(x,0,NULL); rr=roots(p,prec); nbrac=lg(rr)-1;
  for (i=1; i<=nbrac; i++)
  {
    GEN p1 = (GEN)rr[i];
    if (!signe(p1[2])) rr[i]=p1[1];
  }
  ly=1; k=1; r2=(GEN)rr[1];
  for(;;)
  {
    r3 = ground(r2); if (gexpo(gsub(r2,r3)) < ex) r2 = r3;
    for (i=1; i<n; i++)
      coeff(z,i,i) = lsub(gcoeff(x,i,i),r2);
    ssesp=ker0(z,prec); l=lg(ssesp);
    if (l == 1)
      err(talker, "precision too low in eigen");
    for (i=1; i<l; ) y[ly++]=ssesp[i++]; /* done with this eigenspace */

    r1=r2; /* try to find a different eigenvalue */
    do
    {
      if (k==nbrac)
      {
        tetpil=avma; setlg(y,ly); /* x may not be diagonalizable */
        return gerepile(av,tetpil,gcopy(y));
      }
      k++; r2=(GEN)rr[k];
    }
    while (gexpo(gsub(r1,r2)) < ex);
  }
}

/*******************************************************************/
/*                                                                 */
/*                           DETERMINANT                           */
/*                                                                 */
/*******************************************************************/

GEN
det0(GEN a,long flag)
{
  switch(flag)
  {
    case 0: return det(a);
    case 1: return det2(a);
    default: err(flagerr,"matdet");
  }
  return NULL; /* not reached */
}

/* Exact types: choose the first non-zero pivot. Otherwise: maximal pivot */
static GEN
det_simple_gauss(GEN a, long inexact)
{
  long i,j,k,av,av1,s, nbco = lg(a)-1;
  GEN x,p;

  av=avma; s=1; x=gun; a=dummycopy(a);
  for (i=1; i<nbco; i++)
  {
    p=gcoeff(a,i,i); k=i;
    if (inexact)
    {
      long e, ex = gexpo(p);
      GEN p1;

      for (j=i+1; j<=nbco; j++)
      {
        e = gexpo(gcoeff(a,i,j));
        if (e > ex) { ex=e; k=j; }
      }
      p1 = gcoeff(a,i,k);
      if (gcmp0(p1)) return gerepileupto(av, gcopy(p1));
    }
    else if (gcmp0(p))
    {
      do k++; while(k<=nbco && gcmp0(gcoeff(a,i,k)));
      if (k>nbco) return gerepileupto(av, gcopy(p));
    }
    if (k != i)
    {
      swap(a[i],a[k]); s = -s;
      p = gcoeff(a,i,i);
    }

    x = gmul(x,p);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = gcoeff(a,i,k);
      if (!gcmp0(m))
      {
	m = gneg_i(gdiv(m,p));
	for (j=i+1; j<=nbco; j++)
	  coeff(a,j,k) = ladd(gcoeff(a,j,k), gmul(m,gcoeff(a,j,i)));
      }
    }
  }
  if (s<0) x = gneg_i(x);
  av1=avma; return gerepile(av,av1,gmul(x,gcoeff(a,nbco,nbco)));
}

/* a has integer entries, N = P^n */
GEN
det_mod_P_n(GEN a, GEN N, GEN P)
{
  long va,i,j,k,s, av = avma, nbco = lg(a)-1;
  GEN x,p;

  s=1; va=0; x=gun; a=dummycopy(a);
  p = NULL; /* for gcc -Wall */
  for (i=1; i<nbco; i++)
  {
    long fl = 0;
    for(;;)
    {
      for (k=i; k<=nbco; k++)
      {
        p=gcoeff(a,i,k);
        if (signe(p))
        {
          fl = 1;
          if (resii(p,P) != gzero) break;
        }
      }
      if (k <= nbco) break;
      va++; N = divii(N, P);
      if (!fl || is_pm1(N)) { avma=av; return gzero; }
      for (k=i; k<=nbco; k++) coeff(a,i,k) = ldivii(gcoeff(a,i,k), P);
    }
    if (k != i) { swap(a[i],a[k]); s = -s; }

    x = gmul(x,p); p = mpinvmod(p,N);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = resii(gcoeff(a,i,k), N);
      coeff(a,i,k) = zero;
      if (signe(m))
      {
	m = negi(resii(mulii(m,p), N));
	for (j=i+1; j<=nbco; j++)
	  coeff(a,j,k) = lresii(addii(gcoeff(a,j,k),
                                mulii(m,gcoeff(a,j,i))), N);
      }
    }
  }
  if (s<0) x = negi(x);
  x = resii(mulii(x,gcoeff(a,nbco,nbco)), N);
  return gerepileuptoint(av, mulii(x, gpowgs(P,va)));
}

GEN
det2(GEN a)
{
  long nbco = lg(a)-1;
  if (typ(a)!=t_MAT) err(mattype1,"det2");
  if (!nbco) return gun;
  if (nbco != lg(a[1])-1) err(mattype1,"det2");
  return det_simple_gauss(a,use_maximal_pivot(a));
}

static GEN
mydiv(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx == ty && tx == t_POL && varn(x) == varn(y))
    return gdeuc(x,y);
  return gdiv(x,y);
}

/* determinant in a ring A: all computations are done within A
 * (Gauss-Bareiss algorithm)
 */
GEN
det(GEN a)
{
  long nbco = lg(a)-1,i,j,k,av,s;
  GEN p,pprec;

  if (typ(a)!=t_MAT) err(mattype1,"det");
  if (!nbco) return gun;
  if (nbco != lg(a[1])-1) err(mattype1,"det");
  if (use_maximal_pivot(a)) return det_simple_gauss(a,1);

  av=avma; a=dummycopy(a); s=1;
  if (DEBUGLEVEL > 7) timer2();
  for (pprec=gun,i=1; i<nbco; i++,pprec=p)
  {
    GEN *ci, *ck, m, p1;
    int diveuc = (gcmp1(pprec)==0);

    p = gcoeff(a,i,i);
    if (gcmp0(p))
    {
      k=i+1; while (k<=nbco && gcmp0(gcoeff(a,i,k))) k++;
      if (k>nbco) return gerepileupto(av, gcopy(p));
      swap(a[k], a[i]); s = -s;
      p = gcoeff(a,i,i);
    }
    ci = (GEN*)a[i];
    for (k=i+1; k<=nbco; k++)
    {
      ck = (GEN*)a[k]; m = (GEN)ck[i];
      if (gcmp0(m))
      {
        if (gcmp1(p))
        {
          if (diveuc)
            a[k] = (long)mydiv((GEN)a[k], pprec);
        }
        else
          for (j=i+1; j<=nbco; j++)
          {
            p1 = gmul(p,ck[j]);
            if (diveuc) p1 = mydiv(p1,pprec);
            ck[j] = p1;
          }
      }
      else
      {
        m = gneg_i(m);
        for (j=i+1; j<=nbco; j++)
        {
          p1 = gadd(gmul(p,ck[j]), gmul(m,ci[j]));
          if (diveuc) p1 = mydiv(p1,pprec);
          ck[j] = p1;
        }
      }
    }
    if (DEBUGLEVEL > 7) msgtimer("det, col %ld / %ld",i,nbco-1);
  }
  p = gcoeff(a,nbco,nbco);
  if (s < 0) p = gneg(p); else p = gcopy(p);
  return gerepileupto(av, p);
}

/*******************************************************************/
/*                                                                 */
/*                SPECIAL HNF (FOR INTERNAL USE !!!)               */
/*                                                                 */
/*******************************************************************/
extern GEN lincomb_integral(GEN u, GEN v, GEN X, GEN Y);
extern GEN vconcat(GEN Q1, GEN Q2);

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
  long av,i,j,k,s,i1,j1,lim,zc;
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
  H = (GEN)p1[1]; /* lnz x lnz */
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
  long av=avma, i,j;
  GEN p1, matj, matgen;
  long co = lg(mat);
  long li = lg(perm);

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

#define gswap(x,y) { long *_t=x; x=y; y=_t; }

/* HNF reduce a relation matrix (column operations + row permutation)
** Input:
**   mat = (li-1) x (co-1) matrix of long
**   C   = r x (co-1) matrix of GEN
**   perm= permutation vector (length li-1), indexing the rows of mat: easier
**     to maintain perm than to copy rows. For columns we can do it directly
**     using e.g. swap(mat[i], mat[j])
**   k0 = integer. The k0 first lines of mat are dense, the others are sparse.
** Output: cf ASCII art in the function body
**
** row permutations applied to perm
** column operations applied to C.
**/
GEN
hnfspec(long** mat, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, long k0)
{
  long av=avma,av2,*p,i,j,k,lk0,col,lig,*matj;
  long n,s,t,lim,nlze,lnz,nr;
  GEN p1,p2,matb,matbnew,vmax,matt,T,extramat;
  GEN B,H,dep,permpro;
  GEN *gptr[4];
  long co = lg(mat);
  long li = lg(perm); /* = lg(mat[1]) */
  int updateT = 1;

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
	lk0++; swap(perm[i], perm[lk0]);
        i=lig; continue;

      case 1: /* move trivial generator between lig+1 and li */
	swap(perm[i], perm[lig]);
        swap(T[n], T[col]);
	gswap(mat[n], mat[col]); p = mat[col];
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
    swap(perm[i], perm[lig]);
    swap(T[n], T[col]); p1 = (GEN)T[col];
    gswap(mat[n], mat[col]); p = mat[col];
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
      T = gerepileupto(av2, gcopy(T));
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

    swap(perm[i], perm[lig]);
    swap(vmax[n], vmax[col]);
    gswap(mat[n], mat[col]); p = mat[col];
    swap(T[n], T[col]); p1 = (GEN)T[col];
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      p1 = gneg(p1); T[col] = (long)p1;
    }
    for (j=1; j<col; j++)
    {
      matj = mat[j];
      if (! (t = matj[perm[lig]]) ) continue;
      if (vmax[col] && labs(t) >= (HIGHBIT-vmax[j]) / vmax[col]) goto END2;

      for (s=0, i=lk0+1; i<=lig; i++)
        absmax(s, matj[perm[i]] -= t*p[perm[i]]);
      vmax[j] = s;
      T[j] = (long)lincomb_integral(gun,stoi(-t), (GEN)T[j],p1);
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"hnfspec[2]");
      T = gerepileupto(av2,gcopy(T));
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
        T[j] = (long)lincomb_integral(gun,negi(p2), (GEN)T[j],Tk);
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
  long av = avma, i,j,lextra,colnew;
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
    if (DEBUGLEVEL>7)
    {
      fprintferr("mit = %Z\n",H);
      fprintferr("C = %Z\n",p1);
    }
    msgtimer("hnfadd (%ld)",lextra);
  }
  return H;
}

/* return a solution of congruence system sum M_{ i,j } X_j = Y_i mod D_i
 * If ptu1 != NULL, put in *ptu1 a Z-basis of the homogeneous system
 */
static GEN
gaussmoduloall(GEN M, GEN D, GEN Y, GEN *ptu1)
{
  long n,m,i,j,lM,av=avma,tetpil;
  GEN p1,delta,H,U,u1,u2,x;

  if (typ(M)!=t_MAT) err(typeer,"gaussmodulo");
  lM = lg(M); m = lM-1;
  if (!m)
  {
    if ((typ(Y)!=t_INT && lg(Y)!=1)
     || (typ(D)!=t_INT && lg(D)!=1)) err(consister,"gaussmodulo");
    return gzero;
  }
  n = lg(M[1])-1;
  switch(typ(D))
  {
    case t_VEC:
    case t_COL: delta=diagonal(D); break;
    case t_INT: delta=gscalmat(D,n); break;
    default: err(typeer,"gaussmodulo");
      return NULL; /* not reached */
  }
  if (typ(Y) == t_INT)
  {
    p1 = cgetg(n+1,t_COL);
    for (i=1; i<=n; i++) p1[i]=(long)Y;
    Y = p1;
  }
  p1 = hnfall(concatsp(M,delta));
  H = (GEN)p1[1]; U = (GEN)p1[2];
  Y = gauss(H,Y);
  if (!gcmp1(denom(Y))) return gzero;
  u1 = cgetg(m+1,t_MAT);
  u2 = cgetg(n+1,t_MAT);
  for (j=1; j<=m; j++)
  {
    p1 = (GEN)U[j]; setlg(p1,lM);
    u1[j] = (long)p1;
  }
  U += m;
  for (j=1; j<=n; j++)
  {
    p1 = (GEN)U[j]; setlg(p1,lM);
    u2[j] = (long)p1;
  }
  x = gmul(u2,Y);
  tetpil=avma; x=lllreducemodmatrix(x,u1);
  if (!ptu1) x = gerepile(av,tetpil,x);
  else
  {
    GEN *gptr[2];
    *ptu1=gcopy(u1); gptr[0]=ptu1; gptr[1]=&x;
    gerepilemanysp(av,tetpil,gptr,2);
  }
  return x;
}

GEN
matsolvemod0(GEN M, GEN D, GEN Y, long flag)
{
  long av;
  GEN p1,y;

  if (!flag) return gaussmoduloall(M,D,Y,NULL);

  av=avma; y = cgetg(3,t_VEC);
  p1 = gaussmoduloall(M,D,Y, (GEN*)y+2);
  if (p1==gzero) { avma=av; return gzero; }
  y[1] = (long)p1; return y;
}

GEN
gaussmodulo2(GEN M, GEN D, GEN Y)
{
  return matsolvemod0(M,D,Y,1);
}

GEN
gaussmodulo(GEN M, GEN D, GEN Y)
{
  return matsolvemod0(M,D,Y,0);
}
