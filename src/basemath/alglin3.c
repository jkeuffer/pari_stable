/* $Id$

Copyright (C) 2012  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**                         LINEAR ALGEBRA                         **/
/**                          (third part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                         TRANSPOSE                               */
/*                                                                 */
/*******************************************************************/
/* A[x0,]~ */
static GEN
row_transpose(GEN A, long x0)
{
  long i, lB = lg(A);
  GEN B  = cgetg(lB, t_COL);
  for (i=1; i<lB; i++) gel(B, i) = gcoeff(A, x0, i);
  return B;
}
static GEN
row_transposecopy(GEN A, long x0)
{
  long i, lB = lg(A);
  GEN B  = cgetg(lB, t_COL);
  for (i=1; i<lB; i++) gel(B, i) = gcopy(gcoeff(A, x0, i));
  return B;
}

/* No copy*/
GEN
shallowtrans(GEN x)
{
  long i, dx, lx, tx = typ(x);
  GEN y;

  if (! is_matvec_t(tx)) pari_err_TYPE("shallowtrans",x);
  switch(tx)
  {
    case t_VEC:
      y = leafcopy(x); settyp(y,t_COL); break;

    case t_COL:
      y = leafcopy(x); settyp(y,t_VEC); break;

    case t_MAT:
      lx = lg(x); if (lx==1) return cgetg(1,t_MAT);
      dx = lg(x[1]); y = cgetg(dx,tx);
      for (i = 1; i < dx; i++) gel(y,i) = row_transpose(x,i);
      break;

    default: y = x; break;
  }
  return y;
}

GEN
gtrans(GEN x)
{
  long i, dx, lx, tx = typ(x);
  GEN y;

  if (! is_matvec_t(tx)) pari_err_TYPE("gtrans",x);
  switch(tx)
  {
    case t_VEC:
      y = gcopy(x); settyp(y,t_COL); break;

    case t_COL:
      y = gcopy(x); settyp(y,t_VEC); break;

    case t_MAT:
      lx = lg(x); if (lx==1) return cgetg(1,t_MAT);
      dx = lg(x[1]); y = cgetg(dx,tx);
      for (i = 1; i < dx; i++) gel(y,i) = row_transposecopy(x,i);
      break;

    default: y = gcopy(x); break;
  }
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                           EXTRACTION                            */
/*                                                                 */
/*******************************************************************/

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
  if (!*s) return 0;
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

static int
extract_selector_ok(long lx, GEN L)
{
  long i, l;
  switch (typ(L))
  {
    case t_INT: {
      long maxj;
      if (!signe(L)) return 1;
      l = lgefint(L)-1;
      maxj = BITS_IN_LONG - bfffo(*int_MSW(L));
      return ((l-2) * BITS_IN_LONG + maxj < lx);
    }
    case t_STR: {
      long first, last, cmpl;
      return get_range(GSTR(L), &first, &last, &cmpl, lx);
    }
    case t_VEC: case t_COL:
      l = lg(L);
      for (i=1; i<l; i++)
      {
        long j = itos(gel(L,i));
        if (j>=lx || j<=0) return 0;
      }
      return 1;
    case t_VECSMALL:
      l = lg(L);
      for (i=1; i<l; i++)
      {
        long j = L[i];
        if (j>=lx || j<=0) return 0;
      }
      return 1;
  }
  return 0;
}

GEN
shallowextract(GEN x, GEN L)
{
  long i,j, tl = typ(L), tx = typ(x), lx = lg(x);
  GEN y;

  switch(tx)
  {
    case t_VEC:
    case t_COL:
    case t_MAT:
    case t_VECSMALL: break;
    default: pari_err_TYPE("extract",x);

  }
  if (tl==t_INT)
  { /* extract components of x as per the bits of mask L */
    long k, l, ix, iy, maxj;
    GEN Ld;
    if (!signe(L)) return cgetg(1,tx);
    y = new_chunk(lx);
    l = lgefint(L)-1; ix = iy = 1;
    maxj = BITS_IN_LONG - bfffo(*int_MSW(L));
    if ((l-2) * BITS_IN_LONG + maxj >= lx)
      pari_err_TYPE("vecextract [mask too large]", L);
    for (k = 2, Ld = int_LSW(L); k < l; k++, Ld = int_nextW(Ld))
    {
      ulong B = *Ld;
      for (j = 0; j < BITS_IN_LONG; j++, B >>= 1, ix++)
        if (B & 1) y[iy++] = x[ix];
    }
    { /* k = l */
      ulong B = *Ld;
      for (j = 0; j < maxj; j++, B >>= 1, ix++)
        if (B & 1) y[iy++] = x[ix];
    }
    y[0] = evaltyp(tx) | evallg(iy);
    return y;
  }
  if (tl==t_STR)
  {
    char *s = GSTR(L);
    long first, last, cmpl, d;
    if (! get_range(s, &first, &last, &cmpl, lx))
      pari_err_TYPE("vecextract [incorrect range]", L);
    if (lx == 1) return cgetg(1,tx);
    d = last - first;
    if (cmpl)
    {
      if (d >= 0)
      {
        y = cgetg(lx - (1+d),tx);
        for (j=1; j<first; j++) gel(y,j) = gel(x,j);
        for (i=last+1; i<lx; i++,j++) gel(y,j) = gel(x,i);
      }
      else
      {
        y = cgetg(lx - (1-d),tx);
        for (j=1,i=lx-1; i>first; i--,j++) gel(y,j) = gel(x,i);
        for (i=last-1; i>0; i--,j++) gel(y,j) = gel(x,i);
      }
    }
    else
    {
      if (d >= 0)
      {
        y = cgetg(d+2,tx);
        for (i=first,j=1; i<=last; i++,j++) gel(y,j) = gel(x,i);
      }
      else
      {
        y = cgetg(2-d,tx);
        for (i=first,j=1; i>=last; i--,j++) gel(y,j) = gel(x,i);
      }
    }
    return y;
  }

  if (is_vec_t(tl))
  {
    long ll=lg(L); y=cgetg(ll,tx);
    for (i=1; i<ll; i++)
    {
      j = itos(gel(L,i));
      if (j>=lx || j<=0) pari_err(e_MISC,"no such component in vecextract");
      gel(y,i) = gel(x,j);
    }
    return y;
  }
  if (tl == t_VECSMALL)
  {
    long ll=lg(L); y=cgetg(ll,tx);
    for (i=1; i<ll; i++)
    {
      j = L[i];
      if (j>=lx || j<=0) pari_err(e_MISC,"no such component in vecextract");
      gel(y,i) = gel(x,j);
    }
    return y;
  }
  pari_err_TYPE("vecextract [mask]", L);
  return NULL; /* not reached */
}

/* does the component selector l select 0 component ? */
static int
select_0(GEN l)
{
  switch(typ(l))
  {
    case t_INT:
      return (!signe(l));
    case t_VEC: case t_COL: case t_VECSMALL:
      return (lg(l) == 1);
  }
  return 0;
}

GEN
extract0(GEN x, GEN l1, GEN l2)
{
  pari_sp av = avma, av2;
  GEN y;
  if (! l2)
  {
    y = shallowextract(x, l1);
    if (lg(y) == 1 || typ(y) == t_VECSMALL) return y;
    av2 = avma;
    y = gcopy(y);
  }
  else
  {
    if (typ(x) != t_MAT) pari_err_TYPE("extract",x);
    y = shallowextract(x,l2);
    if (select_0(l1)) { avma = av; return zeromat(0, lg(y)-1); }
    if (lg(y) == 1 && lg(x) > 1)
    {
      if (!extract_selector_ok(lg(gel(x,1)), l1))
        pari_err_TYPE("vecextract [incorrect mask]", l1);
      avma = av; return cgetg(1, t_MAT);
    }
    y = shallowextract(shallowtrans(y), l1);
    av2 = avma;
    y = gtrans(y);
  }
  stackdummy(av, av2);
  return y;
}

static long
vecslice_parse_arg(long lA, long *y1, long *y2, long *skip)
{
  *skip=0;
  if (!*y1)
  {
    if (*y2)
    {
      if (*y2<0) *y2 += lA;
      if (*y2<=0 || *y2>=lA)
        pari_err_DIM("_[..]");
      *skip=*y2;
    }
    *y1 = 1; *y2 = lA-1;
  }
  else if (!*y2) *y2 = *y1;
  if (*y1<0) *y1 += lA;
  if (*y2<0) *y2 += lA;
  if (*y1<=0 || *y1>*y2 || *y2>=lA) pari_err_DIM("_[..]");
  return *y2 - *y1 + 2 - !!*skip;
}

GEN
vecslice0(GEN A, long y1, long y2)
{
  GEN B;
  long t = typ(A), skip;
  long i,lB, lA=lg(A);
  if (!is_vec_t(t)) pari_err_TYPE("_[_.._]",A);
  lB = vecslice_parse_arg(lA, &y1, &y2, &skip);
  B = cgetg(lB, t);
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) {i--; continue; }
    gel(B,i) = gcopy(gel(A,y1));
  }
  return B;
}

GEN
matslice0(GEN A, long x1, long x2, long y1, long y2)
{
  GEN B;
  long i,lB, lA=lg(A), skip;
  if (typ(A)!=t_MAT) pari_err_TYPE("_[_.._,_.._]",A);
  lB = vecslice_parse_arg(lA, &y1, &y2, &skip);
  B = cgetg(lB, t_MAT);
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) {i--; continue; }
    gel(B,i) = vecslice0(gel(A,y1),x1,x2);
  }
  return B;
}

GEN
vecrange(GEN a, GEN b)
{
  GEN y;
  long i, l;
  if (typ(a)!=t_INT) pari_err_TYPE("[_.._]",a);
  if (typ(b)!=t_INT) pari_err_TYPE("[_.._]",b);
  if (cmpii(a,b)>0) return cgetg(1,t_VEC);
  l = itos(subii(b,a))+1;
  a = setloop(a);
  y = cgetg(l+1, t_VEC);
  for (i=1; i<=l; incloop(a), i++)
    gel(y,i) = icopy(a);
  return y;
}

GEN
vecrangess(long a, long b)
{
  GEN y;
  long i, l;
  if (a>b) return cgetg(1,t_VEC);
  l = b-a+1;
  y = cgetg(l+1, t_VEC);
  for (i=1; i<=l; a++, i++)
    gel(y,i) = stoi(a);
  return y;
}

GEN
genindexselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  long l = lg(A), i, lv = 1;
  GEN v = cgetg(l, t_VECSMALL);
  pari_sp av = avma;
  for (i = 1; i < l; i++) {
    if (f(E, gel(A,i))) v[lv++] = i;
    avma = av;
  }
  fixlg(v, lv); return v;
}
static GEN
extract_copy(GEN A, GEN v)
{
  long i, l = lg(v);
  GEN B = cgetg(l, typ(A));
  for (i = 1; i < l; i++) gel(B,i) = gcopy(gel(A,v[i]));
  return B;
}
/* as genselect, but treat A [ t_VEC,t_COL, or t_MAT] as a t_VEC */
GEN
vecselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  GEN v = genindexselect(E, f, A);
  A = extract_copy(A, v); settyp(A, t_VEC);
  return A;
}
GEN
genselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  GEN v;/* v left on stack for efficiency */
  switch(typ(A))
  {
    case t_LIST:
    {
      GEN L, B;
      A = list_data(A);
      if (!A) return listcreate();
      L = cgetg(3, t_LIST);
      v = genindexselect(E, f, A);
      B = extract_copy(A, v);
      list_nmax(L) = lg(B)-1;
      list_data(L) = B; return L;
    }
    case t_VEC: case t_COL: case t_MAT:
      v = genindexselect(E, f, A);
      return extract_copy(A, v);
  }
  pari_err_TYPE("select",A);
  return NULL; /*not reached*/
}

GEN
select0(GEN f, GEN x, long flag)
{
  if (typ(f) != t_CLOSURE || closure_arity(f) < 1) pari_err_TYPE("select", f);
  switch(flag)
  {
    case 0: return genselect((void *) f, gp_callbool, x);
    case 1: return genindexselect((void *) f, gp_callbool, x);
    default: pari_err_FLAG("select");
             return NULL;/*not reached*/
  }
}

/* as genapply, but treat A [ t_VEC,t_COL, or t_MAT] as a t_VEC */
GEN
vecapply(void *E, GEN (*f)(void* E, GEN x), GEN x)
{
  long i, lx;
  GEN y = cgetg_copy(x, &lx);
  for (i = 1; i < lx; i++) gel(y,i) = f(E, gel(x,i));
  settyp(y, t_VEC); return y;
}
GEN
genapply(void *E, GEN (*f)(void* E, GEN x), GEN x)
{
  long i, lx, tx = typ(x);
  GEN y;
  if (is_scalar_t(tx)) return f(E, x);
  switch(tx) {
    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = f(E, gel(x,i));
      return normalizepol_lg(y, lx);
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = f(E, gel(x,i));
      return normalize(y);
    case t_LIST: {
      GEN L;
      x = list_data(x);
      if (!x) return listcreate();
      L = cgetg(3, t_LIST);
      y = cgetg_copy(x, &lx);
      for (i = 1; i < lx; i++) gel(y,i) = f(E, gel(x,i));
      list_nmax(L) = lx-1;
      list_data(L) = y; return L;
    }
    case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i = 1; i < lx; i++) gel(y,i) = genapply(E, f, gel(x,i));
      return y;

    case t_VEC: case t_COL:
      y = cgetg_copy(x, &lx);
      for (i = 1; i < lx; i++) gel(y,i) = f(E, gel(x,i));
      return y;
  }
  pari_err_TYPE("apply",x);
  return NULL; /* not reached */
}

GEN
apply0(GEN f, GEN x)
{
  if (typ(f) != t_CLOSURE || closure_arity(f) < 1) pari_err_TYPE("apply",f);
  return genapply((void *) f, gp_call, x);
}

GEN
vecselapply(void *Epred, long (*pred)(void* E, GEN x), void *Efun, GEN (*fun)(void* E, GEN x), GEN A)
{
  GEN y;
  long i, l = lg(A), nb=1;
  y = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
    if (pred(Epred, gel(A,i)))
      gel(y,nb++) = fun(Efun, gel(A,i));
  fixlg(y,nb);
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                     SCALAR-MATRIX OPERATIONS                    */
/*                                                                 */
/*******************************************************************/
GEN
gtomat(GEN x)
{
  long lx, i;
  GEN y;

  if (!x) return cgetg(1, t_MAT);
  switch(typ(x))
  {
    case t_LIST:
      x = list_data(x);
      if (!x) return cgetg(1, t_MAT);
      /* fall through */
    case t_VEC: {
      lx=lg(x); y=cgetg(lx,t_MAT);
      if (lx == 1) break;
      if (typ(x[1]) == t_COL) {
        long h = lg(x[1]);
        for (i=2; i<lx; i++) {
          if (typ(x[i]) != t_COL || lg(x[i]) != h) break;
        }
        if (i == lx) { /* matrix with h-1 rows */
          y = cgetg(lx, t_MAT);
          for (i=1 ; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
          return y;
        }
      }
      for (i=1; i<lx; i++) gel(y,i) = mkcolcopy(gel(x,i));
      break;
    }
    case t_COL:
      lx = lg(x);
      if (lx == 1) return cgetg(1, t_MAT);
      if (typ(x[1]) == t_VEC) {
        long j, h = lg(x[1]);
        for (i=2; i<lx; i++) {
          if (typ(x[i]) != t_VEC || lg(x[i]) != h) break;
        }
        if (i == lx) { /* matrix with h cols */
          y = cgetg(h, t_MAT);
          for (j=1 ; j<h; j++) {
            gel(y,j) = cgetg(lx, t_COL);
            for (i=1; i<lx; i++) gcoeff(y,i,j) = gcopy(gmael(x,i,j));
          }
          return y;
        }
      }
      y = mkmatcopy(x); break;
    case t_MAT:
      y = gcopy(x); break;
    case t_QFI: case t_QFR: {
      GEN b;
      y = cgetg(3,t_MAT); b = gmul2n(gel(x,2),-1);
      gel(y,1) = mkcol2(icopy(gel(x,1)), b);
      gel(y,2) = mkcol2(b, icopy(gel(x,3)));
      break;
    }
    default:
      y = cgetg(2,t_MAT); gel(y,1) = mkcolcopy(x);
      break;
  }
  return y;
}

/* create the diagonal matrix, whose diagonal is given by x */
GEN
diagonal(GEN x)
{
  long j, lx, tx = typ(x);
  GEN y;

  if (! is_matvec_t(tx)) return scalarmat(x,1);
  if (tx==t_MAT)
  {
    if (RgM_isdiagonal(x)) return gcopy(x);
    pari_err_TYPE("diagonal",x);
  }
  lx=lg(x); y=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    gel(y,j) = zerocol(lx-1);
    gcoeff(y,j,j) = gcopy(gel(x,j));
  }
  return y;
}
/* same, assuming x is a t_VEC/t_COL. Not memory clean. */
GEN
diagonal_shallow(GEN x)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx,t_MAT);

  for (j=1; j<lx; j++)
  {
    gel(y,j) = zerocol(lx-1);
    gcoeff(y,j,j) = gel(x,j);
  }
  return y;
}

/* compute m*diagonal(d) */
GEN
matmuldiagonal(GEN m, GEN d)
{
  long j, lx;
  GEN y = cgetg_copy(m, &lx);

  if (typ(m)!=t_MAT) pari_err_TYPE("matmuldiagonal",m);
  if (! is_vec_t(typ(d))) pari_err_TYPE("matmuldiagonal",d);
  if (lg(d) != lx) pari_err_OP("operation 'matmuldiagonal'", m,d);
  for (j=1; j<lx; j++) gel(y,j) = RgC_Rg_mul(gel(m,j), gel(d,j));
  return y;
}

/* compute A*B assuming the result is a diagonal matrix */
GEN
matmultodiagonal(GEN A, GEN B)
{
  long i, j, hA, hB, lA = lg(A), lB = lg(B);
  GEN y = matid(lB-1);

  if (typ(A) != t_MAT) pari_err_TYPE("matmultodiagonal",A);
  if (typ(B) != t_MAT) pari_err_TYPE("matmultodiagonal",B);
  hA = (lA == 1)? lB: lg(A[1]);
  hB = (lB == 1)? lA: lg(B[1]);
  if (lA != hB || lB != hA) pari_err_OP("operation 'matmultodiagonal'", A,B);
  for (i=1; i<lB; i++)
  {
    GEN z = gen_0;
    for (j=1; j<lA; j++) z = gadd(z, gmul(gcoeff(A,i,j),gcoeff(B,j,i)));
    gcoeff(y,i,i) = z;
  }
  return y;
}

/* [m[1,1], ..., m[l,l]], internal */
GEN
RgM_diagonal_shallow(GEN m)
{
  long i, lx = lg(m);
  GEN y = cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) gel(y, i) = gcoeff(m,i,i);
  return y;
}

/* same, public function */
GEN
RgM_diagonal(GEN m)
{
  long i, lx = lg(m);
  GEN y = cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) gel(y,i) = gcopy(gcoeff(m,i,i));
  return y;
}

