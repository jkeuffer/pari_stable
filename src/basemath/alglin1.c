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
/**                          (first part)                          **/
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

GEN
genselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  long i, l, nb = 0, t = typ(A);
  GEN B, v;/* v left on stack for efficiency */
  pari_sp av;
  if (t == t_LIST)
  {
    GEN L;
    A = list_data(A);
    if (!A) return listcreate();
    L = cgetg(3, t_LIST);
    l = lg(A); v = cgetg(l, t_VECSMALL); av = avma;
    for (i = 1; i < l; i++) {
      if (f(E, gel(A,i))) v[++nb] = i;
      avma = av;
    }
    B = cgetg(nb+1, t_VEC);
    for (i = 1; i <= nb; i++) gel(B, i) = gcopy(gel(A,v[i]));
    list_nmax(L) = nb;
    list_data(L) = B; return L;
  }
  else
    if (!is_matvec_t(t)) pari_err_TYPE("select",A);

  l = lg(A); v = cgetg(l, t_VECSMALL); av = avma;
  for (i = 1; i < l; i++) {
    if (f(E, gel(A,i))) v[++nb] = i;
    avma = av;
  }
  B = cgetg(nb+1, t);
  for (i = 1; i <= nb; i++) gel(B, i) = gcopy(gel(A,v[i]));
  return B;
}

GEN
select0(GEN f, GEN x)
{
  if (typ(f) != t_CLOSURE || f[1] < 1) pari_err_TYPE("select", f);
  return genselect((void *) f, gp_callbool, x);
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
  if (typ(f) != t_CLOSURE || f[1] < 1) pari_err_TYPE("apply",f);
  return genapply((void *) f, gp_call, x);
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

/*******************************************************************/
/*                                                                 */
/*                       Solve A*X=B (Gauss pivot)                 */
/*                                                                 */
/*******************************************************************/
/* x ~ 0 compared to reference y */
int
approx_0(GEN x, GEN y)
{
  long tx = typ(x);
  if (tx == t_COMPLEX)
    return approx_0(gel(x,1), y) && approx_0(gel(x,2), y);
  return gequal0(x) ||
         (tx == t_REAL && gexpo(y) - gexpo(x) > bit_prec(x));
}
/* x a column, x0 same column in the original input matrix (for reference),
 * c list of pivots so far */
static long
gauss_get_pivot_max(GEN X, GEN X0, long ix, GEN c)
{
  GEN p, r, x = gel(X,ix), x0 = gel(X0,ix);
  long i, k = 0, ex = - (long)HIGHEXPOBIT, lx = lg(x);
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i])
      {
        long e = gexpo(gel(x,i));
        if (e > ex) { ex = e; k = i; }
      }
  }
  else
  {
    for (i=ix; i<lx; i++)
    {
      long e = gexpo(gel(x,i));
      if (e > ex) { ex = e; k = i; }
    }
  }
  if (!k) return lx;
  p = gel(x,k);
  r = gel(x0,k); if (isrationalzero(r)) r = x0;
  return approx_0(p, r)? lx: k;
}
static long
gauss_get_pivot_padic(GEN X, GEN p, long ix, GEN c)
{
  GEN x = gel(X, ix);
  long i, k = 0, ex = (long)HIGHVALPBIT, lx = lg(x);
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i] && !gequal0(gel(x,i)))
      {
        long e = ggval(gel(x,i), p);
        if (e < ex) { ex = e; k = i; }
      }
  }
  else
  {
    for (i=ix; i<lx; i++)
      if (!gequal0(gel(x,i)))
      {
        long e = ggval(gel(x,i), p);
        if (e < ex) { ex = e; k = i; }
      }
  }
  return k? k: lx;
}
static long
gauss_get_pivot_NZ(GEN X, GEN x0/*unused*/, long ix, GEN c)
{
  GEN x = gel(X, ix);
  long i, lx = lg(x);
  (void)x0;
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i] && !gequal0(gel(x,i))) return i;
  }
  else
  {
    for (i=ix; i<lx; i++)
      if (!gequal0(gel(x,i))) return i;
  }
  return lx;
}

/* Return pivot seeking function appropriate for the domain of the RgM x
 * (first non zero pivot, maximal pivot...) */
static pivot_fun
get_pivot_fun(GEN x, GEN *data)
{
  long i, j, hx, lx = lg(x);
  int res = t_INT;
  GEN p = NULL;

  *data = NULL;
  if (lx == 1) return &gauss_get_pivot_NZ;
  hx = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    GEN xj = gel(x,j);
    for (i=1; i<hx; i++)
    {
      GEN c = gel(xj,i);
      switch(typ(c))
      {
        case t_REAL:
          res = t_REAL;
          break;
        case t_COMPLEX:
          if (typ(gel(c,1)) == t_REAL || typ(gel(c,2)) == t_REAL) res = t_REAL;
          break;
        case t_INT: case t_INTMOD: case t_FRAC: case t_FFELT: case t_QUAD:
        case t_POLMOD: /* exact types */
          break;
        case t_PADIC:
          p = gel(c,2);
          res = t_PADIC;
          break;
        default: return &gauss_get_pivot_NZ;
      }
    }
  }
  switch(res)
  {
    case t_REAL: *data = x; return &gauss_get_pivot_max;
    case t_PADIC: *data = p; return &gauss_get_pivot_padic;
    default: return &gauss_get_pivot_NZ;
  }
}

static GEN
get_col(GEN a, GEN b, GEN p, long li)
{
  GEN u = cgetg(li+1,t_COL);
  long i, j;

  gel(u,li) = gdiv(gel(b,li), p);
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++) m = gsub(m, gmul(gcoeff(a,i,j), gel(u,j)));
    gel(u,i) = gerepileupto(av, gdiv(m, gcoeff(a,i,i)));
  }
  return u;
}
static GEN
Fp_get_col(GEN a, GEN b, long li, GEN p)
{
  GEN u = cgetg(li+1,t_COL);
  long i, j;

  gel(u,li) = Fp_mul(gel(b,li), gcoeff(a,li,li), p);
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++) m = subii(m, mulii(gcoeff(a,i,j), gel(u,j)));
    m = remii(m, p);
    gel(u,i) = gerepileuptoint(av, modii(mulii(m, gcoeff(a,i,i)), p));
  }
  return u;
}
static GEN
Fq_get_col(GEN a, GEN b, long li, GEN T, GEN p)
{
  GEN u = cgetg(li+1,t_COL);
  long i, j;

  gel(u,li) = Fq_mul(gel(b,li), gcoeff(a,li,li), T,p);
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++)
      m = Fq_sub(m, Fq_mul(gcoeff(a,i,j), gel(u,j), T, p), NULL,p);
    m = Fq_red(m, T,p);
    gel(u,i) = gerepileupto(av, Fq_mul(m, gcoeff(a,i,i), T,p));
  }
  return u;
}
/* assume 0 <= a[i,j] < p */
static uGEN
Fl_get_col_OK(GEN a, uGEN b, long li, ulong p)
{
  uGEN u = (uGEN)cgetg(li+1,t_VECSMALL);
  ulong m = b[li] % p;
  long i,j;

  u[li] = (m * ucoeff(a,li,li)) % p;
  for (i = li-1; i > 0; i--)
  {
    m = p - b[i]%p;
    for (j = i+1; j <= li; j++) {
      if (m & HIGHBIT) m %= p;
      m += ucoeff(a,i,j) * u[j]; /* 0 <= u[j] < p */
    }
    m %= p;
    if (m) m = ((p-m) * ucoeff(a,i,i)) % p;
    u[i] = m;
  }
  return u;
}
static uGEN
Fl_get_col(GEN a, uGEN b, long li, ulong p)
{
  uGEN u = (uGEN)cgetg(li+1,t_VECSMALL);
  ulong m = b[li] % p;
  long i,j;

  u[li] = Fl_mul(m, ucoeff(a,li,li), p);
  for (i=li-1; i>0; i--)
  {
    m = b[i]%p;
    for (j = i+1; j <= li; j++)
      m = Fl_sub(m, Fl_mul(ucoeff(a,i,j), u[j], p), p);
    if (m) m = Fl_mul(m, ucoeff(a,i,i), p);
    u[i] = m;
  }
  return u;
}

/* bk -= m * bi */
static void
_submul(GEN b, long k, long i, GEN m)
{
  gel(b,k) = gsub(gel(b,k), gmul(m, gel(b,i)));
}
static void /* same, reduce mod p */
_Fp_submul(GEN b, long k, long i, GEN m, GEN p)
{
  if (lgefint(b[i]) > lgefint(p)) gel(b,i) = remii(gel(b,i), p);
  gel(b,k) = subii(gel(b,k), mulii(m, gel(b,i)));
}
static void /* same, reduce mod (T,p) */
_Fq_submul(GEN b, long k, long i, GEN m, GEN T, GEN p)
{
  gel(b,i) = Fq_red(gel(b,i), T,p);
  gel(b,k) = gsub(gel(b,k), gmul(m, gel(b,i)));
}
static void /* assume m < p */
_Fl_submul(uGEN b, long k, long i, ulong m, ulong p)
{
  b[k] = Fl_sub(b[k], Fl_mul(m, b[i], p), p);
}
static void /* same m = 1 */
_Fl_sub(uGEN b, long k, long i, ulong p)
{
  b[k] = Fl_sub(b[k], b[i], p);
}
static void /* assume m < p && SMALL_ULONG(p) && (! (b[i] & b[k] & HIGHMASK)) */
_Fl_addmul_OK(uGEN b, long k, long i, ulong m, ulong p)
{
  b[k] += m * b[i];
  if (b[k] & HIGHMASK) b[k] %= p;
}
static void /* assume SMALL_ULONG(p) && (! (b[i] & b[k] & HIGHMASK)) */
_Fl_add_OK(uGEN b, long k, long i, ulong p)
{
  b[k] += b[i];
  if (b[k] & HIGHMASK) b[k] %= p;
}
static void /* assume m < p */
_Fl_addmul(uGEN b, long k, long i, ulong m, ulong p)
{
  b[i] %= p;
  b[k] = Fl_add(b[k], Fl_mul(m, b[i], p), p);
}
static void /* same m = 1 */
_Fl_add(uGEN b, long k, long i, ulong p)
{
  b[k] = Fl_add(b[k], b[i], p);
}

static int
init_gauss(GEN a, GEN *b, long *aco, long *li, int *iscol)
{
  *iscol = *b ? (typ(*b) == t_COL): 0;
  *aco = lg(a) - 1;
  if (!*aco) /* a empty */
  {
    if (*b && lg(*b) != 1) pari_err_DIM("gauss");
    *li = 0; return 0;
  }
  *li = lg(a[1])-1;
  if (*li < *aco) pari_err_DIM("gauss");
  if (*b)
  {
    if (*li != *aco) pari_err_DIM("gauss");
    switch(typ(*b))
    {
      case t_MAT:
        if (lg(*b) == 1) return 0;
        *b = RgM_shallowcopy(*b);
        break;
      case t_COL:
        *b = mkmat( leafcopy(*b) );
        break;
      default: pari_err_TYPE("gauss",*b);
    }
    if (lg((*b)[1])-1 != *li) pari_err_DIM("gauss");
  }
  else
    *b = matid(*li);
  return 1;
}

static int
is_modular_solve(GEN a, GEN b, GEN *u)
{
  GEN p = NULL;
  if (!RgM_is_FpM(a, &p) || !p) return 0;
  a = RgM_to_FpM(a, p);
  if (!b)
  {
    a = FpM_inv(a,p);
    if (a) a = FpM_to_mod(a, p);
  }
  else
  {
    switch(typ(b))
    {
      case t_COL:
        if (!RgV_is_FpV(b, &p)) return 0;
        b = RgC_to_FpC(b, p);
        a = FpM_gauss(a,b,p);
        if (a) a = FpC_to_mod(a, p);
        break;
      case t_MAT:
        if (!RgM_is_FpM(b, &p)) return 0;
        b = RgM_to_FpM(b, p);
        a = FpM_gauss(a,b,p);
        if (a) a = FpM_to_mod(a, p);
        break;
      default: return 0;
    }
  }
  *u = a; return 1;
}
/* Gaussan Elimination. Compute a^(-1)*b
 * b is a matrix or column vector, NULL meaning: take the identity matrix
 * If a and b are empty, the result is the empty matrix.
 *
 * li: nb lines of a and b
 * aco: nb columns of a
 * bco: nb columns of b (if matrix)
 *
 * li > aco is allowed if b = NULL, in which case return c such that c a = Id */
GEN
RgM_solve(GEN a, GEN b)
{
  pari_sp av = avma, lim = stack_lim(av,1);
  long i, j, k, li, bco, aco;
  int iscol;
  pivot_fun pivot;
  GEN p, u, data;

  if (is_modular_solve(a,b,&u)) return gerepileupto(av, u);
  avma = av;
  if (!init_gauss(a, &b, &aco, &li, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  pivot = get_pivot_fun(a, &data);
  a = RgM_shallowcopy(a);
  bco = lg(b)-1;
  if(DEBUGLEVEL>4) err_printf("Entering gauss\n");

  p = NULL; /* gcc -Wall */
  for (i=1; i<=aco; i++)
  {
    /* k is the line where we find the pivot */
    k = pivot(a, data, i, NULL);
    if (k > li) return NULL;
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    p = gcoeff(a,i,i);
    if (i == aco) break;

    for (k=i+1; k<=li; k++)
    {
      GEN m = gcoeff(a,k,i);
      if (!gequal0(m))
      {
        m = gdiv(m,p);
        for (j=i+1; j<=aco; j++) _submul(gel(a,j),k,i,m);
        for (j=1;   j<=bco; j++) _submul(gel(b,j),k,i,m);
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gauss. i=%ld",i);
      gerepileall(av,2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = get_col(a,gel(b,j),p,aco);
  return gerepilecopy(av, iscol? gel(u,1): u);
}

/* assume dim A >= 1, A invertible + upper triangular  */
static GEN
RgM_inv_upper_ind(GEN A, long index)
{
  long n = lg(A)-1, i = index, j;
  GEN u = zerocol(n);
  gel(u,i) = ginv(gcoeff(A,i,i));
  for (i--; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gneg(gmul(gcoeff(A,i,i+1),gel(u,i+1))); /* j = i+1 */
    for (j=i+2; j<=n; j++) m = gsub(m, gmul(gcoeff(A,i,j),gel(u,j)));
    gel(u,i) = gerepileupto(av, gdiv(m, gcoeff(A,i,i)));
  }
  return u;
}
GEN
RgM_inv_upper(GEN A)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = RgM_inv_upper_ind(A, i);
  return B;
}

static GEN
split_realimag_col(GEN z, long r1, long r2)
{
  long i, ru = r1+r2;
  GEN x = cgetg(ru+r2+1,t_COL), y = x + r2;
  for (i=1; i<=r1; i++) {
    GEN a = gel(z,i);
    if (typ(a) == t_COMPLEX) a = gel(a,1); /* paranoia: a should be real */
    gel(x,i) = a;
  }
  for (   ; i<=ru; i++) {
    GEN b, a = gel(z,i);
    if (typ(a) == t_COMPLEX) { b = gel(a,2); a = gel(a,1); } else b = gen_0;
    gel(x,i) = a;
    gel(y,i) = b;
  }
  return x;
}
GEN
split_realimag(GEN x, long r1, long r2)
{
  long i,l; GEN y;
  if (typ(x) == t_COL) return split_realimag_col(x,r1,r2);
  y = cgetg_copy(x, &l);
  for (i=1; i<l; i++) gel(y,i) = split_realimag_col(gel(x,i), r1, r2);
  return y;
}

/* assume M = (r1+r2) x (r1+2r2) matrix and y compatible vector or matrix
 * r1 first lines of M,y are real. Solve the system obtained by splitting
 * real and imaginary parts. */
GEN
RgM_solve_realimag(GEN M, GEN y)
{
  long l = lg(M), r2 = l - lg(M[1]), r1 = l-1 - 2*r2;
  return RgM_solve(split_realimag(M, r1,r2),
                   split_realimag(y, r1,r2));
}

GEN
gauss(GEN a, GEN b)
{
  GEN z;
  if (typ(a)!=t_MAT) pari_err_TYPE("gauss",a);
  if (RgM_is_ZM(a) && b &&
      ((typ(b) == t_COL && RgV_is_ZV(b)) || (typ(b) == t_MAT && RgM_is_ZM(b))))
    z = ZM_gauss(a,b);
  else
    z = RgM_solve(a,b);
  if (!z) pari_err(e_INV);
  return z;
}

/* destroy a, b */
static GEN
F2m_gauss_sp(GEN a, GEN b)
{
  long i, j, k, l, li, bco, aco = lg(a)-1;
  GEN u, d;

  if (!aco) return cgetg(1,t_MAT);
  li = coeff(a,1,1);
  d = zero_Flv(li);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    GEN ai = vecsmall_copy(gel(a,i));
    if (!d[i] && F2v_coeff(ai, i))
      k = i;
    else
      for (k = 1; k <= li; k++) if (!d[k] && F2v_coeff(ai,k)) break;
    /* found a pivot on row k */
    if (k > li) return NULL;
    d[k] = i;

    /* Clear k-th row but column-wise */
    F2v_clear(ai,k);
    for (l=1; l<=aco; l++)
    {
      GEN al = gel(a,l);
      if (!F2v_coeff(al,k)) continue;

      F2v_add_inplace(al,ai);
    }
    for (l=1; l<=bco; l++)
    {
      GEN al = gel(b,l);
      if (!F2v_coeff(al,k)) continue;

      F2v_add_inplace(al,ai);
    }
  }
  u = gcopy(b);
  for (j = 1; j <= bco; j++)
  {
    GEN bj = gel(b, j), uj = gel(u, j);

    for (i = 1; i <= li; i++)
      if (d[i] && d[i] != i) /* can d[i] still be 0 ? */
      {
        if (F2v_coeff(bj, i))
          F2v_set(uj, d[i]);
        else
          F2v_clear(uj, d[i]);
      }
  }
  return u;
}

GEN
matid_F2m(long n)
{
  GEN y = cgetg(n+1,t_MAT);
  long i;
  if (n < 0) pari_err(e_MISC,"negative size in matid_F2m");
  for (i=1; i<=n; i++) { gel(y,i) = zero_F2v(n); F2v_set(gel(y,i),i); }
  return y;
}

GEN
F2m_gauss(GEN a, GEN b) {
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return F2m_gauss_sp(F2m_copy(a), F2m_copy(b));
}

GEN
F2m_inv(GEN a) {
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return F2m_gauss_sp(F2m_copy(a), matid_F2m(lg(a)-1));
}

/* destroy a, b */
static GEN
Flm_gauss_sp(GEN a, GEN b, ulong *detp, ulong p)
{
  long i, j, k, li, bco, aco = lg(a)-1;
  const int OK_ulong = SMALL_ULONG(p);
  ulong det = 1;
  GEN u;

  if (!aco) { if (detp) *detp = 1; return cgetg(1,t_MAT); }
  li = lg(a[1])-1;
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    ulong invpiv;
    /* Fl_get_col wants 0 <= a[i,j] < p for all i,j */
    if (OK_ulong)
    {
      for (k = 1; k < i; k++) ucoeff(a,k,i) %= p;
      for (k = i; k <= li; k++)
      {
        ulong piv = ( ucoeff(a,k,i) %= p );
        if (piv)
        {
          ucoeff(a,k,i) = Fl_inv(piv, p);
          if (detp)
          {
            if (det & HIGHMASK) det %= p;
            det *= piv;
          }
          break;
        }
      }
    }
    else
    {
      for (k = i; k <= li; k++)
      {
        ulong piv = ucoeff(a,k,i);
        if (piv)
        {
          ucoeff(a,k,i) = Fl_inv(piv, p);
          if (detp) det = Fl_mul(det, piv, p);
          break;
        }
      }
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = ucoeff(a,i,i); /* 1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      ulong m = ( ucoeff(a,k,i) %= p );
      if (!m) continue;

      m = Fl_mul(m, invpiv, p);
      if (OK_ulong)
      {
        m = p - m; /* = -m */
        if (m == 1) {
          for (j=i+1; j<=aco; j++) _Fl_add_OK((uGEN)a[j],k,i, p);
          for (j=1;   j<=bco; j++) _Fl_add_OK((uGEN)b[j],k,i, p);
        } else {
          for (j=i+1; j<=aco; j++) _Fl_addmul_OK((uGEN)a[j],k,i,m, p);
          for (j=1;   j<=bco; j++) _Fl_addmul_OK((uGEN)b[j],k,i,m, p);
        }
      } else {
        if (m == 1) {
          for (j=i+1; j<=aco; j++) _Fl_sub((uGEN)a[j],k,i, p);
          for (j=1;   j<=bco; j++) _Fl_sub((uGEN)b[j],k,i, p);
        } else {
          for (j=i+1; j<=aco; j++) _Fl_submul((uGEN)a[j],k,i,m, p);
          for (j=1;   j<=bco; j++) _Fl_submul((uGEN)b[j],k,i,m, p);
        }
      }
    }
  }
  if (detp) *detp = det;
  u = cgetg(bco+1,t_MAT);
  if (OK_ulong)
    for (j=1; j<=bco; j++) ugel(u,j) = Fl_get_col_OK(a,(uGEN)b[j], aco,p);
  else
    for (j=1; j<=bco; j++) ugel(u,j) = Fl_get_col(a,(uGEN)b[j], aco,p);
  return u;
}

GEN
matid_Flm(long n)
{
  GEN y = cgetg(n+1,t_MAT);
  long i;
  if (n < 0) pari_err(e_MISC,"negative size in matid_Flm");
  for (i=1; i<=n; i++) { gel(y,i) = const_vecsmall(n, 0); ucoeff(y, i,i) = 1; }
  return y;
}

GEN
Flm_gauss(GEN a, GEN b, ulong p) {
  return Flm_gauss_sp(RgM_shallowcopy(a), RgM_shallowcopy(b), NULL, p);
}
static GEN
Flm_inv_sp(GEN a, ulong *detp, ulong p) {
  return Flm_gauss_sp(a, matid_Flm(lg(a)-1), detp, p);
}
GEN
Flm_inv(GEN a, ulong p) {
  return Flm_inv_sp(RgM_shallowcopy(a), NULL, p);
}

GEN
FpM_gauss(GEN a, GEN b, GEN p)
{
  pari_sp av = avma, lim;
  long i, j, k, li, bco, aco;
  int iscol;
  GEN u;

  if (!init_gauss(a, &b, &aco, &li, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    if (pp == 2)
    {
      a = ZM_to_F2m(a);
      b = ZM_to_F2m(b);
      u = F2m_gauss_sp(a,b);
      if (!u) {avma = av; return u;}
      u = iscol? F2c_to_ZC(gel(u,1)): F2m_to_ZM(u);
    }
    else
    {
      a = ZM_to_Flm(a, pp);
      b = ZM_to_Flm(b, pp);
      u = Flm_gauss_sp(a,b, NULL, pp);
      if (!u) {avma = av; return u;}
      u = iscol? Flc_to_ZC(gel(u,1)): Flm_to_ZM(u);
    }
    return gerepileupto(av, u);
  }
  lim = stack_lim(av,1);
  a = RgM_shallowcopy(a);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    GEN invpiv;
    for (k = i; k <= li; k++)
    {
      GEN piv = remii(gcoeff(a,k,i), p);
      if (signe(piv)) { gcoeff(a,k,i) = Fp_inv(piv, p); break; }
      gcoeff(a,k,i) = gen_0;
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = gcoeff(a,i,i); /* 1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      GEN m = remii(gcoeff(a,k,i), p); gcoeff(a,k,i) = gen_0;
      if (!signe(m)) continue;

      m = Fp_mul(m, invpiv, p);
      for (j=i+1; j<=aco; j++) _Fp_submul(gel(a,j),k,i,m, p);
      for (j=1  ; j<=bco; j++) _Fp_submul(gel(b,j),k,i,m, p);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FpM_gauss. i=%ld",i);
      gerepileall(av,2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = Fp_get_col(a, gel(b,j), aco, p);
  return gerepilecopy(av, iscol? gel(u,1): u);
}
GEN
FqM_gauss(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp  av = avma, lim;
  long i, j, k, li, bco, aco = lg(a)-1;
  int iscol;
  GEN u;

  if (!T) return FpM_gauss(a,b,p);
  if (!init_gauss(a, &b, &aco, &li, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);

  lim = stack_lim(av,1);
  a = RgM_shallowcopy(a);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    GEN invpiv;
    for (k = i; k <= li; k++)
    {
      GEN piv = Fq_red(gcoeff(a,k,i), T,p);
      if (signe(piv)) { gcoeff(a,k,i) = Fq_inv(piv,T,p); break; }
      gcoeff(a,k,i) = gen_0;
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = gcoeff(a,i,i); /* 1/piv */
    for (k=i+1; k<=li; k++)
    {
      GEN m = Fq_red(gcoeff(a,k,i), T,p); gcoeff(a,k,i) = gen_0;
      if (!signe(m)) continue;

      m = Fq_mul(m, invpiv, T,p);
      for (j=i+1; j<=aco; j++) _Fq_submul(gel(a,j),k,i,m, T,p);
      for (j=1;   j<=bco; j++) _Fq_submul(gel(b,j),k,i,m, T,p);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FpM_gauss. i=%ld",i);
      gerepileall(av, 2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = Fq_get_col(a, gel(b,j), aco, T, p);
  return gerepilecopy(av, iscol? gel(u,1): u);
}

/* Dixon p-adic lifting algorithm.
 * Numer. Math. 40, 137-141 (1982), DOI: 10.1007/BF01459082 */
GEN
ZM_gauss(GEN a, GEN b0)
{
  pari_sp av = avma, av2;
  int iscol;
  long n, ncol, i, m;
  ulong p;
  byteptr d;
  GEN N, C, delta, xb, nb, nmin, res, b = b0;

  if (!init_gauss(a, &b, &n, &ncol, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  nb = gen_0; ncol = lg(b);
  for (i = 1; i < ncol; i++)
  {
    GEN ni = gnorml2(gel(b, i));
    if (cmpii(nb, ni) < 0) nb = ni;
  }
  if (!signe(nb)) { avma = av; return gcopy(b0); }
  delta = gen_1; nmin = nb;
  for (i = 1; i <= n; i++)
  {
    GEN ni = gnorml2(gel(a, i));
    if (cmpii(ni, nmin) < 0)
    {
      delta = mulii(delta, nmin); nmin = ni;
    }
    else
      delta = mulii(delta, ni);
  }
  if (!signe(nmin)) { avma = av; return NULL; }
  d = init_modular(&p); av2 = avma;
  for(;;)
  {
    C = Flm_inv(ZM_to_Flm(a, p), p);
    if (C) break;
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    avma = av2;
  }
  /* N.B. Our delta/lambda are SQUARES of those in the paper
   * log(delta lambda) / log p, where lambda is 3+sqrt(5) / 2,
   * whose log is < 1, hence + 1 (to cater for rounding errors) */
  m = (long)ceil((rtodbl(logr_abs(itor(delta,LOWDEFAULTPREC))) + 1)
                 / log((double)p));
  xb = Zlm_gauss(a, b, p, m, C);
  N = powuu(p, m);
  delta = sqrti(delta);
  if (iscol)
    res = FpC_ratlift(gel(xb,1), N, delta,delta, NULL);
  else
    res = FpM_ratlift(xb, N, delta,delta, NULL);
  return gerepileupto(av, res);
}

GEN
Zlm_gauss(GEN a, GEN b, ulong p, long e, GEN C)
{
  pari_sp av = avma, lim = stack_lim(av, 2), av2;
  GEN xi, xb, pi = gen_1, P;
  long i;
  if (!C) {
    C = Flm_inv(ZM_to_Flm(a, p), p);
    if (!C) pari_err(e_INV);
  }
  P = utoipos(p);
  av2 = avma;
  xb = xi = Flm_to_ZM(Flm_mul(C, ZM_to_Flm(b, p), p));
  for (i = 2; i <= e; i++)
  {
    pi = mulii(pi, P); /* = p^i */
    b = ZM_Z_divexact(ZM_sub(b, ZM_mul(a, xi)), P);
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Zlm_gauss. i=%ld",i);
      gerepileall(av2,3, &pi,&b,&xb);
    }
    xi = Flm_to_ZM(Flm_mul(C, ZM_to_Flm(b, p), p));
    xb = ZM_add(xb, ZM_Z_mul(xi, pi));
  }
  return gerepileupto(av, xb);
}

GEN
FpM_inv(GEN x, GEN p) { return FpM_gauss(x, NULL, p); }

/* M integral, dM such that M' = dM M^-1 is integral [e.g det(M)]. Return M' */
GEN
ZM_inv(GEN M, GEN dM)
{
  pari_sp av2, av = avma, lim = stack_lim(av,1);
  GEN Hp,q,H;
  ulong p;
  byteptr d;
  long lM = lg(M), stable = 0;
  int negate = 0;

  if (lM == 1) return cgetg(1,t_MAT);

  /* HACK: include dM = -1 ! */
  if (dM && is_pm1(dM))
  {
    /* modular algorithm computes M^{-1}, NOT multiplied by det(M) = -1.
     * We will correct (negate) at the end. */
    if (signe(dM) < 0) negate = 1;
    dM = gen_1;
  }
  av2 = avma;
  H = NULL;
  d = init_modular(&p);
  for(;;)
  {
    ulong dMp;
    GEN Mp;
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    Mp = ZM_to_Flm(M,p);
    if (dM == gen_1)
      Hp = Flm_inv_sp(Mp, NULL, p);
    else
    {
      if (dM) {
        dMp = umodiu(dM,p); if (!dMp) continue;
        Hp = Flm_inv_sp(Mp, NULL, p);
        if (!Hp) pari_err(e_INV);
      } else {
        Hp = Flm_inv_sp(Mp, &dMp, p);
        if (!Hp) continue;
      }
      if (dMp != 1) Flm_Fl_mul_inplace(Hp, dMp, p);
    }

    if (!H)
    {
      H = ZM_init_CRT(Hp, p);
      q = utoipos(p);
    }
    else
    {
      GEN qp = muliu(q,p);
      stable = ZM_incremental_CRT(&H, Hp, q,qp, p);
      q = qp;
    }
    if (DEBUGLEVEL>5) err_printf("inverse mod %ld (stable=%ld)\n", p,stable);
    if (stable) {/* DONE ? */
      if (dM != gen_1)
      { if (RgM_isscalar(ZM_mul(M, H), dM)) break; }
      else
      { if (ZM_isidentity(ZM_mul(M, H))) break; }
    }

    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZM_inv");
      gerepileall(av2, 2, &H, &q);
    }
  }
  if (DEBUGLEVEL>5) err_printf("ZM_inv done\n");
  if (negate)
    return gerepileupto(av, ZM_neg(H));
  else
    return gerepilecopy(av, H);
}

/* same as above, M rational */
GEN
QM_inv(GEN M, GEN dM)
{
  pari_sp av = avma;
  GEN cM, pM = Q_primitive_part(M, &cM);
  if (!cM) return ZM_inv(pM,dM);
  return gerepileupto(av, ZM_inv(pM, gdiv(dM,cM)));
}

/* x a ZM. Return a multiple of the determinant of the lattice generated by
 * the columns of x. From Algorithm 2.2.6 in GTM138 */
GEN
detint(GEN A)
{
  if (typ(A) != t_MAT) pari_err_TYPE("detint",A);
  RgM_check_ZM(A, "detint");
  return ZM_detmult(A);
}
GEN
ZM_detmult(GEN A)
{
  pari_sp av1, av = avma, lim = stack_lim(av,1);
  GEN B, c, v, piv;
  long rg, i, j, k, m, n = lg(A) - 1;

  if (!n) return gen_1;
  m = lg(A[1]) - 1;
  if (n < m) return gen_0;
  c = const_vecsmall(m, 0);
  av1 = avma;
  B = zeromatcopy(m,m);
  v = cgetg(m+1, t_COL);
  piv = gen_1; rg = 0;
  for (k=1; k<=n; k++)
  {
    GEN pivprec = piv;
    long t = 0;
    for (i=1; i<=m; i++)
    {
      pari_sp av2 = avma;
      GEN vi;
      if (c[i]) continue;

      vi = mulii(piv, gcoeff(A,i,k));
      for (j=1; j<=m; j++)
        if (c[j]) vi = addii(vi, mulii(gcoeff(B,j,i),gcoeff(A,j,k)));
      if (!t && signe(vi)) t = i;
      gel(v,i) = gerepileuptoint(av2, vi);
    }
    if (!t) continue;
    /* at this point c[t] = 0 */

    if (++rg >= m) { /* full rank; mostly done */
      GEN det = gel(v,t); /* last on stack */
      if (++k > n)
        det = absi(det);
      else
      {
        /* improve further; at this point c[i] is set for all i != t */
        gcoeff(B,t,t) = piv; v = centermod(gel(B,t), det);
        av1 = avma; lim = stack_lim(av1,1);
        for ( ; k<=n; k++)
        {
          det = gcdii(det, ZV_dotproduct(v, gel(A,k)));
          if (low_stack(lim, stack_lim(av1,1)))
          {
            if(DEBUGMEM>1) pari_warn(warnmem,"detint end. k=%ld",k);
            det = gerepileuptoint(av1, det);
          }
        }
      }
      return gerepileuptoint(av, det);
    }

    piv = gel(v,t);
    for (i=1; i<=m; i++)
    {
      GEN mvi;
      if (c[i] || i == t) continue;

      gcoeff(B,t,i) = mvi = negi(gel(v,i));
      for (j=1; j<=m; j++)
        if (c[j]) /* implies j != t */
        {
          pari_sp av2 = avma;
          GEN z = addii(mulii(gcoeff(B,j,i), piv), mulii(gcoeff(B,j,t), mvi));
          if (rg > 1) z = diviiexact(z, pivprec);
          gcoeff(B,j,i) = gerepileuptoint(av2, z);
        }
    }
    c[t] = k;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"detint. k=%ld",k);
      gerepileall(av1, 2, &piv,&B); v = zerovec(m);
    }
  }
  avma = av; return gen_0;
}

static void
gerepile_mat(pari_sp av, pari_sp tetpil, GEN x, long k, long m, long n, long t)
{
  pari_sp A;
  long u, i;
  size_t dec;

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;

  for (u=t+1; u<=m; u++)
  {
    A = (pari_sp)coeff(x,u,k);
    if (A < av && A >= bot) coeff(x,u,k) += dec;
  }
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
    {
      A = (pari_sp)coeff(x,u,i);
      if (A < av && A >= bot) coeff(x,u,i) += dec;
    }
}

#define COPY(x) {\
  GEN _t = (x); if (!is_universal_constant(_t)) x = gcopy(_t); \
}

static void
gerepile_gauss_ker(GEN x, long k, long t, pari_sp av)
{
  pari_sp tetpil = avma;
  long u,i, n = lg(x)-1, m = n? lg(x[1])-1: 0;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot_ker. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++) COPY(gcoeff(x,u,k));
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++) COPY(gcoeff(x,u,i));
  gerepile_mat(av,tetpil,x,k,m,n,t);
}

static void
gerepile_gauss_FpM_ker(GEN x, GEN p, long k, long t, pari_sp av)
{
  pari_sp tetpil = avma;
  long u,i, n = lg(x)-1, m = n? lg(x[1])-1: 0;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot_ker. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (isonstack(gcoeff(x,u,k))) gcoeff(x,u,k) = modii(gcoeff(x,u,k),p);
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
      if (isonstack(gcoeff(x,u,i))) gcoeff(x,u,i) = modii(gcoeff(x,u,i),p);
  gerepile_mat(av,tetpil,x,k,m,n,t);
}

/* special gerepile for huge matrices */

static void
gerepile_gauss(GEN x,long k,long t,pari_sp av, long j, GEN c)
{
  pari_sp tetpil = avma, A;
  long u,i, n = lg(x)-1, m = n? lg(x[1])-1: 0;
  size_t dec;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u]) COPY(gcoeff(x,u,k));
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++) COPY(gcoeff(x,u,i));

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u])
    {
      A=(pari_sp)coeff(x,u,k);
      if (A<av && A>=bot) coeff(x,u,k)+=dec;
    }
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++)
      {
        A=(pari_sp)coeff(x,u,i);
        if (A<av && A>=bot) coeff(x,u,i)+=dec;
      }
}

/* Reduce x modulo (invertible) y */
GEN
closemodinvertible(GEN x, GEN y)
{
  return gmul(y, ground(RgM_solve(y,x)));
}
GEN
reducemodinvertible(GEN x, GEN y)
{
  return gsub(x, closemodinvertible(x,y));
}
GEN
reducemodlll(GEN x,GEN y)
{
  return reducemodinvertible(x, ZM_lll(y, 0.75, LLL_INPLACE));
}

/*******************************************************************/
/*                                                                 */
/*                    KERNEL of an m x n matrix                    */
/*          return n - rk(x) linearly independent vectors          */
/*                                                                 */
/*******************************************************************/
/* x has INTEGER coefficients. Gauss-Bareiss */
GEN
keri(GEN x)
{
  pari_sp av, av0, lim;
  GEN c, l, y, p, pp;
  long i, j, k, r, t, n, m;

  n = lg(x)-1; if (!n) return cgetg(1,t_MAT);
  av0 = avma; m = lg(x[1])-1;
  pp = cgetg(n+1,t_COL);
  x = RgM_shallowcopy(x);
  c = const_vecsmall(m, 0);
  l = cgetg(n+1, t_VECSMALL);
  av = avma; lim = stack_lim(av,1);
  for (r=0, p=gen_1, k=1; k<=n; k++)
  {
    j = 1;
    while ( j <= m && (c[j] || !signe(gcoeff(x,j,k))) ) j++;
    if (j > m)
    {
      r++; l[k] = 0;
      for(j=1; j<k; j++)
        if (l[j]) gcoeff(x,l[j],k) = gclone(gcoeff(x,l[j],k));
      gel(pp,k) = gclone(p);
    }
    else
    {
      GEN p0 = p;
      c[j] = k; l[k] = j; p = gcoeff(x,j,k);
      for (t=1; t<=m; t++)
        if (t!=j)
        {
          GEN q = gcoeff(x,t,k);
          for (i=k+1; i<=n; i++)
          {
            pari_sp av1 = avma;
            GEN p1 = subii(mulii(p,gcoeff(x,t,i)), mulii(q,gcoeff(x,j,i)));
            gcoeff(x,t,i) = gerepileuptoint(av1, diviiexact(p1,p0));
          }
          if (low_stack(lim, stack_lim(av,1)))
          {
            GEN _p0 = gclone(p0);
            GEN _p  = gclone(p);
            gerepile_gauss_ker(x,k,t,av);
            p = icopy(_p);  gunclone(_p);
            p0= icopy(_p0); gunclone(_p0);
          }
        }
    }
  }
  if (!r) { avma = av0; y = cgetg(1,t_MAT); return y; }

  /* non trivial kernel */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    p = cgetg(n+1, t_COL);
    gel(y,j) = p; while (l[k]) k++;
    for (i=1; i<k; i++)
      if (l[i])
      {
        c = gcoeff(x,l[i],k);
        gel(p,i) = icopy(c); gunclone(c);
      }
      else
        gel(p,i) = gen_0;
    gel(p,k) = negi(gel(pp,k)); gunclone(gel(pp,k));
    for (i=k+1; i<=n; i++) gel(p,i) = gen_0;
  }
  return gerepileupto(av0, y);
}

GEN
deplin(GEN x0)
{
  pari_sp av = avma;
  long i,j,k,t,nc,nl;
  GEN D, x, y, c, l, d, ck;

  t = typ(x0);
  if (t == t_MAT) x = RgM_shallowcopy(x0);
  else
  {
    if (t != t_VEC) pari_err_TYPE("deplin",x0);
    x = gtomat(x0);
  }
  nc = lg(x)-1; if (!nc) { avma=av; return cgetg(1,t_COL); }
  nl = lg(x[1])-1;
  d = const_vec(nl, gen_1); /* pivot list */
  c = const_vecsmall(nl, 0);
  l = cgetg(nc+1, t_VECSMALL); /* not initialized */
  ck = NULL; /* gcc -Wall */
  for (k=1; k<=nc; k++)
  {
    ck = gel(x,k);
    for (j=1; j<k; j++)
    {
      GEN cj = gel(x,j), piv = gel(d,j), q = gel(ck,l[j]);
      for (i=1; i<=nl; i++)
        if (i!=l[j]) gel(ck,i) = gsub(gmul(piv, gel(ck,i)), gmul(q, gel(cj,i)));
    }

    i = gauss_get_pivot_NZ(x, NULL, k, c);
    if (i > nl) break;

    d[k] = ck[i];
    c[i] = k; l[k] = i; /* pivot d[k] in x[i,k] */
  }
  if (k > nc) { avma = av; return zerocol(nc); }
  if (k == 1) { avma = av; return scalarcol_shallow(gen_1,nc); }
  y = cgetg(nc+1,t_COL);
  gel(y,1) = gel(ck, l[1]);
  for (D=gel(d,1),j=2; j<k; j++)
  {
    gel(y,j) = gmul(gel(ck, l[j]), D);
    D = gmul(D, gel(d,j));
  }
  gel(y,j) = gneg(D);
  for (j++; j<=nc; j++) gel(y,j) = gen_0;
  y = primitive_part(y, &c);
  return c? gerepileupto(av, y): gerepilecopy(av, y);
}

/*******************************************************************/
/*                                                                 */
/*         GAUSS REDUCTION OF MATRICES  (m lines x n cols)         */
/*           (kernel, image, complementary image, rank)            */
/*                                                                 */
/*******************************************************************/
/* return the transform of x under a standard Gauss pivot. r = dim ker(x).
 * d[k] contains the index of the first non-zero pivot in column k */
static GEN
gauss_pivot_ker(GEN x0, GEN *dd, long *rr)
{
  GEN x, c, d, p, data;
  pari_sp av, lim;
  long i, j, k, r, t, n, m;
  pivot_fun pivot;

  n=lg(x0)-1; if (!n) { *dd=NULL; *rr=0; return cgetg(1,t_MAT); }
  m=lg(x0[1])-1; r=0;
  pivot = get_pivot_fun(x0, &data);
  x = RgM_shallowcopy(x0);
  c = const_vecsmall(m, 0);
  d = cgetg(n+1,t_VECSMALL);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    j = pivot(x, data, k, c);
    if (j > m)
    {
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    { /* pivot for column k on row j */
      c[j]=k; d[k]=j; p = gdiv(gen_m1,gcoeff(x,j,k));
      gcoeff(x,j,k) = gen_m1;
      /* x[j,] /= - x[j,k] */
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = gmul(p,gcoeff(x,j,i));
      for (t=1; t<=m; t++)
        if (t!=j)
        { /* x[t,] -= 1 / x[j,k] x[j,] */
          p = gcoeff(x,t,k); gcoeff(x,t,k) = gen_0;
          for (i=k+1; i<=n; i++)
            gcoeff(x,t,i) = gadd(gcoeff(x,t,i),gmul(p,gcoeff(x,j,i)));
          if (low_stack(lim, stack_lim(av,1))) gerepile_gauss_ker(x,k,t,av);
        }
    }
  }
  *dd=d; *rr=r; return x;
}

static GEN FpM_gauss_pivot(GEN x, GEN p, long *rr);
static GEN FqM_gauss_pivot(GEN x, GEN T, GEN p, long *rr);
static GEN F2m_gauss_pivot(GEN x, long *rr);
static GEN Flm_gauss_pivot(GEN x, ulong p, long *rry);

/* r = dim ker(x).
 * Returns d:
 *   d[k] != 0 contains the index of a non-zero pivot in column k
 *   d[k] == 0 if column k is a linear combination of the (k-1) first ones */
GEN
RgM_pivots(GEN x0, GEN data, long *rr, pivot_fun pivot)
{
  GEN x, c, d, p;
  long i, j, k, r, t, m, n = lg(x0)-1;
  pari_sp av, lim;

  if (RgM_is_ZM(x0)) return ZM_pivots(x0, rr);
  if (!n) { *rr = 0; return NULL; }

  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x0);
  m = lg(x[1])-1; r = 0;
  c = const_vecsmall(m, 0);
  av = avma; lim = stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    j = pivot(x, data, k, c);
    if (j > m) { r++; d[k] = 0; }
    else
    {
      c[j] = k; d[k] = j; p = gdiv(gen_m1, gcoeff(x,j,k));
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = gmul(p,gcoeff(x,j,i));

      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          p = gcoeff(x,t,k); gcoeff(x,t,k) = gen_0;
          for (i=k+1; i<=n; i++)
            gcoeff(x,t,i) = gadd(gcoeff(x,t,i), gmul(p, gcoeff(x,j,i)));
          if (low_stack(lim, stack_lim(av,1))) gerepile_gauss(x,k,t,av,j,c);
        }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = gen_0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

static long
ZM_count_0_cols(GEN M)
{
  long i, l = lg(M), n = 0;
  for (i = 1; i < l; i++)
    if (ZV_equal0(gel(M,i))) n++;
  return n;
}

static void indexrank_all(long m, long n, long r, GEN d, GEN *prow, GEN *pcol);
/* As above, integer entries */
GEN
ZM_pivots(GEN M0, long *rr)
{
  ulong mod_p;
  byteptr bp;
  GEN d, dbest = NULL;
  long m, n, i, imax, rmin, rbest, zc;
  int beenthere = 0;
  pari_sp av, av0 = avma;

  rbest = n = lg(M0)-1;
  if (n == 0) { *rr = 0; return NULL; }
  zc = ZM_count_0_cols(M0);
  if (n == zc) { *rr = zc; return zero_zv(n); }

  m = lg(M0[1])-1;
  rmin = (m < n-zc) ? n-m : zc;
  bp = init_modular(&mod_p);
  imax = (n < (1<<4))? 1: (n>>3); /* heuristic */

  for(;;)
  {
    GEN row, col, M, KM, IM, RHS, X, cX;
    long rk;
    for (av = avma, i = 0;; avma = av, i++)
    {
      NEXT_PRIME_VIADIFF_CHECK(mod_p, bp);
      d = Flm_gauss_pivot(ZM_to_Flm(M0, mod_p), mod_p, rr);
      if (*rr == rmin) goto END; /* maximal rank, return */
      if (*rr < rbest) { /* save best r so far */
        rbest = *rr;
        if (dbest) gunclone(dbest);
        dbest = gclone(d);
        if (beenthere) break;
      }
      if (!beenthere && i >= imax) break;
    }
    beenthere = 1;
    /* Dubious case: there is (probably) a non trivial kernel */
    indexrank_all(m,n, rbest, dbest, &row, &col);
    M = rowpermute(vecpermute(M0, col), row);
    rk = n - rbest; /* (probable) dimension of image */
    IM = vecslice(M,1,rk);
    KM = vecslice(M,rk+1, n);
    M = rowslice(IM, 1,rk); /* square maximal rank */
    X = ZM_gauss(M, rowslice(KM, 1,rk));
    X = Q_remove_denom(X, &cX);
    RHS = rowslice(KM,rk+1,m);
    if (cX) RHS = ZM_Z_mul(RHS, cX);
    if (ZM_equal(ZM_mul(rowslice(IM,rk+1,m), X), RHS))
    {
      d = vecsmall_copy(dbest);
      goto END;
    }
    avma = av;
  }
END:
  if (dbest) gunclone(dbest);
  return gerepileuptoleaf(av0, d);
}

static GEN
gauss_pivot(GEN x, long *rr) {
  GEN data;
  pivot_fun pivot = get_pivot_fun(x, &data);
  return RgM_pivots(x, data, rr, pivot);
}

/* compute ker(x) */
static GEN
ker_aux(GEN x)
{
  pari_sp av = avma;
  GEN d,y;
  long i,j,k,r,n;

  x = gauss_pivot_ker(x,&d,&r);
  if (!r) { avma=av; return cgetg(1,t_MAT); }
  n = lg(x)-1; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN p = cgetg(n+1,t_COL);

    gel(y,j) = p; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(p,i) = gcopy(p1); gunclone(p1);
      }
      else
        gel(p,i) = gen_0;
    gel(p,k) = gen_1; for (i=k+1; i<=n; i++) gel(p,i) = gen_0;
  }
  return gerepileupto(av,y);
}
GEN
ker(GEN x)
{
  pari_sp av = avma;
  GEN p = NULL;
  if (RgM_is_FpM(x, &p) && p)
    return gerepileupto(av, FpM_to_mod(FpM_ker(RgM_to_FpM(x, p), p), p));
  return ker_aux(x);
}
GEN
matker0(GEN x,long flag)
{
  if (typ(x)!=t_MAT) pari_err_TYPE("matker",x);
  if (!flag) return ker(x);
  RgM_check_ZM(x, "keri");
  return keri(x);
}

GEN
image(GEN x)
{
  pari_sp av = avma;
  GEN d, y, p = NULL;
  long j, k, r;

  if (typ(x)!=t_MAT) pari_err_TYPE("matimage",x);
  if (RgM_is_FpM(x, &p) && p)
    return gerepileupto(av, FpM_to_mod(FpM_image(RgM_to_FpM(x, p), p), p));
  d = gauss_pivot(x,&r);
  if (!d) { avma = av; return gcopy(x); }
  /* d left on stack for efficiency */
  r = lg(x)-1 - r; /* = dim Im(x) */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = gcopy(gel(x,k));
  return y;
}

static GEN
imagecompl_aux(GEN x, GEN(*PIVOT)(GEN,long*))
{
  pari_sp av = avma;
  GEN d,y;
  long j,i,r;

  if (typ(x)!=t_MAT) pari_err_TYPE("imagecompl",x);
  (void)new_chunk(lg(x) * 4 + 1); /* HACK */
  d = PIVOT(x,&r); /* if (!d) then r = 0 */
  avma = av; y = cgetg(r+1,t_VECSMALL);
  for (i=j=1; j<=r; i++)
    if (!d[i]) y[j++] = i;
  return y;
}
GEN
imagecompl(GEN x) { return imagecompl_aux(x, &gauss_pivot); }
GEN
ZM_imagecompl(GEN x) { return imagecompl_aux(x, &ZM_pivots); }

/* permutation giving imagecompl(x') | image(x'), x' = transpose of x */
static GEN
imagecomplspec_aux(GEN x, long *nlze, GEN(*PIVOT)(GEN,long*))
{
  pari_sp av = avma;
  GEN d,y;
  long i,j,k,l,r;

  if (typ(x)!=t_MAT) pari_err_TYPE("imagecomplspec",x);
  x = shallowtrans(x); l = lg(x);
  d = PIVOT(x,&r);
  *nlze = r;
  avma = av; /* HACK: shallowtrans(x) big enough to avoid overwriting d */
  if (!d) return identity_perm(l-1);
  y = cgetg(l,t_VECSMALL);
  for (i=j=1, k=r+1; i<l; i++)
    if (d[i]) y[k++]=i; else y[j++]=i;
  return y;
}
GEN
imagecomplspec(GEN x, long *nlze)
{ return imagecomplspec_aux(x,nlze,&gauss_pivot); }
GEN
ZM_imagecomplspec(GEN x, long *nlze)
{ return imagecomplspec_aux(x,nlze,&ZM_pivots); }

static GEN
sinverseimage(GEN mat, GEN y)
{
  pari_sp av = avma;
  long i, nbcol = lg(mat);
  GEN col,p1 = cgetg(nbcol+1,t_MAT);

  if (nbcol==1) return NULL;
  if (lg(y) != lg(mat[1])) pari_err_DIM("inverseimage");

  gel(p1,nbcol) = y;
  for (i=1; i<nbcol; i++) p1[i]=mat[i];
  p1 = ker(p1); i=lg(p1)-1;
  if (!i) return NULL;

  col = gel(p1,i); p1 = gel(col,nbcol);
  if (gequal0(p1)) return NULL;

  p1 = gneg_i(p1); setlg(col,nbcol);
  return gerepileupto(av, RgC_Rg_div(col, p1));
}

/* Calcule l'image reciproque de v par m */
GEN
inverseimage(GEN m,GEN v)
{
  pari_sp av=avma;
  long j,lv,tv=typ(v);
  GEN y,p1;

  if (typ(m)!=t_MAT) pari_err_TYPE("inverseimage",m);
  if (tv==t_COL)
  {
    p1 = sinverseimage(m,v);
    if (p1) return p1;
    avma = av; return cgetg(1,t_COL);
  }
  if (tv!=t_MAT) pari_err_TYPE("inverseimage",v);

  lv=lg(v)-1; y=cgetg(lv+1,t_MAT);
  for (j=1; j<=lv; j++)
  {
    p1 = sinverseimage(m,gel(v,j));
    if (!p1) { avma = av; return cgetg(1,t_MAT); }
    gel(y,j) = p1;
  }
  return y;
}

static GEN
get_suppl(GEN x, GEN d, long r)
{
  pari_sp av;
  GEN y, c;
  long j, k, n, rx = lg(x)-1;

  if (!rx) pari_err(e_MISC,"empty matrix in suppl");
  n = lg(x[1])-1;
  if (rx == n && r == 0) return gcopy(x);
  y = cgetg(n+1, t_MAT);
  av = avma; c = const_vecsmall(n,0);
  /* c = lines containing pivots (could get it from gauss_pivot, but cheap)
   * In theory r = 0 and d[j] > 0 for all j, but why take chances? */
  for (k = j = 1; j<=rx; j++)
    if (d[j]) { c[ d[j] ] = 1; y[k++] = x[j]; }
  for (j=1; j<=n; j++)
    if (!c[j]) y[k++] = j;
  avma = av;

  rx -= r;
  for (j=1; j<=rx; j++) gel(y,j) = gcopy(gel(y,j));
  for (   ; j<=n; j++)  gel(y,j) = col_ei(n, y[j]);
  return y;
}

static void
init_suppl(GEN x)
{
  if (lg(x) == 1) pari_err(e_MISC,"empty matrix in suppl");
  /* HACK: avoid overwriting d from gauss_pivot() after avma=av */
  (void)new_chunk(lg(x[1]) * 2);
}

/* x is an n x k matrix, rank(x) = k <= n. Return an invertible n x n matrix
 * whose first k columns are given by x. If rank(x) < k, undefined result. */
GEN
suppl(GEN x)
{
  pari_sp av = avma;
  GEN d, X = x, p = NULL;
  long r;

  if (typ(x)!=t_MAT) pari_err_TYPE("suppl",x);
  if (RgM_is_FpM(x, &p) && p)
    return gerepileupto(av, FpM_to_mod(FpM_suppl(RgM_to_FpM(x, p), p), p));
  avma = av; init_suppl(x);
  d = gauss_pivot(X,&r);
  avma = av; return get_suppl(X,d,r);
}
GEN
FpM_suppl(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN d;
  long r;

  init_suppl(x);
  d = FpM_gauss_pivot(x,p, &r);
  avma = av; return get_suppl(x,d,r);
}
GEN
FqM_suppl(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN d;
  long r;

  if (!T) return FpM_suppl(x,p);
  init_suppl(x);
  d = FqM_gauss_pivot(x,T,p,&r);
  avma = av; return get_suppl(x,d,r);
}

GEN
image2(GEN x)
{
  pari_sp av = avma;
  long k, n, i;
  GEN A, B;

  if (typ(x)!=t_MAT) pari_err_TYPE("image2",x);
  if (lg(x) == 1) return cgetg(1,t_MAT);
  A = ker(x); k = lg(A)-1;
  if (!k) { avma = av; return gcopy(x); }
  A = suppl(A); n = lg(A)-1;
  B = cgetg(n-k+1, t_MAT);
  for (i = k+1; i <= n; i++) gel(B,i-k) = RgM_RgC_mul(x, gel(A,i));
  return gerepileupto(av, B);
}

GEN
matimage0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return image(x);
    case 1: return image2(x);
    default: pari_err_FLAG("matimage");
  }
  return NULL; /* not reached */
}

long
rank(GEN x)
{
  pari_sp av = avma;
  long r;
  GEN p = NULL;

  if (typ(x)!=t_MAT) pari_err_TYPE("rank",x);
  if (RgM_is_FpM(x, &p) && p)
  {
    r = FpM_rank(RgM_to_FpM(x, p), p);
    avma = av; return r;
  }
  (void)gauss_pivot(x, &r);
  avma = av; return lg(x)-1 - r;
}

GEN
F2m_indexrank(GEN x)
{
  long i,j,r;
  GEN res,d,p1,p2;
  pari_sp av = avma;
  long n = lg(x)-1;
  (void)new_chunk(3+n+1+n+1);
  /* yield r = dim ker(x) */
  d = F2m_gauss_pivot(F2m_copy(x),&r);
  avma = av;
  /* now r = dim Im(x) */
  r = n - r;

  res=cgetg(3,t_VEC);
  p1 = cgetg(r+1,t_VECSMALL); gel(res,1) = p1;
  p2 = cgetg(r+1,t_VECSMALL); gel(res,2) = p2;
  if (d)
  {
    for (i=0,j=1; j<=n; j++)
      if (d[j]) { i++; p1[i] = d[j]; p2[i] = j; }
    vecsmall_sort(p1);
  }
  return res;
}

GEN
Flm_indexrank(GEN x, ulong p)
{
  long i,j,r;
  GEN res,d,p1,p2;
  pari_sp av = avma;
  long n = lg(x)-1;
  (void)new_chunk(3+n+1+n+1);
  /* yield r = dim ker(x) */
  d = Flm_gauss_pivot(Flm_copy(x),p,&r);
  avma = av;
  /* now r = dim Im(x) */
  r = n - r;

  res=cgetg(3,t_VEC);
  p1 = cgetg(r+1,t_VECSMALL); gel(res,1) = p1;
  p2 = cgetg(r+1,t_VECSMALL); gel(res,2) = p2;
  if (d)
  {
    for (i=0,j=1; j<=n; j++)
      if (d[j]) { i++; p1[i] = d[j]; p2[i] = j; }
    vecsmall_sort(p1);
  }
  return res;
}

/* d a t_VECSMALL of integers in 1..n. Return the vector of the d[i]
 * followed by the missing indices */
static GEN
perm_complete(GEN d, long n)
{
  GEN y = cgetg(n+1, t_VECSMALL);
  long i, j = 1, k = n, l = lg(d);
  pari_sp av = avma;
  char *T = stack_calloc(n+1);
  for (i = 1; i < l; i++) T[d[i]] = 1;
  for (i = 1; i <= n; i++)
    if (T[i]) y[j++] = i; else y[k--] = i;
  avma = av; return y;
}

/* n = dim x, r = dim Ker(x), d from gauss_pivot */
static GEN
indexrank0(long n, long r, GEN d)
{
  GEN p1, p2, res = cgetg(3,t_VEC);
  long i, j;

  r = n - r; /* now r = dim Im(x) */
  p1 = cgetg(r+1,t_VECSMALL); gel(res,1) = p1;
  p2 = cgetg(r+1,t_VECSMALL); gel(res,2) = p2;
  if (d)
  {
    for (i=0,j=1; j<=n; j++)
      if (d[j]) { i++; p1[i] = d[j]; p2[i] = j; }
    vecsmall_sort(p1);
  }
  return res;
}
/* x an m x n t_MAT, n > 0, r = dim Ker(x), d from gauss_pivot */
static void
indexrank_all(long m, long n, long r, GEN d, GEN *prow, GEN *pcol)
{
  GEN IR = indexrank0(n, r, d);
  *prow = perm_complete(gel(IR,1), m);
  *pcol = perm_complete(gel(IR,2), n);
}
static void
init_indexrank(GEN x) {
  (void)new_chunk(3 + 2*lg(x)); /* HACK */
}

GEN
indexrank(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d, p = NULL;
  if (typ(x)!=t_MAT) pari_err_TYPE("indexrank",x);
  if (RgM_is_FpM(x, &p) && p)
    return gerepileupto(av, FpM_indexrank(RgM_to_FpM(x, p), p));
  init_indexrank(x);
  d = gauss_pivot(x,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
FpM_indexrank(GEN x, GEN p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = FpM_gauss_pivot(x,p,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

/*******************************************************************/
/*                                                                 */
/*                    LINEAR ALGEBRA MODULO P                      */
/*                                                                 */
/*******************************************************************/

static long
F2v_find_nonzero(GEN x0, GEN mask0, long l, long m)
{
  ulong *x = (ulong *)x0+2, *mask = (ulong *)mask0+2, e;
  long i, j;
  for (i = 0; i < l; i++)
  {
    e = *x++ & *mask++;
    if (e)
      for (j = 1; ; j++, e >>= 1) if (e & 1uL) return i*BITS_IN_LONG+j;
  }
  return m+1;
}

/* in place, destroy x */
GEN
F2m_ker_sp(GEN x, long deplin)
{
  GEN y, c, d;
  long i, j, k, l, r, m, n;

  n = lg(x)-1;
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = zero_F2v(m);
  l = lg(c)-1;
  for (i = 2; i <= l; i++) c[i] = -1;
  if (remsBIL(m)) c[l] = (1uL<<remsBIL(m))-1uL;
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, l, m);
    if (j>m)
    {
      if (deplin) {
        GEN c = zero_F2v(n);
        for (i=1; i<k; i++)
          if (F2v_coeff(xk, d[i]))
            F2v_set(c, i);
        F2v_set(c, k);
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      F2v_clear(c,j); d[k] = j;
      F2v_clear(xk, j);
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
      F2v_set(xk, j);
    }
  }
  if (deplin) return NULL;

  y = zero_F2m_copy(n,r);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = gel(y,j); while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i] && F2m_coeff(x,d[i],k))
        F2v_set(C,i);
    F2v_set(C, k);
  }
  return y;
}

/* in place, destroy x */
GEN
Flm_ker_sp(GEN x, ulong p, long deplin)
{
  GEN y, c, d;
  long i, j, k, r, t, m, n;
  ulong a;
  const int OK_ulong = SMALL_ULONG(p);

  n = lg(x)-1;
  m=lg(x[1])-1; r=0;

  c = const_vecsmall(m, 0);
  d = new_chunk(n+1);
  a = 0; /* for gcc -Wall */
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        a = ucoeff(x,j,k) % p;
        if (a) break;
      }
    if (j > m)
    {
      if (deplin) {
        c = cgetg(n+1, t_VECSMALL);
        for (i=1; i<k; i++) c[i] = ucoeff(x,d[i],k) % p;
        c[k] = 1; for (i=k+1; i<=n; i++) c[i] = 0;
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      ulong piv = p - Fl_inv(a, p); /* -1/a */
      c[j] = k; d[k] = j;
      ucoeff(x,j,k) = p-1;
      if (piv == 1) { /* nothing */ }
      else if (OK_ulong)
        for (i=k+1; i<=n; i++) ucoeff(x,j,i) = (piv * ucoeff(x,j,i)) % p;
      else
        for (i=k+1; i<=n; i++) ucoeff(x,j,i) = Fl_mul(piv, ucoeff(x,j,i), p);
      for (t=1; t<=m; t++)
      {
        if (t == j) continue;

        piv = ( ucoeff(x,t,k) %= p );
        if (!piv) continue;

        if (OK_ulong)
        {
          if (piv == 1)
            for (i=k+1; i<=n; i++) _Fl_add_OK((uGEN)x[i],t,j, p);
          else
            for (i=k+1; i<=n; i++) _Fl_addmul_OK((uGEN)x[i],t,j,piv, p);
        } else {
          if (piv == 1)
            for (i=k+1; i<=n; i++) _Fl_add((uGEN)x[i],t,j,p);
          else
            for (i=k+1; i<=n; i++) _Fl_addmul((uGEN)x[i],t,j,piv,p);
        }
      }
    }
  }
  if (deplin) return NULL;

  y = cgetg(r+1, t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1, t_VECSMALL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
        C[i] = ucoeff(x,d[i],k) % p;
      else
        C[i] = 0;
    C[k] = 1; for (i=k+1; i<=n; i++) C[i] = 0;
  }
  return y;
}

/* assume x has integer entries */
static GEN
FpM_ker_i(GEN x, GEN p, long deplin)
{
  pari_sp av0 = avma, av, lim, tetpil;
  GEN y, c, d;
  long i, j, k, r, t, n, m;

  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    if (pp==2)
    {
      y = ZM_to_F2m(x);
      y = F2m_ker_sp(y, deplin);
      if (!y) return y;
      y = deplin? F2c_to_ZC(y): F2m_to_ZM(y);
      return gerepileupto(av0, y);
    } else {
      y = ZM_to_Flm(x, pp);
      y = Flm_ker_sp(y, pp, deplin);
      if (!y) return y;
      y = deplin? Flc_to_ZC(y): Flm_to_ZM(y);
      return gerepileupto(av0, y);
    }
  }
  m=lg(x[1])-1; r=0;
  x = RgM_shallowcopy(x);
  c = const_vecsmall(m, 0);
  d=new_chunk(n+1);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = modii(gcoeff(x,j,k), p);
        if (signe(gcoeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (deplin) {
        c = cgetg(n+1, t_COL);
        for (i=1; i<k; i++) gel(c,i) = modii(gcoeff(x,d[i],k), p);
        gel(c,k) = gen_1; for (i=k+1; i<=n; i++) gel(c,i) = gen_0;
        return gerepileupto(av0, c);
      }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    {
      GEN piv = Fp_inv(gcoeff(x,j,k), p);
      togglesign(piv);
      c[j] = k; d[k] = j;
      gcoeff(x,j,k) = gen_m1;
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = Fp_mul(piv,gcoeff(x,j,i), p);
      for (t=1; t<=m; t++)
      {
        if (t==j) continue;

        piv = modii(gcoeff(x,t,k), p);
        if (!signe(piv)) continue;

        gcoeff(x,t,k) = gen_0;
        for (i=k+1; i<=n; i++) gcoeff(x,t,i) = addii(gcoeff(x,t,i), mulii(piv,gcoeff(x,j,i)));
        if (low_stack(lim, stack_lim(av,1)))
          gerepile_gauss_FpM_ker(x,p,k,t,av);
      }
    }
  }
  if (deplin) { avma = av0; return NULL; }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1,t_COL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(C,i) = modii(p1, p); gunclone(p1);
      }
      else
        gel(C,i) = gen_0;
    gel(C,k) = gen_1; for (i=k+1; i<=n; i++) gel(C,i) = gen_0;
  }
  return gerepile(av0,tetpil,y);
}

GEN
FpM_intersect(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  long j, lx = lg(x);
  GEN z;

  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);
  z = FpM_ker(shallowconcat(x,y), p);
  for (j=lg(z)-1; j; j--) setlg(z[j],lx);
  return gerepileupto(av, FpM_mul(x,z,p));
}

GEN
FpM_ker(GEN x, GEN p) { return FpM_ker_i(x, p, 0); }
GEN
FpM_deplin(GEN x, GEN p) { return FpM_ker_i(x, p, 1); }
/* not memory clean */
GEN
F2m_ker(GEN x) { return F2m_ker_sp(F2m_copy(x), 0); }
GEN
F2m_deplin(GEN x) { return F2m_ker_sp(F2m_copy(x), 1); }
GEN
Flm_ker(GEN x, ulong p) { return Flm_ker_sp(Flm_copy(x), p, 0); }
GEN
Flm_deplin(GEN x, ulong p) { return Flm_ker_sp(Flm_copy(x), p, 1); }

ulong
F2m_det_sp(GEN x) { return !F2m_ker_sp(x, 1); }

ulong
F2m_det(GEN x)
{
  pari_sp av = avma;
  ulong d = F2m_det_sp(F2m_copy(x));
  avma = av; return d;
}

/* in place, destroy a, SMALL_ULONG(p) is TRUE */
static ulong
Flm_det_sp_OK(GEN a, long nbco, ulong p)
{
  long i,j,k, s = 1;
  ulong q, x = 1;

  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
    {
      ulong c = ucoeff(a,k,i) % p;
      ucoeff(a,k,i) = c;
      if (c) break;
    }
    for(j=k+1; j<=nbco; j++) ucoeff(a,j,i) %= p;
    if (k > nbco) return ucoeff(a,i,i);
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) lswap(ucoeff(a,i,j), ucoeff(a,k,j));
      s = -s;
    }
    q = ucoeff(a,i,i);

    if (x & HIGHMASK) x %= p;
    x *= q;
    q = Fl_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      ulong m = ucoeff(a,i,k) % p;
      if (!m) continue;

      m = p - ((m*q)%p);
      for (j=i+1; j<=nbco; j++)
      {
        ulong c = ucoeff(a,j,k);
        if (c & HIGHMASK) c %= p;
        ucoeff(a,j,k) = c  + m*ucoeff(a,j,i);
      }
    }
  }
  if (x & HIGHMASK) x %= p;
  q = ucoeff(a,nbco,nbco);
  if (q & HIGHMASK) q %= p;
  x = (x*q) % p;
  if (s < 0 && x) x = p - x;
  return x;
}
/* in place, destroy a */
ulong
Flm_det_sp(GEN a, ulong p)
{
  long i,j,k, s = 1, nbco = lg(a)-1;
  ulong q, x = 1;

  if (SMALL_ULONG(p)) return Flm_det_sp_OK(a, nbco, p);
  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
      if (ucoeff(a,k,i)) break;
    if (k > nbco) return ucoeff(a,i,i);
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) lswap(ucoeff(a,i,j), ucoeff(a,k,j));
      s = -s;
    }
    q = ucoeff(a,i,i);

    x = Fl_mul(x,q,p);
    q = Fl_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      ulong m = ucoeff(a,i,k);
      if (!m) continue;

      m = Fl_mul(m, q, p);
      for (j=i+1; j<=nbco; j++)
        ucoeff(a,j,k) = Fl_sub(ucoeff(a,j,k), Fl_mul(m,ucoeff(a,j,i), p), p);
    }
  }
  if (s < 0) x = Fl_neg(x, p);
  return Fl_mul(x, ucoeff(a,nbco,nbco), p);
}

ulong
Flm_det(GEN x, ulong p)
{
  pari_sp av = avma;
  ulong d = Flm_det_sp(Flm_copy(x), p);
  avma = av; return d;
}

GEN
FpM_det(GEN a, GEN p)
{
  pari_sp av = avma, lim = stack_lim(av,1);
  long i,j,k, s = 1, nbco = lg(a)-1;
  GEN q, x = gen_1;
  if (lgefint(p) == 3)
  {
    ulong d, pp = (ulong)p[2];
    if (pp==2)
      d = F2m_det_sp(ZM_to_F2m(a));
    else
      d = Flm_det_sp(ZM_to_Flm(a, pp), pp);
    avma = av;
    return utoi(d);
  }

  a = RgM_shallowcopy(a);
  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
    {
      gcoeff(a,k,i) = modii(gcoeff(a,k,i), p);
      if (signe(gcoeff(a,k,i))) break;
    }
    if (k > nbco) return gerepileuptoint(av, gcoeff(a,i,i));
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      s = -s;
    }
    q = gcoeff(a,i,i);

    x = Fp_mul(x,q,p);
    q = Fp_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = modii(gcoeff(a,i,k), p);
      if (!signe(m)) continue;

      m = Fp_mul(m, q, p);
      for (j=i+1; j<=nbco; j++)
      {
        gcoeff(a,j,k) = Fp_sub(gcoeff(a,j,k), Fp_mul(m,gcoeff(a,j,i),p),p);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
          gerepileall(av,4, &a,&x,&q,&m);
        }
      }
    }
  }
  if (s < 0) x = gneg_i(x);
  return gerepileuptoint(av, Fp_mul(x, gcoeff(a,nbco,nbco),p));
}

/* Destroy x */
static GEN
F2m_gauss_pivot(GEN x, long *rr)
{
  GEN c, d;
  long i, j, k, l, r, m, n;

  n = lg(x)-1; if (!n) { *rr=0; return NULL; }
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = zero_F2v(m);
  l = lg(c)-1;
  for (i = 2; i <= l; i++) c[i] = -1;
  if (remsBIL(m)) c[l] = (1uL<<remsBIL(m))-1uL;
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, l, m);
    if (j>m) { r++; d[k] = 0; }
    else
    {
      F2v_clear(c,j); d[k] = j;
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
    }
  }

  *rr = r; avma = (pari_sp)d; return d;
}

/* Destroy x */
static GEN
Flm_gauss_pivot(GEN x, ulong p, long *rr)
{
  GEN c,d;
  long i,j,k,r,t,n,m;

  n=lg(x)-1; if (!n) { *rr=0; return NULL; }

  m=lg(x[1])-1; r=0;
  d=cgetg(n+1,t_VECSMALL);
  c = const_vecsmall(m, 0);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        ucoeff(x,j,k) %= p;
        if (ucoeff(x,j,k)) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      ulong piv = p - Fl_inv(ucoeff(x,j,k), p);
      c[j]=k; d[k]=j;
      for (i=k+1; i<=n; i++)
        ucoeff(x,j,i) = Fl_mul(piv, ucoeff(x,j,i), p);
      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          piv = ucoeff(x,t,k);
          if (piv)
          {
            ucoeff(x,t,k) = 0;
            for (i=k+1; i<=n; i++)
              ucoeff(x,t,i) = Fl_add(ucoeff(x,t,i),
                                     Fl_mul(piv,ucoeff(x,j,i),p),p);
          }
        }
      for (i=k; i<=n; i++) ucoeff(x,j,i) = 0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

static GEN
FpM_gauss_pivot(GEN x, GEN p, long *rr)
{
  pari_sp av, lim;
  GEN c, d;
  long i, j, k, r, t, m, n = lg(x)-1;

  if (!n) { *rr = 0; return NULL; }
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    if (pp == 2)
      return F2m_gauss_pivot(ZM_to_F2m(x), rr);
    else
      return Flm_gauss_pivot(ZM_to_Flm(x, pp), pp, rr);
  }

  m=lg(x[1])-1; r=0;
  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x);
  c = const_vecsmall(m, 0);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = modii(gcoeff(x,j,k), p);
        if (signe(gcoeff(x,j,k))) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      GEN piv = Fp_inv(gcoeff(x,j,k), p);
      togglesign(piv);
      c[j] = k; d[k] = j;
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = Fp_mul(piv,gcoeff(x,j,i), p);
      for (t=1; t<=m; t++)
      {
        if (c[t]) continue; /* already a pivot on that line */

        piv = modii(gcoeff(x,t,k), p);
        if (!signe(piv)) continue;

        gcoeff(x,t,k) = gen_0;
        for (i=k+1; i<=n; i++)
          gcoeff(x,t,i) = addii(gcoeff(x,t,i), mulii(piv,gcoeff(x,j,i)));
        if (low_stack(lim, stack_lim(av,1)))
          gerepile_gauss(x,k,t,av,j,c);
      }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = gen_0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}
static GEN
FqM_gauss_pivot(GEN x, GEN T, GEN p, long *rr)
{
  pari_sp av, lim;
  GEN c, d;
  long i, j, k, r, t, n, m;

  n=lg(x)-1; if (!n) { *rr=0; return NULL; }
  m=lg(x[1])-1; r=0;
  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x);
  c = const_vecsmall(m, 0);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = Fq_red(gcoeff(x,j,k), T,p);
        if (signe(gcoeff(x,j,k))) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      GEN piv = gneg(Fq_inv(gcoeff(x,j,k), T,p));
      c[j]=k; d[k]=j;
      for (i=k+1; i<=n; i++)
        gcoeff(x,j,i) = Fq_mul(piv,gcoeff(x,j,i), T, p);
      for (t=1; t<=m; t++)
      {
        if (c[t]) continue; /* already a pivot on that line */

        piv = Fq_red(gcoeff(x,t,k), T,p);
        if (!signe(piv)) continue;

        gcoeff(x,t,k) = gen_0;
        for (i=k+1; i<=n; i++)
          gcoeff(x,t,i) = gadd(gcoeff(x,t,i), gmul(piv,gcoeff(x,j,i)));
        if (low_stack(lim, stack_lim(av,1)))
          gerepile_gauss(x,k,t,av,j,c);
      }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = gen_0; /* dummy */
    }
  }
  *rr=r; return d;
}

GEN
FpM_image(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN d, y;
  long j, k, r;

  d = FpM_gauss_pivot(x,p,&r);
  if (!d) { avma = av; return ZM_copy(x); }
  /* d left on stack for efficiency */
  r = lg(x)-1 - r; /* = dim Im(x) */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = ZC_copy(gel(x,k));
  return y;
}

long
FpM_rank(GEN x, GEN p)
{
  pari_sp av = avma;
  long r;
  (void)FpM_gauss_pivot(x,p,&r);
  avma = av; return lg(x)-1 - r;
}

GEN
F2m_image(GEN x)
{
  pari_sp av = avma;
  GEN d,y;
  long j,k,r;

  d = F2m_gauss_pivot(F2m_copy(x),&r);
  if (!d) { avma = av; return F2m_copy(x); }
  /* d left on stack */
  r = lg(x)-1 - r; /* = dim Im(x) */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = F2v_copy(gel(x,k));
  return y;
}

GEN
Flm_image(GEN x, ulong p)
{
  pari_sp av = avma;
  GEN d,y;
  long j,k,r;

  d = Flm_gauss_pivot(Flm_copy(x),p,&r);
  if (!d) { avma = av; return Flm_copy(x); }
  /* d left on stack */
  r = lg(x)-1 - r; /* = dim Im(x) */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = Flv_copy(gel(x,k));
  return y;
}

long
F2m_rank(GEN x)
{
  pari_sp av = avma;
  long r;
  (void)F2m_gauss_pivot(F2m_copy(x),&r);
  avma = av; return lg(x)-1 - r;
}

long
Flm_rank(GEN x, ulong p)
{
  pari_sp av = avma;
  long r;
  (void)Flm_gauss_pivot(Flm_copy(x),p,&r);
  avma = av; return lg(x)-1 - r;
}

static GEN
sFpM_invimage(GEN mat, GEN y, GEN p)
{
  pari_sp av = avma;
  long i, l = lg(mat);
  GEN M = cgetg(l+1,t_MAT), col, t;

  if (l==1) return NULL;
  if (lg(y) != lg(mat[1])) pari_err_DIM("FpM_invimage");

  for (i=1; i<l; i++) gel(M,i) = gel(mat,i);
  gel(M,l) = y; M = FpM_ker(M,p);
  i = lg(M)-1; if (!i) return NULL;

  col = gel(M,i); t = gel(col,l);
  if (!signe(t)) return NULL;

  t = Fp_inv(negi(t),p);
  setlg(col,l);
  if (is_pm1(t)) return gerepilecopy(av, col);
  return gerepileupto(av, FpC_Fp_mul(col, t, p));
}

/* inverse image of v by m */
GEN
FpM_invimage(GEN m, GEN v, GEN p)
{
  pari_sp av = avma;
  long j, l;
  GEN y, c;

  if (typ(v) == t_COL)
  {
    c = sFpM_invimage(m,v,p);
    if (c) return c;
    avma = av; return cgetg(1,t_MAT);
  }
  /* t_MAT */
  y = cgetg_copy(v, &l);
  for (j=1; j < l; j++)
  {
    c = sFpM_invimage(m,gel(v,j),p);
    if (!c) { avma = av; return cgetg(1,t_MAT); }
    gel(y,j) = c;
  }
  return y;
}
/**************************************************************
 Rather stupid implementation of linear algebra in finite fields
 **************************************************************/

static void
Fq_gerepile_gauss_ker(GEN x, GEN T, GEN p, long k, long t, pari_sp av)
{
  pari_sp tetpil = avma;
  long u,i, n = lg(x)-1, m = n? lg(x[1])-1: 0;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot_ker. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (isonstack(gcoeff(x,u,k))) gcoeff(x,u,k) = Fq_red(gcoeff(x,u,k),T,p);
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
      if (isonstack(gcoeff(x,u,i))) gcoeff(x,u,i) = Fq_red(gcoeff(x,u,i),T,p);
  gerepile_mat(av,tetpil,x,k,m,n,t);
}

static void
Flxq_gerepile_gauss_ker(GEN x, GEN T, ulong p, long k, long t, pari_sp av)
{
  pari_sp tetpil = avma;
  long u,i, n = lg(x)-1, m = n? lg(x[1])-1: 0;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot_ker. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (isonstack(gcoeff(x,u,k))) gcoeff(x,u,k) = Flx_rem(gcoeff(x,u,k),T,p);
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
      if (isonstack(gcoeff(x,u,i))) gcoeff(x,u,i) = Flx_rem(gcoeff(x,u,i),T,p);
  gerepile_mat(av,tetpil,x,k,m,n,t);
}

static GEN
FqM_ker_i(GEN x, GEN T, GEN p, long deplin)
{
  pari_sp av0, av, lim, tetpil;
  GEN y, c, d;
  long i, j, k, r, t, n, m;

  if (!T) return FpM_ker_i(x,p,deplin);
  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);

  if (lgefint(p)==3)
  {
    pari_sp ltop=avma;
    ulong l= p[2];
    GEN Ml = FqM_to_FlxM(x, T, p);
    GEN Tl = ZX_to_Flx(T,l);
    GEN p1 = FlxM_to_ZXM(FlxqM_ker(Ml,Tl,l));
    return gerepileupto(ltop,p1);
  }
  m=lg(x[1])-1; r=0; av0 = avma;
  x = RgM_shallowcopy(x);
  c = const_vecsmall(m, 0);
  d=new_chunk(n+1);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = Fq_red(gcoeff(x,j,k), T, p);
        if (signe(gcoeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (deplin) {
        c = cgetg(n+1, t_COL);
        for (i=1; i<k; i++) gel(c,i) = Fq_red(gcoeff(x,d[i],k), T, p);
        gel(c,k) = gen_1; for (i=k+1; i<=n; i++) gel(c,i) = gen_0;
        return gerepileupto(av0, c);
      }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    {
      GEN piv = Fq_neg_inv(gcoeff(x,j,k), T, p);
      c[j] = k; d[k] = j;
      gcoeff(x,j,k) = gen_m1;
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = Fq_mul(piv,gcoeff(x,j,i), T, p);
      for (t=1; t<=m; t++)
      {
        if (t==j) continue;

        piv = Fq_red(gcoeff(x,t,k), T, p);
        /*Assume signe work for both t_POL and t_INT*/
        if (!signe(piv)) continue;

        gcoeff(x,t,k) = gen_0;
        for (i=k+1; i<=n; i++)
          gcoeff(x,t,i) = Fq_add(gcoeff(x,t,i), Fq_mul(piv,gcoeff(x,j,i), T, p), T, p);
        if (low_stack(lim, stack_lim(av,1)))
          Fq_gerepile_gauss_ker(x,T,p,k,t,av);
      }
    }
  }
  if (deplin) { avma = av0; return NULL; }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1,t_COL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(C,i) = Fq_red(p1, T, p); gunclone(p1);
      }
      else
        gel(C,i) = gen_0;
    gel(C,k) = gen_1; for (i=k+1; i<=n; i++) gel(C,i) = gen_0;
  }
  return gerepile(av0,tetpil,y);
}

GEN
FqM_ker(GEN x, GEN T, GEN p)
{
  return FqM_ker_i(x, T, p, 0);
}

static GEN
FlxqM_ker_i(GEN x, GEN T, ulong p, long deplin)
{
  pari_sp av0,av,lim,tetpil;
  GEN y, c, d, mun;
  long i, j, k, r, t, n, m;
  long vs;

  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  vs = mael3(x,1,1,1);

  m=lg(x[1])-1; r=0; av0 = avma;
  x = RgM_shallowcopy(x); mun=Fl_to_Flx(p-1,vs);
  c = const_vecsmall(m, 0);
  d=new_chunk(n+1);
  av=avma; lim=stack_lim(av,1);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = Flx_rem(gcoeff(x,j,k), T, p);
        if (lgpol(gcoeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (deplin) {
        c = cgetg(n+1, t_COL);
        for (i=1; i<k; i++) gel(c,i) = Flx_rem(gcoeff(x,d[i],k), T, p);
        gel(c,k) = pol1_Flx(vs);
        for (i=k+1; i<=n; i++) gel(c,i) = zero_Flx(vs);
        return gerepileupto(av0, c);
      }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    {
      GEN piv = Flx_neg(Flxq_inv(gcoeff(x,j,k), T, p), p);
      c[j] = k; d[k] = j;
      gcoeff(x,j,k) = mun;
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = Flxq_mul(piv,gcoeff(x,j,i), T, p);
      for (t=1; t<=m; t++)
      {
        if (t==j) continue;

        piv = Flx_rem(gcoeff(x,t,k), T, p);
        if (!lgpol(piv)) continue;

        gcoeff(x,t,k) = zero_Flx(vs);
        for (i=k+1; i<=n; i++)
          gcoeff(x,t,i) = Flx_add(gcoeff(x,t,i),
                                  Flxq_mul(piv,gcoeff(x,j,i), T, p), p);
        if (low_stack(lim, stack_lim(av,1)))
          Flxq_gerepile_gauss_ker(x,T,p,k,t,av);
      }
    }
  }
  if (deplin) { avma = av0; return NULL; }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1,t_COL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(C,i) = Flx_rem(p1, T, p); gunclone(p1);
      }
      else
        gel(C,i) = zero_Flx(vs);
    gel(C,k) = pol1_Flx(vs);
    for (i=k+1; i<=n; i++) gel(C,i) = zero_Flx(vs);
  }
  return gerepile(av0,tetpil,y);
}

GEN
FlxqM_ker(GEN x, GEN T, ulong p)
{
  return FlxqM_ker_i(x, T, p, 0);
}

/*******************************************************************/
/*                                                                 */
/*                   Structured Elimination                        */
/*                                                                 */
/*******************************************************************/

static void
rem_col(GEN c, long i, GEN iscol, GEN Wrow, long *rcol, long *rrow)
{
  long lc = lg(c), k;
  iscol[i] = 0; (*rcol)--;
  for (k = 1; k < lc; ++k)
  {
    Wrow[c[k]]--;
    if (Wrow[c[k]]==0) (*rrow)--;
  }
}

static void
rem_singleton(GEN M, GEN iscol, GEN Wrow, long *rcol, long *rrow)
{
  long i, j;
  long nbcol = lg(iscol)-1, last;
  do
  {
    last = 0;
    for (i = 1; i <= nbcol; ++i)
      if (iscol[i])
      {
        GEN c = gmael(M, i, 1);
        long lc = lg(c);
        for (j = 1; j < lc; ++j)
          if (Wrow[c[j]] == 1)
          {
            rem_col(c, i, iscol, Wrow, rcol, rrow);
            last=1; break;
          }
      }
  } while (last);
}

static GEN
fill_wcol(GEN M, GEN iscol, GEN Wrow, long *w, GEN wcol)
{
  long nbcol = lg(iscol)-1;
  long i, j, m, last;
  GEN per;
  for (m = 2, last=0; !last ; m++)
  {
    for (i = 1; i <= nbcol; ++i)
    {
      wcol[i] = 0;
      if (iscol[i])
      {
        GEN c = gmael(M, i, 1);
        long lc = lg(c);
        for (j = 1; j < lc; ++j)
          if (Wrow[c[j]] == m) {  wcol[i]++; last = 1; }
      }
    }
  }
  per = vecsmall_indexsort(wcol);
  *w = wcol[per[nbcol]];
  return per;
}

/* M is a RgMs with nbrow rows, A a list of row indices.
   Eliminate rows of M with a single entry that do not belong to A,
   and the corresponding columns. Also eliminate columns until #colums=#rows.
   Return pcol and prow:
   pcol is a map from the new columns indices to the old one.
   prow is a map from the old rows indices to the new one (0 if removed).
*/

void
RgMs_structelim(GEN M, long nbrow, GEN A, GEN *p_col, GEN *p_row)
{
  long i,j,k;
  long nbcol = lg(M)-1, lA = lg(A);
  GEN prow = cgetg(nbrow+1, t_VECSMALL);
  GEN pcol = const_vecsmall(nbcol, 0);
  pari_sp av = avma;
  long rcol = nbcol, rrow = 0, imin = nbcol - usqrtsafe(nbcol);
  GEN iscol = const_vecsmall(nbcol, 1);
  GEN Wrow  = const_vecsmall(nbrow, 0);
  GEN wcol = cgetg(nbcol+1, t_VECSMALL);
  pari_sp av2=avma;
  for (i = 1; i <= nbcol; ++i)
  {
    GEN F = gmael(M, i, 1);
    long l = lg(F)-1;
    for (j = 1; j <= l; ++j)
      Wrow[F[j]]++;
  }
  for (j = 1; j < lA; ++j)
    Wrow[A[j]] = -1;
  for (i = 1; i <= nbrow; ++i)
    if (Wrow[i])
      rrow++;
  rem_singleton(M, iscol, Wrow, &rcol, &rrow);
  for (; rcol>rrow;)
  {
    long w;
    GEN per = fill_wcol(M, iscol, Wrow, &w, wcol);
    for (i = nbcol; i>=imin && wcol[per[i]]>=w && rcol>rrow; i--)
      rem_col(gmael(M, per[i], 1), per[i], iscol, Wrow, &rcol, &rrow);
    rem_singleton(M, iscol, Wrow, &rcol, &rrow);
    avma = av2;
  }
  for (j = 1, i = 1; i <= nbcol; ++i)
    if (iscol[i])
      pcol[j++] = i;
  setlg(pcol,j);
  for (k = 1, i = 1; i <= nbrow; ++i)
    prow[i] = Wrow[i] ? k++: 0;
  avma = av;
  *p_col = pcol; *p_row = prow;
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
  GEN y,rr,p,ssesp,r1,r2,r3;
  long e,i,k,l,ly,ex, n = lg(x);
  pari_sp av = avma;

  if (typ(x)!=t_MAT) pari_err_TYPE("eigen",x);
  if (n != 1 && n != lg(x[1])) pari_err_DIM("eigen");
  if (n<=2) return gcopy(x);

  ex = 16 - prec2nbits(prec);
  y=cgetg(n,t_MAT);
  p=caradj(x,0,NULL); rr = cleanroots(p,prec);
  ly=1; k=2; r2=gel(rr,1);
  for(;;)
  {
    r3 = grndtoi(r2, &e); if (e < ex) r2 = r3;
    ssesp = ker_aux(RgM_Rg_add_shallow(x, gneg(r2))); l = lg(ssesp);
    if (l == 1 || ly + (l-1) > n)
      pari_err_PREC("mateigen");
    for (i=1; i<l; i++,ly++) gel(y,ly) = gel(ssesp,i); /* eigenspace done */

    r1=r2; /* try to find a different eigenvalue */
    do
    {
      if (k == n || ly == n)
      {
        setlg(y,ly); /* x may not be diagonalizable */
        return gerepilecopy(av,y);
      }
      r2 = gel(rr,k++);
      r3 = gsub(r1,r2);
    }
    while (gequal0(r3) || gexpo(r3) < ex);
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
    default: pari_err_FLAG("matdet");
  }
  return NULL; /* not reached */
}

static GEN
det_simple_gauss(GEN a, GEN data, pivot_fun pivot)
{
  pari_sp av = avma, lim = stack_lim(av,1);
  long i,j,k, s = 1, nbco = lg(a)-1;
  GEN p, x = gen_1;

  a = RgM_shallowcopy(a);
  for (i=1; i<nbco; i++)
  {
    k = pivot(a, data, i, NULL);
    if (k > nbco) return gerepilecopy(av, gcoeff(a,i,i));
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      s = -s;
    }
    p = gcoeff(a,i,i);

    x = gmul(x,p);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = gcoeff(a,i,k);
      if (gequal0(m)) continue;

      m = gdiv(m,p);
      for (j=i+1; j<=nbco; j++)
      {
        gcoeff(a,j,k) = gsub(gcoeff(a,j,k), gmul(m,gcoeff(a,j,i)));
        if (low_stack(lim, stack_lim(av,1)))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
          gerepileall(av,2, &a,&x);
          p = gcoeff(a,i,i);
          m = gcoeff(a,i,k); m = gdiv(m, p);
        }
      }
    }
  }
  if (s < 0) x = gneg_i(x);
  return gerepileupto(av, gmul(x, gcoeff(a,nbco,nbco)));
}

GEN
det2(GEN a)
{
  GEN data;
  pivot_fun pivot;
  long nbco = lg(a)-1;
  if (typ(a)!=t_MAT) pari_err_TYPE("det2",a);
  if (!nbco) return gen_1;
  if (nbco != lg(a[1])-1) pari_err_DIM("det2");
  pivot = get_pivot_fun(a, &data);
  return det_simple_gauss(a, data, pivot);
}

static GEN
mydiv(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx == ty && tx == t_POL && varn(x) == varn(y)) return RgX_div(x,y);
  return gdiv(x,y);
}

/* Assumes a a square t_MAT of dimension n > 0. Returns det(a) using
 * Gauss-Bareiss. */
static GEN
det_bareiss(GEN a)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  long nbco = lg(a)-1,i,j,k,s = 1;
  GEN p, pprec;

  a = RgM_shallowcopy(a);
  for (pprec=gen_1,i=1; i<nbco; i++,pprec=p)
  {
    GEN ci, ck, m;
    int diveuc = (gequal1(pprec)==0);

    p = gcoeff(a,i,i);
    if (gequal0(p))
    {
      k=i+1; while (k<=nbco && gequal0(gcoeff(a,i,k))) k++;
      if (k>nbco) return gerepilecopy(av, p);
      swap(gel(a,k), gel(a,i)); s = -s;
      p = gcoeff(a,i,i);
    }
    ci = gel(a,i);
    for (k=i+1; k<=nbco; k++)
    {
      ck = gel(a,k); m = gel(ck,i);
      if (gequal0(m))
      {
        if (gequal1(p))
        {
          if (diveuc)
            gel(a,k) = mydiv(gel(a,k), pprec);
        }
        else
          for (j=i+1; j<=nbco; j++)
          {
            GEN p1 = gmul(p, gel(ck,j));
            if (diveuc) p1 = mydiv(p1,pprec);
            gel(ck,j) = p1;
          }
      }
      else
      {
        for (j=i+1; j<=nbco; j++)
        {
          pari_sp av2 = avma;
          GEN p1 = gsub(gmul(p,gel(ck,j)), gmul(m,gel(ci,j)));
          if (diveuc) p1 = mydiv(p1,pprec);
          gel(ck,j) = gerepileupto(av2, p1);
          if (low_stack(lim,stack_lim(av,2)))
          {
            if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
            gerepileall(av,2, &a,&pprec);
            ci = gel(a,i);
            ck = gel(a,k); m = gel(ck,i);
            p = gcoeff(a,i,i);
          }
        }
      }
    }
  }
  p = gcoeff(a,nbco,nbco);
  p = (s < 0)? gneg(p): gcopy(p);
  return gerepileupto(av, p);
}

/* count non-zero entries in col j, at most 'max' of them.
 * Return their indices */
static GEN
col_count_non_zero(GEN a, long j, long max)
{
  GEN v = cgetg(max+1, t_VECSMALL);
  GEN c = gel(a,j);
  long i, l = lg(a), k = 1;
  for (i = 1; i < l; i++)
    if (!gequal0(gel(c,i)))
    {
      if (k > max) return NULL; /* fail */
      v[k++] = i;
    }
  setlg(v, k); return v;
}
/* count non-zero entries in row i, at most 'max' of them.
 * Return their indices */
static GEN
row_count_non_zero(GEN a, long i, long max)
{
  GEN v = cgetg(max+1, t_VECSMALL);
  long j, l = lg(a), k = 1;
  for (j = 1; j < l; j++)
    if (!gequal0(gcoeff(a,i,j)))
    {
      if (k > max) return NULL; /* fail */
      v[k++] = j;
    }
  setlg(v, k); return v;
}

static GEN det_develop(GEN a, long max, double bound);
/* (-1)^(i+j) a[i,j] * det RgM_minor(a,i,j) */
static GEN
coeff_det(GEN a, long i, long j, long max, double bound)
{
  GEN c = gcoeff(a, i, j);
  c = gmul(c, det_develop(RgM_minor(a, i,j), max, bound));
  if (odd(i+j)) c = gneg(c);
  return c;
}
/* a square t_MAT, 'bound' a rough upper bound for the number of
 * multiplications we are willing to pay while developing rows/columns before
 * switching to Gaussian elimination */
static GEN
det_develop(GEN M, long max, double bound)
{
  pari_sp av = avma;
  long i,j, n = lg(M)-1, lbest = max+2, best_col = 0, best_row = 0;
  GEN best = NULL;

  if (bound < 1.) return det_bareiss(M); /* too costly now */

  switch(n)
  {
    case 0: return gen_1;
    case 1: return gcopy(gcoeff(M,1,1));
    case 2: {
      GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
      GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
      return gerepileupto(av, gsub(gmul(a,d), gmul(b,c)));
    }
  }
  if (max > ((n+2)>>1)) max = (n+2)>>1;
  for (j = 1; j <= n; j++)
  {
    pari_sp av2 = avma;
    GEN v = col_count_non_zero(M, j, max);
    long lv;
    if (!v || (lv = lg(v)) >= lbest) { avma = av2; continue; }
    if (lv == 1) { avma = av; return gen_0; }
    if (lv == 2) {
      avma = av;
      return gerepileupto(av, coeff_det(M,v[1],j,max,bound));
    }
    best = v; lbest = lv; best_col = j;
  }
  for (i = 1; i <= n; i++)
  {
    pari_sp av2 = avma;
    GEN v = row_count_non_zero(M, i, max);
    long lv;
    if (!v || (lv = lg(v)) >= lbest) { avma = av2; continue; }
    if (lv == 1) { avma = av; return gen_0; }
    if (lv == 2) {
      avma = av;
      return gerepileupto(av, coeff_det(M,i,v[1],max,bound));
    }
    best = v; lbest = lv; best_row = i;
  }
  if (best_row)
  {
    GEN s = NULL;
    long k;
    bound /= (lbest-1);
    for (k = 1; k < lbest; k++)
    {
      GEN c = coeff_det(M, best_row, best[k], max, bound);
      s = s? gadd(s, c): c;
    }
    return gerepileupto(av, s);
  }
  if (best_col)
  {
    GEN s = NULL;
    long k;
    bound /= (lbest-1);
    for (k = 1; k < lbest; k++)
    {
      GEN c = coeff_det(M, best[k], best_col, max, bound);
      s = s? gadd(s, c): c;
    }
    return gerepileupto(av, s);
  }
  return det_bareiss(M);
}

/* area of parallelogram bounded by (v1,v2) */
static GEN
parallelogramarea(GEN v1, GEN v2)
{ return gsub(gmul(gnorml2(v1), gnorml2(v2)), gsqr(RgV_dotproduct(v1, v2))); }

/* Square of Hadamard bound for det(a), a square matrix.
 * Slightly improvement: instead of using the column norms, use the area of
 * the parallelogram formed by pairs of consecutive vectors */
GEN
RgM_Hadamard(GEN a)
{
  pari_sp av = avma;
  long n = lg(a)-1, i;
  GEN B;
  if (n == 0) return gen_1;
  if (n == 1) return gsqr(gcoeff(a,1,1));
  a = RgM_gtofp(a, LOWDEFAULTPREC);
  B = gen_1;
  for (i = 1; i <= n/2; i++)
    B = gmul(B, parallelogramarea(gel(a,2*i-1), gel(a,2*i)));
  if (odd(n)) B = gmul(B, gnorml2(gel(a, n)));
  return gerepileuptoint(av, ceil_safe(B));
}

/* assume dim(a) = n > 1 */
static GEN
ZM_det_i(GEN a, long n)
{
  pari_sp av = avma, av2;
  long i;
  ulong p, compp, Dp = 1;
  byteptr d;
  GEN D, h, q, v, comp;
  if (n == 2) {
    D = subii(mulii(gcoeff(a,1,1), gcoeff(a,2,2)),
              mulii(gcoeff(a,2,1), gcoeff(a,1,2)));
    return gerepileuptoint(av, D);
  }
  h = RgM_Hadamard(a);
  if (!signe(h)) { avma = av; return gen_0; }
  h = sqrti(h);
  for (q = gen_1, d = init_modular(&p); cmpii(q, h) <= 0; )
  {
    av2 = avma;
    Dp = Flm_det(ZM_to_Flm(a, p), p);
    avma = av2;
    if (Dp) break;
    q = muliu(q, p);
    NEXT_PRIME_VIADIFF_CHECK(p,d);
  }
  if (!Dp) { avma = av; return gen_0; }
  av2 = avma;
  v = cgetg(n+1, t_COL);
  gel(v, 1) = gen_1; /* ensure content(v) = 1 */
  for (i = 2; i <= n; i++) gel(v, i) = stoi(random_Fl(15) - 7);
  D = Q_denom(ZM_gauss(a, v));
  if (expi(D) < expi(h) >> 1)
  { /* First try unlucky, try once more */
    for (i = 2; i <= n; i++) gel(v, i) = stoi(random_Fl(15) - 7);
    D = lcmii(D, Q_denom(ZM_gauss(a, v)));
  }
  D = gerepileuptoint(av2, D);
  if (q != gen_1) D = lcmii(D, q);
  /* determinant is a multiple of D */
  h = shifti(divii(h, D), 1);

  compp = Fl_div(Dp, umodiu(D,p), p);
  comp = Z_init_CRT(compp, p);
  q = utoipos(p);
  while (cmpii(q, h) <= 0)
  {
    GEN qp;
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    Dp = umodiu(D, p);
    if (!Dp) continue;
    av2 = avma;
    compp = Fl_div(Flm_det(ZM_to_Flm(a, p), p), Dp, p);
    avma = av2;
    qp = muliu(q, p);
    (void) Z_incremental_CRT(&comp, compp, q, qp, p);
    q = qp;
  }
  return gerepileuptoint(av, mulii(comp, D));
}

GEN
det(GEN a)
{
  long n = lg(a)-1;
  double B;
  GEN data, p=NULL;
  pivot_fun pivot;

  if (typ(a)!=t_MAT) pari_err_TYPE("det",a);
  if (!n) return gen_1;
  if (n != lg(a[1])-1) pari_err_DIM("det");
  if (n == 1) return gcopy(gcoeff(a,1,1));
  if (RgM_is_FpM(a, &p))
  {
    pari_sp av;
    if (!p) return ZM_det_i(a, n);
    av = avma;
    return gerepilecopy(av, Fp_to_mod(FpM_det(RgM_to_FpM(a, p), p), p));
  }
  pivot = get_pivot_fun(a, &data);
  if (pivot != gauss_get_pivot_NZ) return det_simple_gauss(a, data, pivot);
  B = (double)n; B = B*B; B = B*B;
  return det_develop(a, 7, B);
}

GEN
ZM_det(GEN a)
{
  long n = lg(a)-1;
  if (typ(a)!=t_MAT) pari_err_TYPE("ZM_det",a);
  if (!n) return gen_1;
  if (n != lg(a[1])-1) pari_err_DIM("ZM_det");
  RgM_check_ZM(a, "ZM_det");
  if (n == 1) return icopy(gcoeff(a,1,1));
  return ZM_det_i(a, n);
}

/* return a solution of congruence system sum M_{ i,j } X_j = Y_i mod D_i
 * If ptu1 != NULL, put in *ptu1 a Z-basis of the homogeneous system */
static GEN
gaussmoduloall(GEN M, GEN D, GEN Y, GEN *ptu1)
{
  pari_sp av = avma;
  long n, m, j, l, lM;
  GEN delta, H, U, u1, u2, x;

  if (typ(M)!=t_MAT) pari_err_TYPE("gaussmodulo",M);
  lM = lg(M);
  if (lM == 1)
  {
    switch(typ(Y))
    {
      case t_INT: break;
      case t_COL: if (lg(Y) != 1) pari_err_DIM("gaussmodulo");
      default: pari_err_TYPE("gaussmodulo",Y);
    }
    switch(typ(D))
    {
      case t_INT: break;
      case t_COL: if (lg(D) != 1) pari_err_DIM("gaussmodulo");
      default: pari_err_TYPE("gaussmodulo",D);
    }
    if (ptu1) *ptu1 = cgetg(1, t_MAT);
    return gen_0;
  }
  n = lg(M[1])-1;
  switch(typ(D))
  {
    case t_COL:
      if (lg(D)-1!=n) pari_err_DIM("gaussmodulo");
      delta = diagonal_shallow(D); break;
    case t_INT: delta = scalarmat_shallow(D,n); break;
    default: pari_err_TYPE("gaussmodulo",D);
      return NULL; /* not reached */
  }
  switch(typ(Y))
  {
    case t_INT: Y = const_col(n, Y); break;
    case t_COL:
      if (lg(Y)-1!=n) pari_err_DIM("gaussmodulo");
      break;
    default: pari_err_TYPE("gaussmodulo",Y);
      return NULL; /* not reached */
  }
  H = ZM_hnfall(shallowconcat(M,delta), &U, 1);
  Y = hnf_solve(H,Y); if (!Y) return gen_0;
  l = lg(H); /* may be smaller than lM if some moduli are 0 */
  n = l-1;
  m = lg(U)-1 - n;
  u1 = cgetg(m+1,t_MAT);
  u2 = cgetg(n+1,t_MAT);
  for (j=1; j<=m; j++) { GEN c = gel(U,j); setlg(c,lM); gel(u1,j) = c; }
  U += m;
  for (j=1; j<=n; j++) { GEN c = gel(U,j); setlg(c,lM); gel(u2,j) = c; }
  /*       (u1 u2)
   * (M D) (*  * ) = (0 H) */
  u1 = ZM_lll(u1, 0.75, LLL_INPLACE);
  Y = ZM_ZC_mul(u2,Y);
  x = ZC_reducemodmatrix(Y, u1);
  if (!ptu1) x = gerepileupto(av, x);
  else
  {
    gerepileall(av, 2, &x, &u1);
    *ptu1 = u1;
  }
  return x;
}

GEN
matsolvemod0(GEN M, GEN D, GEN Y, long flag)
{
  pari_sp av;
  GEN p1,y;

  if (!flag) return gaussmoduloall(M,D,Y,NULL);

  av=avma; y = cgetg(3,t_VEC);
  p1 = gaussmoduloall(M,D,Y, (GEN*)y+2);
  if (p1==gen_0) { avma=av; return gen_0; }
  gel(y,1) = p1; return y;
}

GEN
gaussmodulo2(GEN M, GEN D, GEN Y) { return matsolvemod0(M,D,Y,1); }

GEN
gaussmodulo(GEN M, GEN D, GEN Y) { return matsolvemod0(M,D,Y,0); }
