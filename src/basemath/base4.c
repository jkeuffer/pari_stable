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

/*******************************************************************/
/*                                                                 */
/*                       BASIC NF OPERATIONS                       */
/*                           (continued)                           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"

extern GEN hnfmerge_get_1(GEN A, GEN B);
extern GEN makeprimetoideal(GEN nf,GEN UV,GEN uv,GEN x);
extern GEN gauss_triangle_i(GEN A, GEN B,GEN t);
extern GEN hnf_invimage(GEN A, GEN b);
extern int hnfdivide(GEN A, GEN B);
extern GEN colreducemodHNF(GEN x, GEN y, GEN *Q);
extern GEN special_anti_uniformizer(GEN nf, GEN pr);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *newx);

static GEN mat_ideal_two_elt2(GEN nf, GEN x, GEN a);

/*******************************************************************/
/*                                                                 */
/*                     IDEAL OPERATIONS                            */
/*                                                                 */
/*******************************************************************/

/* A valid ideal is either principal (valid nf_element), or prime, or a matrix
 * on the integer basis (preferably HNF).
 * A prime ideal is of the form [p,a,e,f,b], where the ideal is p.Z_K+a.Z_K,
 * p is a rational prime, a belongs to Z_K, e=e(P/p), f=f(P/p), and b
 * Lenstra constant (p.P^(-1)= p Z_K + b Z_K).
 *
 * An idele is a couple[I,V] where I is a valid ideal and V a row vector
 * with r1+r2 components (real or complex). For instance, if M=(a), V
 * contains the complex logarithms of the first r1+r2 conjugates of a
 * (depends on the chosen generator a). All subroutines work with either
 * ideles or ideals (an omitted V is assumed to be 0).
 *
 * All ideals are output in HNF form. */

/* types and conversions */

static long
idealtyp(GEN *ideal, GEN *arch)
{
  GEN x = *ideal;
  long t,lx,tx = typ(x);

  if (tx==t_VEC && lg(x)==3)
  { *arch = (GEN)x[2]; x = (GEN)x[1]; tx = typ(x); }
  else
    *arch = NULL;
  switch(tx)
  {
    case t_MAT: lx = lg(x);
      if (lx>2) t = id_MAT;
      else
      {
        t = id_PRINCIPAL;
        x = (lx==2)? (GEN)x[1]: gzero;
      }
      break;

    case t_VEC: if (lg(x)!=6) err(idealer2);
      t = id_PRIME; break;

    case t_POL: case t_POLMOD: case t_COL:
      t = id_PRINCIPAL; break;
    default:
      if (tx!=t_INT && !is_frac_t(tx)) err(idealer2);
      t = id_PRINCIPAL;
  }
  *ideal = x; return t;
}

static GEN
prime_to_ideal_aux(GEN nf, GEN vp)
{
  GEN m = eltmul_get_table(nf, (GEN)vp[2]);
  return hnfmodid(m, (GEN)vp[1]);
}

/* vp = [a,x,...], a in Z. Return (a,x)  [HACK: vp need not be prime] */
GEN
prime_to_ideal(GEN nf, GEN vp)
{
  pari_sp av=avma;
  if (typ(vp) == t_INT) return gscalmat(vp, degpol(nf[1]));
  return gerepileupto(av, prime_to_ideal_aux(nf,vp));
}

/* x = ideal in matrix form. Put it in hnf. */
static GEN
idealmat_to_hnf(GEN nf, GEN x)
{
  long rx = lg(x)-1, N = degpol(nf[1]);
  GEN cx;

  if (!rx) return gscalmat(gzero,N);

  x = Q_primitive_part(x, &cx);
  if (rx < N)
  {
    GEN m = cgetg(rx*N + 1, t_MAT);
    long i,j,k;
    for (i=k=1; i<=rx; i++)
      for (j=1; j<=N; j++) m[k++] = (long)element_mulid(nf,(GEN)x[i],j);
    x = m;
  }
  x = hnfmod(x, detint(x));
  return cx? gmul(x,cx): x;
}

int
ishnfall(GEN x)
{
  long i,j, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    if (gsigne(gcoeff(x,i,i)) <= 0) return 0;
    for (j=1; j<i; j++)
      if (!gcmp0(gcoeff(x,i,j))) return 0;
  }
  return (gsigne(gcoeff(x,1,1)) > 0);
}
/* same x is known to be integral */
int
Z_ishnfall(GEN x)
{
  long i,j, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    if (signe(gcoeff(x,i,i)) <= 0) return 0;
    for (j=1; j<i; j++)
      if (signe(gcoeff(x,i,j))) return 0;
  }
  return (signe(gcoeff(x,1,1)) > 0);
}

GEN
idealhermite_aux(GEN nf, GEN x)
{
  long N,tx,lx;
  GEN z, cx;

  tx = idealtyp(&x,&z);
  if (tx == id_PRIME) return prime_to_ideal_aux(nf,x);
  if (tx == id_PRINCIPAL)
  {
    x = eltmul_get_table(nf, x);
    return idealmat_to_hnf(nf,x);
  }
  N=degpol(nf[1]); lx = lg(x);
  if (lg(x[1]) != N+1) err(idealer2);

  if (lx == N+1 && ishnfall(x)) return x;
  if (lx <= N) return idealmat_to_hnf(nf,x);
  x = Q_primitive_part(x, &cx);
  x = hnfmod(x,detint(x));
  return cx? gmul(x, cx): x;
}

GEN
idealhermite(GEN nf, GEN x)
{
  pari_sp av=avma;
  GEN p1;
  nf = checknf(nf); p1 = idealhermite_aux(nf,x);
  if (p1==x || p1==(GEN)x[1]) return gcopy(p1);
  return gerepileupto(av,p1);
}

GEN
principalideal(GEN nf, GEN x)
{
  GEN z = cgetg(2,t_MAT);

  nf = checknf(nf);
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      x = gscalcol(x, degpol(nf[1])); break;

    case t_POLMOD:
      x = checknfelt_mod(nf,x,"principalideal");
      /* fall through */
    case t_POL:
      x = algtobasis(nf,x);
      break;

    case t_MAT:
      if (lg(x)!=2) err(typeer,"principalideal");
      x = (GEN)x[1];
    case t_COL:
      if (lg(x)-1==degpol(nf[1])) { x = gcopy(x); break; }
    default: err(typeer,"principalideal");
  }
  z[1]=(long)x; return z;
}

static GEN
mylog(GEN x, long prec)
{
  if (gcmp0(x)) err(precer,"get_arch");
  return glog(x,prec);
}

GEN get_arch(GEN nf,GEN x,long prec);

static GEN
famat_get_arch(GEN nf, GEN x, long prec)
{
  GEN A, a, g = (GEN)x[1], e = (GEN)x[2];
  long i, l = lg(e);

  if (l <= 1)
    return get_arch(nf, gun, prec);
  A = NULL; /* -Wall */
  for (i=1; i<l; i++)
  {
    a = get_arch(nf, (GEN)g[i], prec);
    a = gmul((GEN)e[i], a);
    A = (i == 1)? a: gadd(A, a);
  }
  return A;
}

static GEN
scalar_get_arch(long R1, long RU, GEN x, long prec)
{
  GEN v = cgetg(RU+1,t_VEC);
  GEN p1 = glog(x, prec);
  long i;

  for (i=1; i<=R1; i++) v[i] = (long)p1;
  if (i <= RU)
  {
    p1 = gmul2n(p1,1);
    for (   ; i<=RU; i++) v[i] = (long)p1;
  }
  return v;
}

/* For internal use. Get archimedean components: [e_i log( sigma_i(x) )],
 * with e_i = 1 (resp 2.) for i <= R1 (resp. > R1) */
GEN
get_arch(GEN nf,GEN x,long prec)
{
  long i, RU, R1 = nf_get_r1(nf);
  GEN v;

  RU = lg(nf[6]) - 1;
  switch(typ(x))
  {
    case t_MAT: return famat_get_arch(nf,x,prec);
    case t_POLMOD:
    case t_POL: x = algtobasis_i(nf,x);   /* fall through */
    case t_COL: if (!isnfscalar(x)) break;
      x = (GEN)x[1]; /* fall through */
    default: /* rational number */
      return scalar_get_arch(R1, RU, x, prec);
  }

  v = cgetg(RU+1,t_VEC);
  if (isnfscalar(x)) /* rational number */
  {
    GEN p1 = glog((GEN)x[1], prec);

    for (i=1; i<=R1; i++) v[i] = (long)p1;
    if (i <= RU)
    {
      p1 = gmul2n(p1,1);
      for (   ; i<=RU; i++) v[i] = (long)p1;
    }
  }
  x = gmul(gmael(nf,5,1),x);
  for (i=1; i<=R1; i++) v[i] = (long)mylog((GEN)x[i],prec);
  for (   ; i<=RU; i++) v[i] = lmul2n(mylog((GEN)x[i],prec),1);
  return v;
}

GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);

static GEN
famat_get_arch_real(GEN nf,GEN x,GEN *emb,long prec)
{
  GEN A, T, a, t, g = (GEN)x[1], e = (GEN)x[2];
  long i, l = lg(e);

  if (l <= 1)
    return get_arch_real(nf, gun, emb, prec);
  A = T = NULL; /* -Wall */
  for (i=1; i<l; i++)
  {
    a = get_arch_real(nf, (GEN)g[i], &t, prec);
    if (!a) return NULL;
    a = gmul((GEN)e[i], a);
    t = vecpow(t, (GEN)e[i]);
    if (i == 1) { A = a;          T = t; }
    else        { A = gadd(A, a); T = vecmul(T, t); }
  }
  *emb = T; return A;
}

static GEN
scalar_get_arch_real(long R1, long RU, GEN u, GEN *emb, long prec)
{
  GEN v, x, p1;
  long i, s;

  s = gsigne(u);
  if (!s) err(talker,"0 in get_arch_real");
  x = cgetg(RU+1, t_COL);
  for (i=1; i<=RU; i++) x[i] = (long)u;

  v = cgetg(RU+1, t_COL);
  p1 = (s > 0)? glog(u,prec): gzero;
  for (i=1; i<=R1; i++) v[i] = (long)p1;
  if (i <= RU)
  {
    p1 = gmul2n(p1,1);
    for (   ; i<=RU; i++) v[i] = (long)p1;
  }
  *emb = x; return v;
}

static int
low_prec(GEN x)
{
  return gcmp0(x) || (typ(x) == t_REAL && lg(x) == 3);
}

/* as above but return NULL if precision problem, and set *emb to the
 * embeddings of x */
GEN
get_arch_real(GEN nf, GEN x, GEN *emb, long prec)
{
  long i, RU, R1 = nf_get_r1(nf);
  GEN v, t;

  RU = lg(nf[6])-1;
  switch(typ(x))
  {
    case t_MAT: return famat_get_arch_real(nf,x,emb,prec);

    case t_POLMOD:
    case t_POL: x = algtobasis_i(nf,x);   /* fall through */
    case t_COL: if (!isnfscalar(x)) break;
      x = (GEN)x[1]; /* fall through */
    default: /* rational number */
      return scalar_get_arch_real(R1, RU, x, emb, prec);
  }
  v = cgetg(RU+1,t_COL);
  x = gmul(gmael(nf,5,1), x);
  for (i=1; i<=R1; i++)
  {
    t = gabs((GEN)x[i],prec); if (low_prec(t)) return NULL;
    v[i] = llog(t,prec);
  }
  for (   ; i<=RU; i++)
  {
    t = gnorm((GEN)x[i]); if (low_prec(t)) return NULL;
    v[i] = llog(t,prec);
  }
  *emb = x; return v;
}

GEN
principalidele(GEN nf, GEN x, long prec)
{
  GEN p1, y = cgetg(3,t_VEC);
  pari_sp av;

  p1 = principalideal(nf,x);
  y[1] = (long)p1;
  av = avma; p1 = get_arch(nf,(GEN)p1[1],prec);
  y[2] = lpileupto(av,p1); return y;
}

/* GP functions */

GEN
ideal_two_elt0(GEN nf, GEN x, GEN a)
{
  if (!a) return ideal_two_elt(nf,x);
  return ideal_two_elt2(nf,x,a);
}

GEN
idealpow0(GEN nf, GEN x, GEN n, long flag, long prec)
{
  if (flag) return idealpowred(nf,x,n,prec);
  return idealpow(nf,x,n);
}

GEN
idealmul0(GEN nf, GEN x, GEN y, long flag, long prec)
{
  if (flag) return idealmulred(nf,x,y,prec);
  return idealmul(nf,x,y);
}

GEN
idealdiv0(GEN nf, GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 0: return idealdiv(nf,x,y);
    case 1: return idealdivexact(nf,x,y);
    default: err(flagerr,"idealdiv");
  }
  return NULL; /* not reached */
}

GEN
idealaddtoone0(GEN nf, GEN arg1, GEN arg2)
{
  if (!arg2) return idealaddmultoone(nf,arg1);
  return idealaddtoone(nf,arg1,arg2);
}

GEN
idealhnf0(GEN nf, GEN a, GEN b)
{
  pari_sp av;
  GEN x;
  if (!b) return idealhermite(nf,a);

  /* HNF of aZ_K+bZ_K */
  av = avma; nf = checknf(nf);
  x = concatsp(eltmul_get_table(nf,a), eltmul_get_table(nf,b));
  return gerepileupto(av, idealmat_to_hnf(nf, x));
}

GEN
idealhermite2(GEN nf, GEN a, GEN b)
{
  return idealhnf0(nf,a,b);
}

static int
ok_elt(GEN x, GEN xZ, GEN y)
{
  pari_sp av = avma;
  int r = gegal(x, hnfmodid(y, xZ));
  avma = av; return r;
}

static GEN
addmul_col(GEN a, long s, GEN b)
{
  long i,l;
  if (!s) return a? dummycopy(a): a;
  if (!a) return gmulsg(s,b);
  l = lg(a);
  for (i=1; i<l; i++)
    if (signe(b[i])) a[i] = laddii((GEN)a[i], mulsi(s, (GEN)b[i]));
  return a;
}

/* a <-- a + s * b, all coeffs integers */
static GEN
addmul_mat(GEN a, long s, GEN b)
{
  long j,l;
  if (!s) return a? dummycopy(a): a; /* copy otherwise next call corrupts a */
  if (!a) return gmulsg(s,b);
  l = lg(a);
  for (j=1; j<l; j++)
    (void)addmul_col((GEN)a[j], s, (GEN)b[j]);
  return a;
}

/* if x square matrix, assume it is HNF */
static GEN
mat_ideal_two_elt(GEN nf, GEN x)
{
  GEN y,a,beta,cx,xZ,mul;
  long i,lm, N = degpol(nf[1]);
  pari_sp av0,av,tetpil;

  y = cgetg(3,t_VEC); av = avma;
  if (lg(x[1]) != N+1) err(typeer,"ideal_two_elt");
  if (N == 2)
  {
    y[1] = lcopy(gcoeff(x,1,1));
    y[2] = lcopy((GEN)x[2]); return y;
  }

  x = Q_primitive_part(x, &cx); if (!cx) cx = gun;
  if (lg(x) != N+1) x = idealhermite_aux(nf,x);

  xZ = gcoeff(x,1,1);
  if (gcmp1(xZ))
  {
    cx = gerepilecopy(av,cx);
    y[1] = (long)cx;
    y[2] = (long)gscalcol_i(cx, N); return y;
  }
  av0 = avma;
  a = NULL; /* gcc -Wall */
  beta= cgetg(N+1, t_VEC);
  mul = cgetg(N+1, t_VEC); lm = 1; /* = lg(mul) */
  /* look for a in x such that a O/xZ = x O/xZ */
  for (i=2; i<=N; i++)
  {
    pari_sp av1 = avma;
    GEN t, y = eltmul_get_table(nf, (GEN)x[i]);
    t = FpM_red(y, xZ);
    if (gcmp0(t)) { avma = av1; continue; }
    if (ok_elt(x,xZ, t)) { a = (GEN)x[i]; break; }
    beta[lm]= x[i];
    /* mul[i] = { canonical generators for x[i] O/xZ as Z-module } */
    mul[lm] = (long)t; lm++;
  }
  if (i > N)
  {
    GEN z = cgetg(lm, t_VECSMALL);
    pari_sp av1;
    ulong c = 0;

    setlg(mul, lm);
    setlg(beta,lm);
    if (DEBUGLEVEL>3) fprintferr("ideal_two_elt, hard case:\n");
    for(av1=avma;;avma=av1)
    {
      if (++c == 100) {
        if (DEBUGLEVEL>3) fprintferr("using approximation theorem\n");
        a = mat_ideal_two_elt2(nf, x, xZ); goto END;
      }
      for (a=NULL,i=1; i<lm; i++)
      {
        long t = random_bits(4) - 7; /* in [-7,8] */
        z[i] = t;
        a = addmul_mat(a, t, (GEN)mul[i]);
      }
      /* a = matrix (NOT HNF) of ideal generated by beta.z in O/xZ */
      if (a && ok_elt(x,xZ, a)) break;
    }
    for (a=NULL,i=1; i<lm; i++)
      a = addmul_col(a, z[i], (GEN)beta[i]);
  }
END:
  a = centermod(a, xZ);
  tetpil = avma;
  y[1] = lmul(xZ,cx);
  y[2] = lmul(a, cx);
  gerepilemanyvec(av,tetpil,y+1,2); return y;
}

/* Given an ideal x, returns [a,alpha] such that a is in Q,
 * x = a Z_K + alpha Z_K, alpha in K^*
 * a = 0 or alpha = 0 are possible, but do not try to determine whether
 * x is principal. */
GEN
ideal_two_elt(GEN nf, GEN x)
{
  GEN z;
  long N, tx = idealtyp(&x,&z);

  nf = checknf(nf);
  if (tx == id_MAT) return mat_ideal_two_elt(nf,x);

  N = degpol(nf[1]); z = cgetg(3,t_VEC);
  if (tx == id_PRINCIPAL)
  {
    switch(typ(x))
    {
      case t_INT: case t_FRAC: case t_FRACN:
        z[1] = lcopy(x);
	z[2] = (long)zerocol(N); return z;

      case t_POLMOD:
        x = checknfelt_mod(nf, x, "ideal_two_elt"); /* fall through */
      case t_POL:
        z[1] = zero;
        z[2] = (long)algtobasis(nf,x); return z;
      case t_COL:
        if (lg(x)==N+1) {
          z[1] = zero;
          z[2] = lcopy(x); return z;
        }
    }
  }
  else if (tx == id_PRIME)
  {
    z[1] = lcopy((GEN)x[1]);
    z[2] = lcopy((GEN)x[2]); return z;
  }
  err(typeer,"ideal_two_elt");
  return NULL; /* not reached */
}

/* factorization */

/* x integral ideal in HNF, return v_p(Nx), *vz = v_p(x \cap Z)
 * Use x[1,1] = x \cap Z */
long
val_norm(GEN x, GEN p, long *vz)
{
  long i,l = lg(x), v;
  *vz = v = pvaluation(gcoeff(x,1,1), p, NULL);
  if (!v) return 0;
  for (i=2; i<l; i++)
    v += pvaluation(gcoeff(x,i,i), p, NULL);
  return v;
}

/* return factorization of Nx */
GEN
factor_norm(GEN x)
{
  GEN f = factor(gcoeff(x,1,1)), p = (GEN)f[1], e = (GEN)f[2];
  long i,k, l = lg(p);
  for (i=1; i<l; i++)
    e[i] = (long)val_norm(x,(GEN)p[i], &k);
  settyp(e, t_VECSMALL); return f;
}

GEN
idealfactor(GEN nf, GEN x)
{
  pari_sp av;
  long tx, i, j, k, lf, lc, N, l, v, vc, e;
  GEN f, f1, f2, c1, c2, y1, y2, y, p1, p2, cx, P;

  tx = idealtyp(&x,&y);
  if (tx == id_PRIME)
  {
    y = cgetg(3,t_MAT);
    y[1] = (long)_col(gcopy(x));
    y[2] = (long)_col(gun); return y;
  }
  av = avma;
  nf = checknf(nf);
  N = degpol(nf[1]);
  if (tx == id_PRINCIPAL) x = idealhermite_aux(nf, x);
  else
    if (lg(x) != N+1) x = idealmat_to_hnf(nf,x);
  if (lg(x)==1) err(talker,"zero ideal in idealfactor");
  x = Q_primitive_part(x, &cx);
  if (!cx)
  {
    c1 = c2 = NULL; /* gcc -Wall */
    lc = 1;
  }
  else
  {
    f = factor(cx);
    c1 = (GEN)f[1];
    c2 = (GEN)f[2]; lc = lg(c1);
  }
  f = factor_norm(x);
  f1 = (GEN)f[1];
  f2 = (GEN)f[2]; lf = lg(f1);
  y1 = cgetg((lf+lc-2)*N+1, t_COL);
  y2 = cgetg((lf+lc-2)*N+1, t_VECSMALL);
  k = 1;
  for (i=1; i<lf; i++)
  {
    p1 = primedec(nf,(GEN)f1[i]);
    l = f2[i]; /* = v_p(Nx) */
    vc = cx? ggval(cx,(GEN)f1[i]): 0;
    for (j=1; j<lg(p1); j++)
    {
      P = (GEN)p1[j]; e = itos((GEN)P[3]);
      v = idealval(nf,x,P);
      l -= v*itos((GEN)P[4]);
      v += vc*e; if (!v) continue;
      y1[k] = (long)P;
      y2[k] = v; k++;
      if (l == 0) break; /* now only the content contributes */
    }
    if (vc == 0) continue;
    for (j++; j<lg(p1); j++)
    {
      P = (GEN)p1[j]; e = itos((GEN)P[3]);
      y1[k] = (long)P;
      y2[k] = vc*e; k++;
    }
  }
  for (i=1; i<lc; i++)
  {
    /* p | Nx already treated */
    if (divise(gcoeff(x,1,1),(GEN)c1[i])) continue;
    p1 = primedec(nf,(GEN)c1[i]);
    vc = itos((GEN)c2[i]);
    for (j=1; j<lg(p1); j++)
    {
      P = (GEN)p1[j]; e = itos((GEN)P[3]);
      y1[k] = (long)P;
      y2[k] = vc*e; k++;
    }
  }
  y = cgetg(3,t_MAT);
  p1 = cgetg(k,t_COL); y[1] = (long)p1;
  p2 = cgetg(k,t_COL); y[2] = (long)p2;
  for (i=1; i<k; i++) { p1[i] = lcopy((GEN)y1[i]); p2[i] = lstoi(y2[i]); }
  y = gerepileupto(av, y);
  return sort_factor_gen(y, cmp_prime_ideal);
}

/* P prime ideal in primedec format. Return valuation(ix) at P */
long
idealval(GEN nf, GEN ix, GEN P)
{
  pari_sp av = avma, av1, lim;
  long N, vmax, vd, v, e, f, i, j, k, tx = typ(ix);
  GEN mul, B, a, x, y, r, t0, p, pk, cx, vals;

  if (is_extscalar_t(tx) || tx==t_COL) return element_val(nf,ix,P);
  tx = idealtyp(&ix,&a);
  if (tx == id_PRINCIPAL) return element_val(nf,ix,P);
  checkprimeid(P);
  p = (GEN)P[1];
  if (tx == id_PRIME) {
    if (!egalii(p, (GEN)ix[1])) return 0;
    return (gegal((GEN)P[2], (GEN)ix[2])
         || element_val(nf, (GEN)ix[2], P))? 1: 0;
  }
  nf = checknf(nf);
  N = degpol(nf[1]);
  checkid(ix, N);
  ix = Q_primitive_part(ix, &cx);
  if (lg(ix) != N+1) ix = idealmat_to_hnf(nf,ix);

  i = val_norm(ix,p, &k);
  if (!i) { avma = av; return cx? itos((GEN)P[3]) * ggval(cx,p): 0; }

  e = itos((GEN)P[3]);
  f = itos((GEN)P[4]);
  vd = cx? e * ggval(cx,p): 0;
  /* 0 <= ceil[v_P(ix) / e] <= v_p(ix \cap Z) --> v_P <= e * v_p */
  j = k * e;
  /* 0 <= v_P(ix) <= floor[v_p(Nix) / f] */
  i = i / f;
  vmax = min(i,j); /* v_P(ix) <= vmax */

  mul = cgetg(N+1,t_MAT); t0 = (GEN)P[5];
  B = cgetg(N+1,t_MAT);
  pk = gpowgs(p, (long)ceil((double)vmax / e));
  mul[1] = (long)t0;
  /* B[1] not needed: v_pr(ix[1]) = v_pr(ix \cap Z) is known already */
  B[1] = zero; /* dummy */
  for (j=2; j<=N; j++)
  {
    mul[j] = (long)element_mulid(nf,t0,j);
    x = (GEN)ix[j];
    y = cgetg(N+1, t_COL); B[j] = (long)y;
    for (i=1; i<=N; i++)
    { /* compute a = (x.t0)_i, ix in HNF ==> x[j+1..N] = 0 */
      a = mulii((GEN)x[1], gcoeff(mul,i,1));
      for (k=2; k<=j; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
      /* p | a ? */
      y[i] = ldvmdii(a,p,&r);
      if (signe(r)) { avma = av; return vd; }
    }
  }
  vals = cgetg(N+1, t_VECSMALL);
  /* vals[1] not needed */
  for (j = 2; j <= N; j++)
  {
    B[j] = (long)Q_primitive_part((GEN)B[j], &cx);
    vals[j] = cx? 1 + e * ggval(cx, p): 1;
  }
  av1 = avma; lim = stack_lim(av1,3);
  y = cgetg(N+1,t_COL);
  /* can compute mod p^ceil((vmax-v)/e) */
  for (v = 1; v < vmax; v++)
  { /* we know v_pr(Bj) >= v for all j */
    if (e == 1 || (vmax - v) % e == 0) pk = diviiexact(pk, p);
    for (j = 2; j <= N; j++)
    {
      x = (GEN)B[j]; if (v < vals[j]) continue;
      for (i=1; i<=N; i++)
      {
        pari_sp av2 = avma;
        a = mulii((GEN)x[1], gcoeff(mul,i,1));
        for (k=2; k<=N; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
        /* a = (x.t_0)_i; p | a ? */
        a = dvmdii(a,p,&r);
        if (signe(r)) { avma = av; return v + vd; }
        if (lgefint(a) > lgefint(pk)) a = resii(a, pk);
        y[i] = lpileuptoint(av2, a);
      }
      B[j] = (long)y; y = x;
      if (low_stack(lim,stack_lim(av1,3)))
      {
	if(DEBUGMEM>1) err(warnmem,"idealval");
        gerepileall(av1,3, &y,&B,&pk);
      }
    }
  }
  avma = av; return v + vd;
}

/* gcd and generalized Bezout */

GEN
idealadd(GEN nf, GEN x, GEN y)
{
  pari_sp av=avma;
  long N,tx,ty;
  GEN z, p1, dx, dy, dz;
  int modid;

  tx = idealtyp(&x,&z);
  ty = idealtyp(&y,&z);
  nf = checknf(nf); N = degpol(nf[1]);
  if (tx != id_MAT || lg(x)!=N+1) x = idealhermite_aux(nf,x);
  if (ty != id_MAT || lg(y)!=N+1) y = idealhermite_aux(nf,y);
  if (lg(x) == 1) return gerepileupto(av,y);
  if (lg(y) == 1) return gerepileupto(av,x); /* check for 0 ideal */
  dx = Q_denom(x);
  dy = Q_denom(y); dz = mpppcm(dx,dy);
  if (gcmp1(dz)) dz = NULL; else {
    x = Q_muli_to_int(x, dz);
    y = Q_muli_to_int(y, dz);
  }
  if (isnfscalar((GEN)x[1]) && isnfscalar((GEN)y[1]))
  {
    p1 = mppgcd(gcoeff(x,1,1), gcoeff(y,1,1));
    modid = 1;
  }
  else
  {
    p1 = mppgcd(detint(x), detint(y));
    modid = 0;
  }
  if (gcmp1(p1))
  {
    if (!dz) { avma = av; return idmat(N); }
    dz = gclone(ginv(dz)); avma = av;
    z = gscalmat(dz, N);
    gunclone(dz); return z;
  }
  z = concatsp(x,y);
  z = modid? hnfmodid(z,p1): hnfmod(z, p1);
  if (dz) z = gdiv(z,dz);
  return gerepileupto(av,z);
}

static GEN
get_hnfid(GEN nf, GEN x)
{
  GEN junk;
  long t = idealtyp(&x, &junk);
  return (t != id_MAT || lg(x) == 1 || lg(x) != lg(x[1]) || !ishnfall(x))
    ? idealhermite_aux(nf,x): x;
}

GEN
idealaddtoone_i(GEN nf, GEN x, GEN y)
{
  GEN xh = get_hnfid(nf, x), yh = get_hnfid(nf, y);
  GEN a = hnfmerge_get_1(xh, yh);
  return lllreducemodmatrix(a, idealmulh(nf,xh,yh));
}

/* y should be an idele (not mandatory). For internal use. */
static GEN
ideleaddone_i(GEN nf, GEN x, GEN y)
{
  GEN p1, p2, u, arch, archp;
  long i, nba;

  (void)idealtyp(&y, &arch);
  u = idealaddtoone_i(nf, x, y); /* u in x, 1-u in y */
  if (!arch) return u;

  if (typ(arch) != t_VEC && lg(arch)-1 != nf_get_r1(nf))
    err(talker,"incorrect idele in idealaddtoone");
  archp = arch_to_perm(arch);
  if (lg(archp) == 1) return u;

  if (gcmp0(u)) u = (GEN)idealhermite_aux(nf,x)[1];
  p2 = zarchstar(nf, idealmul(nf,x,y), archp);
  p1 = lift_intern(gmul((GEN)p2[3], zsigne(nf,u,archp)));
  p2 = (GEN)p2[2]; nba = 0;
  for (i = 1; i < lg(p1); i++)
    if (signe(p1[i])) { nba = 1; u = element_mul(nf,u,(GEN)p2[i]); }
  if (gcmp0(u)) return gcopy((GEN)x[1]); /* can happen if y = Z_K */
  return nba? u: gcopy(u);
}

GEN
unnf_minus_x(GEN x)
{
  long i, N = lg(x);
  GEN y = cgetg(N,t_COL);

  y[1] = lsub(gun,(GEN)x[1]);
  for (i=2;i<N; i++) y[i] = lneg((GEN)x[i]);
  return y;
}

static GEN
addone(GEN f(GEN,GEN,GEN), GEN nf, GEN x, GEN y)
{
  GEN z = cgetg(3,t_VEC), a;
  pari_sp av = avma;
  nf = checknf(nf);
  a = gerepileupto(av, f(nf,x,y));
  z[1]=(long)a;
  z[2]=(long)unnf_minus_x(a); return z;
}

GEN
idealaddtoone(GEN nf, GEN x, GEN y)
{
  return addone(idealaddtoone_i,nf,x,y);
}

GEN
ideleaddone(GEN nf, GEN x, GEN y)
{
  return addone(ideleaddone_i,nf,x,y);
}

/* given an element x in Z_K and an integral ideal y with x, y coprime,
   outputs an element inverse of x modulo y */
GEN
element_invmodideal(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a, xh, yh;

  nf = checknf(nf);
  if (gcmp1(gcoeff(y,1,1))) return zerocol( degpol(nf[1]) );

  yh = get_hnfid(nf, y);
  switch (typ(x))
  {
    case t_POL: case t_POLMOD: case t_COL:
      xh = idealhermite_aux(nf,x); break;
    default: err(typeer,"element_invmodideal");
      return NULL; /* not reached */
  }
  a = element_div(nf, hnfmerge_get_1(xh, yh), x);
  return gerepileupto(av, nfreducemodideal(nf, a, y));
}

GEN
idealaddmultoone(GEN nf, GEN list)
{
  pari_sp av = avma;
  long N, i, j, k, tx = typ(list);
  GEN z, v, v1, v2, v3, p1;

  nf = checknf(nf); N = degpol(nf[1]);
  if (!is_vec_t(tx)) err(talker,"not a list in idealaddmultoone");
  k = lg(list); z = cgetg(1,t_MAT); list = dummycopy(list);
  if (k == 1) err(talker,"ideals don't sum to Z_K in idealaddmultoone");
  for (i=1; i<k; i++)
  {
    p1 = (GEN)list[i];
    if (typ(p1) != t_MAT || lg(p1) != lg(p1[1]))
      list[i] = (long)idealhermite_aux(nf,p1);
    z = concatsp(z, (GEN)list[i]);
  }
  v = hnfperm(z);
  v1 = (GEN)v[1];
  v2 = (GEN)v[2];
  v3 = (GEN)v[3];
  if (!gcmp1(gcoeff(v1,1,1)))
    err(talker,"ideals don't sum to Z_K in idealaddmultoone");
  for (j=0, i=1; i<=N; i++)
    if (gcmp1((GEN)v3[i])) { j = i; break; }
  v2 = (GEN)v2[(k-2)*N + j]; /* z v2 = 1 */
  v = cgetg(k, tx);
  for (i=1; i<k; i++)
    v[i] = lmul((GEN)list[i], vecextract_i(v2, (i-1)*N + 1, i*N));
  return gerepilecopy(av, v);
}

/* multiplication */

/* x integral ideal (without archimedean component) in HNF form
 * y = [a,alpha] corresponds to the ideal aZ_K+alpha Z_K (a is a
 * rational integer). Multiply them
 */
static GEN
idealmulspec(GEN nf, GEN x, GEN y)
{
  long i, N=lg(x)-1;
  GEN m, mod, a = (GEN)y[1], alpha = (GEN)y[2];

  if (isnfscalar(alpha))
    return gmul(mppgcd(a, (GEN)alpha[1]),x);
  mod = mulii(a, gcoeff(x,1,1));
  m = cgetg((N<<1)+1,t_MAT);
  for (i=1; i<=N; i++) m[i]=(long)element_muli(nf,alpha,(GEN)x[i]);
  for (i=1; i<=N; i++) m[i+N]=lmul(a,(GEN)x[i]);
  return hnfmodid(m,mod);
}

/* x ideal (matrix form,maximal rank), vp prime ideal (primedec). Output the
 * product. Can be used for arbitrary vp of the form [p,a,e,f,b], IF vp
 * =pZ_K+aZ_K, p is an integer, and norm(vp) = p^f; e and b are not used.
 * For internal use. */
GEN
idealmulprime(GEN nf, GEN x, GEN vp)
{
  GEN cx;
  x = Q_primitive_part(x, &cx);
  x = idealmulspec(nf,x,vp);
  return cx? gmul(x,cx): x;
}

GEN arch_mul(GEN x, GEN y);
GEN vecpow(GEN x, GEN n);
GEN vecmul(GEN x, GEN y);

static GEN
mul(GEN nf, GEN x, GEN y)
{
  GEN yZ = gcoeff(y,1,1);
  if (is_pm1(yZ)) return gcopy(x);
  y = mat_ideal_two_elt(nf,y);
  return idealmulspec(nf, x, y);
}

/* Assume ix and iy are integral in HNF form (or ideles of the same form).
 * HACK: ideal in iy can be of the form [a,b], a in Z, b in Z_K
 * For internal use. */
GEN
idealmulh(GEN nf, GEN ix, GEN iy)
{
  long f = 0;
  GEN res,x,y;

  if (typ(ix)==t_VEC) {f=1;  x=(GEN)ix[1];} else x=ix;
  if (typ(iy)==t_VEC && typ(iy[1]) != t_INT) {f+=2; y=(GEN)iy[1];} else y=iy;
  res = f? cgetg(3,t_VEC): NULL;

  if (typ(y) == t_VEC)
    y = idealmulspec(nf,x,y);
  else
  {
    GEN xZ = gcoeff(x,1,1);
    GEN yZ = gcoeff(x,1,1);
    y = (cmpii(xZ, yZ) < 0)? mul(nf,y,x): mul(nf,x,y);
  }
  if (!f) return y;

  res[1] = (long)y;
  if (f==3) y = arch_mul((GEN)ix[2], (GEN)iy[2]);
  else
  {
    y = (f==2)? (GEN)iy[2]: (GEN)ix[2];
    y = gcopy(y);
  }
  res[2] = (long)y; return res;
}

GEN
mul_content(GEN cx, GEN cy)
{
  if (!cx) return cy;
  if (!cy) return cx;
  return gmul(cx,cy);
}

/* x and y are ideals in matrix form */
static GEN
idealmat_mul(GEN nf, GEN x, GEN y)
{
  long i,j, rx = lg(x)-1, ry = lg(y)-1;
  GEN cx, cy, m;

  x = Q_primitive_part(x, &cx);
  y = Q_primitive_part(y, &cy); cx = mul_content(cx,cy);
  if (rx <= 2 || ry <= 2)
  {
    m = cgetg(rx*ry+1,t_MAT);
    for (i=1; i<=rx; i++)
      for (j=1; j<=ry; j++)
        m[(i-1)*ry+j] = (long)element_muli(nf,(GEN)x[i],(GEN)y[j]);
    if (isnfscalar((GEN)x[1]) && isnfscalar((GEN)y[1]))
    {
      GEN p1 = mulii(gcoeff(x,1,1),gcoeff(y,1,1));
      y = hnfmodid(m, p1);
    }
    else
      y = hnfmod(m, detint(m));
  }
  else
  {
    if (!Z_ishnfall(x)) x = idealmat_to_hnf(nf,x);
    if (!Z_ishnfall(y)) y = idealmat_to_hnf(nf,y);
    y = idealmulh(nf,x,y);
  }
  return cx? gmul(y,cx): y;
}

/* operations on elements in factored form */

GEN
to_famat(GEN g, GEN e)
{
  GEN h = cgetg(3,t_MAT);
  if (typ(g) != t_COL) { g = dummycopy(g); settyp(g, t_COL); }
  if (typ(e) != t_COL) { e = dummycopy(e); settyp(e, t_COL); }
  h[1] = (long)g;
  h[2] = (long)e; return h;
}

GEN
to_famat_all(GEN x, GEN y) { return to_famat(_col(x), _col(y)); }

static GEN
append(GEN v, GEN x)
{
  long i, l = lg(v);
  GEN w = cgetg(l+1, typ(v));
  for (i=1; i<l; i++) w[i] = lcopy((GEN)v[i]);
  w[i] = lcopy(x); return w;
}

/* add x^1 to factorisation f */
static GEN
famat_add(GEN f, GEN x)
{
  GEN t,h = cgetg(3,t_MAT);
  if (lg(f) == 1)
  {
    t=cgetg(2,t_COL); h[1]=(long)t; t[1]=lcopy(x);
    t=cgetg(2,t_COL); h[2]=(long)t; t[1]=un;
  }
  else
  {
    h[1] = (long)append((GEN)f[1], x); /* x may be a t_COL */
    h[2] = (long)concat((GEN)f[2], gun);
  }
  return h;
}

/* cf merge_factor_i */
GEN
famat_mul(GEN f, GEN g)
{
  GEN h;
  if (typ(g) != t_MAT) return famat_add(f, g);
  if (lg(f) == 1) return gcopy(g);
  if (lg(g) == 1) return gcopy(f);
  h = cgetg(3,t_MAT);
  h[1] = (long)concat((GEN)f[1], (GEN)g[1]);
  h[2] = (long)concat((GEN)f[2], (GEN)g[2]);
  return h;
}

static GEN
famat_sqr(GEN f)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  h = cgetg(3,t_MAT);
  h[1] = lcopy((GEN)f[1]);
  h[2] = lmul2n((GEN)f[2],1);
  return h;
}
GEN
famat_inv(GEN f)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  h = cgetg(3,t_MAT);
  h[1] = lcopy((GEN)f[1]);
  h[2] = lneg((GEN)f[2]);
  return h;
}
GEN
famat_pow(GEN f, GEN n)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  if (typ(f) != t_MAT) return to_famat_all(f,n);
  h = cgetg(3,t_MAT);
  h[1] = lcopy((GEN)f[1]);
  h[2] = lmul((GEN)f[2],n);
  return h;
}

GEN
famat_to_nf(GEN nf, GEN f)
{
  GEN t, *x, *e;
  long i;
  if (lg(f) == 1) return gun;

  x = (GEN*)f[1];
  e = (GEN*)f[2];
  t = element_pow(nf, x[1], e[1]);
  for (i=lg(x)-1; i>1; i--)
    t = element_mul(nf, t, element_pow(nf, x[i], e[i]));
  return t;
}

/* "compare" two nf elt. Goal is to quickly sort for uniqueness of
 * representation, not uniqueness of represented element ! */
static int
elt_cmp(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (ty == tx)
    return (tx == t_POL || tx == t_POLMOD)? cmp_pol(x,y): lexcmp(x,y);
  return tx - ty;
}
static int
elt_egal(GEN x, GEN y)
{
  if (typ(x) == typ(y)) return gegal(x,y);
  return 0;
}

GEN
famat_reduce(GEN fa)
{
  GEN E, F, G, L, g, e;
  long i, k, l;

  if (lg(fa) == 1) return fa;
  g = (GEN)fa[1]; l = lg(g);
  e = (GEN)fa[2];
  L = gen_sort(g, cmp_IND|cmp_C, &elt_cmp);
  G = cgetg(l, t_COL);
  E = cgetg(l, t_COL);
  /* merge */
  for (k=i=1; i<l; i++,k++)
  {
    G[k] = g[L[i]];
    E[k] = e[L[i]];
    if (k > 1 && elt_egal((GEN)G[k], (GEN)G[k-1]))
    {
      E[k-1] = laddii((GEN)E[k], (GEN)E[k-1]);
      k--;
    }
  }
  /* kill 0 exponents */
  l = k;
  for (k=i=1; i<l; i++)
    if (!gcmp0((GEN)E[i]))
    {
      G[k] = G[i];
      E[k] = E[i]; k++;
    }
  F = cgetg(3, t_MAT);
  setlg(G, k); F[1] = (long)G;
  setlg(E, k); F[2] = (long)E; return F;
}

/* assume (num(g[i]), id) = 1 for all i. Return prod g[i]^e[i] mod id.
 * EX = multiple of exponent of (O_K/id)^* */
GEN
famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id, GEN EX)
{
  GEN dh, h, n, z, plus = NULL, minus = NULL, idZ = gcoeff(id,1,1);
  long i, lx = lg(g);
  GEN EXo2 = (expi(EX) > 10)? shifti(EX,-1): NULL;

  if (is_pm1(idZ)) lx = 1; /* id = Z_K */
  for (i=1; i<lx; i++)
  {
    long sn;
    n = centermodii((GEN)e[i], EX, EXo2);
    sn = signe(n); if (!sn) continue;

    h = Q_remove_denom((GEN)g[i], &dh);
    if (dh)
      h = FpV_red(gmul(h,mpinvmod(dh,idZ)), idZ);
    if (sn > 0)
    {
      z = element_powmodideal(nf, h, n, id);
      plus = (plus == NULL)? z: element_mulmodideal(nf, plus, z, id);
    }
    else /* sn < 0 */
    {
      z = element_powmodideal(nf, h, negi(n), id);
      minus = (minus == NULL)? z: element_mulmodideal(nf, minus, z, id);
    }
  }
  if (minus)
  {
    minus = element_invmodideal(nf, minus, id);
    plus = plus? element_mulmodideal(nf, minus, plus, id): minus;
  }
  return plus? plus: gscalcol(gun, lg(id)-1);
}

/* assume pr has degree 1 and coprime to numerator(x) */
static GEN
nf_to_Fp_simple(GEN x, GEN modpr, GEN p)
{
  GEN c, r = zk_to_ff(Q_primitive_part(x, &c), modpr);
  if (c) r = gmod(gmul(r, c), p);
  return r;
}

static GEN
famat_to_Fp_simple(GEN nf, GEN x, GEN modpr, GEN p)
{
  GEN h, n, t = gun, g = (GEN)x[1], e = (GEN)x[2], q = subis(p,1);
  long i, l = lg(g);

  for (i=1; i<l; i++)
  {
    n = (GEN)e[i]; n = modii(n,q);
    if (!signe(n)) continue;

    h = (GEN)g[i];
    switch(typ(h))
    {
      case t_POL: case t_POLMOD: h = algtobasis(nf, h);  /* fall through */
      case t_COL: h = nf_to_Fp_simple(h, modpr, p); break;
      default: h = gmod(h, p);
    }
    t = mulii(t, powmodulo(h, n, p)); /* not worth reducing */
  }
  return modii(t, p);
}

/* cf famat_to_nf_modideal_coprime, but id is a prime of degree 1 (=pr) */
GEN
to_Fp_simple(GEN nf, GEN x, GEN pr)
{
  GEN T, p, modpr = zk_to_ff_init(nf, &pr, &T, &p);
  switch(typ(x))
  {
    case t_COL: return nf_to_Fp_simple(x,modpr,p);
    case t_MAT: return famat_to_Fp_simple(nf,x,modpr,p);
    default: err(impl,"generic conversion to finite field");
  }
  return NULL;
}

/* Compute t = prod g[i]^e[i] mod pr^k, assuming (t, pr) = 1.
 * Method: modify each g[i] so that it becomes coprime to pr :
 *  x / (p^k u) --> x * (b/p)^v_pr(x) / z^k u, where z = b^e/p^(e-1)
 * b/p = vp^(-1) times something prime to p; both numerator and denominator
 * are integral and coprime to pr.  Globally, we multiply by (b/p)^v_pr(t) = 1.
 *
 * EX = multiple of exponent of (O_K / pr^k)^* used to reduce the product in
 * case the e[i] are large */
GEN
famat_makecoprime(GEN nf, GEN g, GEN e, GEN pr, GEN prk, GEN EX)
{
  long i, l = lg(g);
  GEN prkZ,cx,x,u, zpow = gzero, p = (GEN)pr[1], b = (GEN)pr[5];
  GEN mul = eltmul_get_table(nf, b);
  GEN newg = cgetg(l+1, t_VEC); /* room for z */

  prkZ = gcoeff(prk, 1,1);
  for (i=1; i < l; i++)
  {
    x = _algtobasis(nf, (GEN)g[i]);
    x = Q_remove_denom(x, &cx);
    if (cx)
    {
      long k = pvaluation(cx, p, &u);
      if (!gcmp1(u)) /* could avoid the inversion, but prkZ is small--> cheap */
        x = gmul(x, mpinvmod(u, prkZ));
      if (k)
        zpow = addii(zpow, mulsi(k, (GEN)e[i]));
    }
    (void)int_elt_val(nf, x, p, mul, &x);
    newg[i] = (long)colreducemodHNF(x, prk, NULL);
  }
  if (zpow == gzero) setlg(newg, l);
  else
  {
    newg[i] = (long)FpV_red(special_anti_uniformizer(nf, pr), prkZ);
    e = concatsp(e, negi(zpow));
  }
  return famat_to_nf_modideal_coprime(nf, newg, e, prk, EX);
}

/* prod g[i]^e[i] mod bid, assume (g[i], id) = 1 */
GEN
famat_to_nf_modidele(GEN nf, GEN g, GEN e, GEN bid)
{
  GEN t,sarch,module,cyc,fa2;
  long lc;
  if (lg(g) == 1) return gscalcol_i(gun, degpol(nf[1])); /* 1 */
  module = (GEN)bid[1];
  fa2 = (GEN)bid[4]; sarch = (GEN)fa2[lg(fa2)-1];
  cyc = gmael(bid,2,2); lc = lg(cyc);
  t = NULL;
  if (lc != 1)
  {
    GEN EX = (GEN)cyc[1]; /* group exponent */
    GEN id = (GEN)module[1];
    t = famat_to_nf_modideal_coprime(nf, g, e, id, EX);
  }
  if (!t) t = gun;
  return set_sign_mod_idele(nf, to_famat(g,e), t, module, sarch);
}

GEN
famat_to_arch(GEN nf, GEN fa, long prec)
{
  GEN g,e, y = NULL;
  long i,l;

  if (typ(fa) != t_MAT) return get_arch(nf, fa, prec);
  if (lg(fa) == 1) return zerovec(lg(nf[6])-1);
  g = (GEN)fa[1];
  e = (GEN)fa[2]; l = lg(e);
  for (i=1; i<l; i++)
  {
    GEN t, x = _algtobasis(nf, (GEN)g[i]);
    x = Q_primpart(x);
    /* multiplicative arch would be better (save logs), but exponents overflow
     * [ could keep track of expo separately, but not worth it ] */
    t = gmul(get_arch(nf,x,prec), (GEN)e[i]);
    y = y? gadd(y,t): t;
  }
  return y;
}

GEN
vecmul(GEN x, GEN y)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return gmul(x,y);
  lx = lg(x); z = cgetg(lx,tx);
  for (i=1; i<lx; i++) z[i] = (long)vecmul((GEN)x[i], (GEN)y[i]);
  return z;
}

GEN
vecinv(GEN x)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return ginv(x);
  lx = lg(x); z = cgetg(lx, tx);
  for (i=1; i<lx; i++) z[i] = (long)vecinv((GEN)x[i]);
  return z;
}

GEN
vecpow(GEN x, GEN n)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return powgi(x,n);
  lx = lg(x); z = cgetg(lx, tx);
  for (i=1; i<lx; i++) z[i] = (long)vecpow((GEN)x[i], n);
  return z;
}

GEN
vecdiv(GEN x, GEN y) { return vecmul(x, vecinv(y)); }

/* x,y assumed to be of the same type, either
 * 	t_VEC: logarithmic distance components
 * 	t_COL: multiplicative distance components [FIXME: find decent type]
 *	t_POLMOD: nf elt
 *	t_MAT: factorisation of nf elt */
GEN
arch_mul(GEN x, GEN y) {
  switch (typ(x)) {
    case t_POLMOD: return gmul(x, y);
    case t_COL: return vecmul(x, y);
    case t_MAT:    return (x == y)? famat_sqr(x): famat_mul(x,y);
    default:       return (x == y)? gmul2n(x,1): gadd(x,y); /* t_VEC */
  }
}

GEN
arch_inv(GEN x) {
  switch (typ(x)) {
    case t_POLMOD: return ginv(x);
    case t_COL:    return vecinv(x);
    case t_MAT:    return famat_inv(x);
    default:       return gneg(x); /* t_VEC */
  }
}

GEN
arch_pow(GEN x, GEN n) {
  switch (typ(x)) {
    case t_POLMOD: return powgi(x,n);
    case t_COL:    return vecpow(x,n);
    case t_MAT:    return famat_pow(x,n);
    default:       return gmul(n,x);
  }
}

static GEN
idealmulelt(GEN nf, GEN x, GEN v)
{
  long t = typ(x);
  if (t == t_POL || t == t_POLMOD) x = algtobasis(nf,x);
  if (isnfscalar(x)) x = (GEN)x[1];
  if (typ(x) != t_COL) return gmul(gabs(x,0), v);
  return idealmat_to_hnf(nf, element_mulvec(nf, x, v));
}

/* output the ideal product ix.iy (don't reduce) */
GEN
idealmul(GEN nf, GEN x, GEN y)
{
  pari_sp av;
  long tx,ty,f;
  GEN res,ax,ay,p1;

  tx = idealtyp(&x,&ax);
  ty = idealtyp(&y,&ay);
  if (tx>ty) {
    res=ax; ax=ay; ay=res;
    res=x; x=y; y=res;
    f=tx; tx=ty; ty=f;
  }
  f = (ax||ay); res = f? cgetg(3,t_VEC): NULL; /* product is an idele */
  nf=checknf(nf); av=avma;
  switch(tx)
  {
    case id_PRINCIPAL:
      switch(ty)
      {
        case id_PRINCIPAL:
          p1 = idealhermite_aux(nf, element_mul(nf,x,y));
          break;
        case id_PRIME:
        {
          GEN mx = eltmul_get_table(nf, x);
          GEN mpi= eltmul_get_table(nf, (GEN)y[2]);
          p1 = concatsp(gmul(mx,(GEN)y[1]), gmul(mx,mpi));
          p1 = idealmat_to_hnf(nf, p1);
          break;
        }
        default: /* id_MAT */
          p1 = idealmulelt(nf, x,y);
      }break;

    case id_PRIME:
      p1 = (ty==id_PRIME)? prime_to_ideal_aux(nf,y)
                         : idealmat_to_hnf(nf,y);
      p1 = idealmulprime(nf,p1,x); break;

    default: /* id_MAT */
      p1 = idealmat_mul(nf,x,y);
  }
  p1 = gerepileupto(av,p1);
  if (!f) return p1;

  if (ax && ay)
    ax = arch_mul(ax, ay);
  else
    ax = gcopy(ax? ax: ay);
  res[1]=(long)p1; res[2]=(long)ax; return res;
}

/* norm of an ideal */
GEN
idealnorm(GEN nf, GEN x)
{
  pari_sp av = avma;
  long tx;
  GEN y;

  nf = checknf(nf);
  switch(idealtyp(&x,&y))
  {
    case id_PRIME:
      return powgi((GEN)x[1],(GEN)x[4]);
    case id_PRINCIPAL:
      x = gnorm(basistoalg(nf,x)); break;
    default:
      if (lg(x) != lgef(nf[1])-2) x = idealhermite_aux(nf,x);
      x = dethnf(x);
  }
  tx = typ(x);
  if (tx == t_INT) return gerepileuptoint(av, absi(x));
  if (tx != t_FRAC) err(typeer, "idealnorm");
  return gerepileupto(av, gabs(x,0));
}

/* inverse */

/* rewritten from original code by P.M & M.H.
 *
 * I^(-1) = { x \in K, Tr(x D^(-1) I) \in Z }, D different of K/Q
 *
 * nf[5][6] = d_K * D^(-1) is integral = d_K T^(-1), T = (Tr(wi wj))
 * nf[5][7] = same in 2-elt form */
static GEN
hnfideal_inv(GEN nf, GEN I)
{
  GEN J, dI, IZ,dual;

  I = Q_remove_denom(I, &dI);
  if (lg(I)==1) err(talker, "cannot invert zero ideal");
  IZ = gcoeff(I,1,1); /* I \cap Z */
  if (!signe(IZ)) err(talker, "cannot invert zero ideal");
  J = idealmulh(nf,I, gmael(nf,5,7));
 /* I in HNF, hence easily inverted; multiply by IZ to get integer coeffs
  * d_K cancels while solving the linear equations. */
  dual = gtrans( gauss_triangle_i(J, gmael(nf,5,6), IZ) );
  dual = hnfmodid(dual, IZ);
  if (dI) IZ = gdiv(IZ,dI);
  return gdiv(dual,IZ);
}

/* return p * P^(-1)  [integral] */
GEN
pidealprimeinv(GEN nf, GEN x)
{
  GEN y=cgetg(6,t_VEC); y[1]=x[1]; y[2]=x[5];
  y[3]=y[5]=zero; y[4]=lsubsi(degpol(nf[1]), (GEN)x[4]);
  return prime_to_ideal_aux(nf,y);
}

/* Calcule le dual de mat_id pour la forme trace */
GEN
idealinv(GEN nf, GEN x)
{
  GEN res,ax;
  pari_sp av=avma;
  long tx = idealtyp(&x,&ax);

  res = ax? cgetg(3,t_VEC): NULL;
  nf=checknf(nf); av=avma;
  switch (tx)
  {
    case id_MAT:
      if (lg(x) != lg(x[1])) x = idealmat_to_hnf(nf,x);
      if (lg(x)-1 != degpol(nf[1])) err(consister,"idealinv");
      x = hnfideal_inv(nf,x); break;
    case id_PRINCIPAL: tx = typ(x);
      if (is_const_t(tx)) x = ginv(x);
      else
      {
        switch(tx)
        {
          case t_COL: x = gmul((GEN)nf[7],x); break;
          case t_POLMOD: x = (GEN)x[2]; break;
        }
        x = QX_invmod(x,(GEN)nf[1]);
      }
      x = idealhermite_aux(nf,x); break;
    case id_PRIME:
      x = gdiv(pidealprimeinv(nf,x), (GEN)x[1]);
  }
  x = gerepileupto(av,x); if (!ax) return x;
  res[1]=(long)x;
  res[2]=(long)arch_inv(ax); return res;
}

/* return x such that vp^n = x/d */
static GEN
idealpowprime_spec(GEN nf, GEN vp, GEN n, GEN *d)
{
  GEN n1, x, r;
  long s = signe(n);

  if (s == 0) err(talker, "0th power in idealpowprime_spec");
  if (s < 0) n = negi(n);
  /* now n > 0 */
  x = dummycopy(vp);
  if (is_pm1(n)) /* n = 1 special cased for efficiency */
  {
    if (s < 0)
    {
      x[2] = x[5];
      *d = (GEN)x[1];
    }
    else
      *d = NULL;
  }
  else
  {
    n1 = dvmdii(n, (GEN)x[3], &r);
    if (signe(r)) n1 = addis(n1,1); /* n1 = ceil(n/e) */
    x[1] = (long)powgi((GEN)x[1],n1);
    if (s < 0)
    {
      x[2] = ldiv(element_pow(nf,(GEN)x[5],n), powgi((GEN)vp[1],subii(n,n1)));
      *d = (GEN)x[1];
    }
    else
    {
      x[2] = (long)element_pow(nf,(GEN)x[2],n);
      *d = NULL;
    }
  }
  return x;
}

static GEN
idealpowprime(GEN nf, GEN vp, GEN n)
{
  GEN x, d;
  long s = signe(n);

  nf = checknf(nf);
  if (s == 0) return idmat(degpol(nf[1]));
  x = idealpowprime_spec(nf, vp, n, &d);
  x = prime_to_ideal_aux(nf,x);
  if (d) x = gdiv(x, d);
  return x;
}

/* x * vp^n. Assume x in HNF (possibly non-integral) */
GEN
idealmulpowprime(GEN nf, GEN x, GEN vp, GEN n)
{
  GEN cx,y,dx;

  if (!signe(n)) return x;
  nf = checknf(nf);

  /* inert, special cased for efficiency */
  if (itos((GEN)vp[4]) == degpol(nf[1]))
    return gmul(x, powgi((GEN)vp[1], n));

  y = idealpowprime_spec(nf, vp, n, &dx);
  x = Q_primitive_part(x, &cx);
  if (cx && dx)
  {
    cx = gdiv(cx, dx);
    if (typ(cx) != t_FRAC) dx = NULL;
    else { dx = (GEN)cx[2]; cx = (GEN)cx[1]; }
    if (is_pm1(cx)) cx = NULL;
  }
  x = idealmulspec(nf,x,y);
  if (cx) x = gmul(x,cx);
  if (dx) x = gdiv(x,dx);
  return x;
}
GEN
idealdivpowprime(GEN nf, GEN x, GEN vp, GEN n)
{
  return idealmulpowprime(nf,x,vp, negi(n));
}

/* raise the ideal x to the power n (in Z) */
GEN
idealpow(GEN nf, GEN x, GEN n)
{
  pari_sp av;
  long tx,N,s;
  GEN res,ax,m,cx,n1,a,alpha;

  if (typ(n) != t_INT) err(talker,"non-integral exponent in idealpow");
  tx = idealtyp(&x,&ax);
  res = ax? cgetg(3,t_VEC): NULL;
  nf = checknf(nf);
  av=avma; N=degpol(nf[1]); s=signe(n);
  if (!s) x = idmat(N);
  else
    switch(tx)
    {
      case id_PRINCIPAL: tx = typ(x);
        if (!is_const_t(tx))
          switch(tx)
          {
            case t_COL: x = gmul((GEN)nf[7],x);
            case t_POL: x = gmodulcp(x,(GEN)nf[1]);
          }
        x = powgi(x,n);
        x = idealhermite_aux(nf,x); break;
      case id_PRIME:
        x = idealpowprime(nf,x,n); break;
      default:
        n1 = (s<0)? negi(n): n;

        x = Q_primitive_part(x, &cx);
        a=ideal_two_elt(nf,x); alpha=(GEN)a[2]; a=(GEN)a[1];
        alpha = element_pow(nf,alpha,n1);
        m = eltmul_get_table(nf, alpha);
        x = hnfmodid(m, powgi(a,n1));
        if (s<0) x = hnfideal_inv(nf,x);
        if (cx) x = gmul(x, powgi(cx,n));
    }
  x = gerepileupto(av, x);
  if (!ax) return x;
  ax = arch_pow(ax, n);
  res[1]=(long)x;
  res[2]=(long)ax;
  return res;
}

/* Return ideal^e in number field nf. e is a C integer. */
GEN
idealpows(GEN nf, GEN ideal, long e)
{
  long court[] = {evaltyp(t_INT) | _evallg(3),0,0};
  affsi(e,court); return idealpow(nf,ideal,court);
}

static GEN
_idealmulred(GEN nf, GEN x, GEN y, long prec)
{
  return ideallllred(nf,idealmul(nf,x,y), NULL, prec);
}

typedef struct {
  GEN nf;
  long prec;
} idealred_muldata;

static GEN
_mul(void *data, GEN x, GEN y)
{
  idealred_muldata *D = (idealred_muldata *)data;
  return _idealmulred(D->nf,x,y,D->prec);
}
static GEN
_sqr(void *data, GEN x)
{
  return _mul(data,x,x);
}

/* compute x^n (x ideal, n integer), reducing along the way */
GEN
idealpowred(GEN nf, GEN x, GEN n, long prec)
{
  pari_sp av=avma;
  long s = signe(n);
  idealred_muldata D;
  GEN y;

  if (typ(n) != t_INT) err(talker,"non-integral exponent in idealpowred");
  if (s == 0) return idealpow(nf,x,n);
  D.nf  = nf;
  D.prec= prec;
  y = leftright_pow(x, n, (void*)&D, &_sqr, &_mul);

  if (s < 0) y = idealinv(nf,y);
  if (s < 0 || is_pm1(n)) y = ideallllred(nf,y,NULL,prec);
  return gerepileupto(av,y);
}

GEN
idealmulred(GEN nf, GEN x, GEN y, long prec)
{
  pari_sp av = avma;
  return gerepileupto(av, _idealmulred(nf,x,y,prec));
}

long
isideal(GEN nf,GEN x)
{
  pari_sp av;
  long N,i,j,tx=typ(x),lx;

  nf=checknf(nf); lx=lg(x);
  if (tx==t_VEC && lx==3) { x=(GEN)x[1]; tx=typ(x); lx=lg(x); }
  if (is_scalar_t(tx))
    return (tx==t_INT || tx==t_FRAC || tx==t_FRACN || tx==t_POL ||
                     (tx==t_POLMOD && gegal((GEN)nf[1],(GEN)x[1])));
  if (typ(x)==t_VEC) return (lx==6);
  if (typ(x)!=t_MAT) return 0;
  if (lx == 1) return 1;
  N = degpol(nf[1]); if (lg(x[1])-1 != N) return 0;

  av = avma; x = Q_primpart(x);
  if (lx-1 != N) x = idealmat_to_hnf(nf,x);

  for (i=1; i<=N; i++)
    for (j=2; j<=N; j++)
      if (! hnf_invimage(x, element_mulid(nf,(GEN)x[i],j)))
      {
        avma = av; return 0;
      }
  avma=av; return 1;
}

GEN
idealdiv(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma, tetpil;
  GEN z = idealinv(nf,y);
  tetpil = avma; return gerepile(av,tetpil, idealmul(nf,x,z));
}

/* This routine computes the quotient x/y of two ideals in the number field nf.
 * It assumes that the quotient is an integral ideal.  The idea is to find an
 * ideal z dividing y such that gcd(Nx/Nz, Nz) = 1.  Then
 *
 *   x + (Nx/Nz)    x
 *   ----------- = ---
 *   y + (Ny/Nz)    y
 *
 * Proof: we can assume x and y are integral. Let p be any prime ideal
 *
 * If p | Nz, then it divides neither Nx/Nz nor Ny/Nz (since Nx/Nz is the
 * product of the integers N(x/y) and N(y/z)).  Both the numerator and the
 * denominator on the left will be coprime to p.  So will x/y, since x/y is
 * assumed integral and its norm N(x/y) is coprime to p.
 *
 * If instead p does not divide Nz, then v_p (Nx/Nz) = v_p (Nx) >= v_p(x).
 * Hence v_p (x + Nx/Nz) = v_p(x).  Likewise for the denominators.  QED.
 *
 *		Peter Montgomery.  July, 1994. */
GEN
idealdivexact(GEN nf, GEN x0, GEN y0)
{
  pari_sp av = avma;
  GEN x,y,Nx,Ny,Nz, cy = content(y0);

  nf = checknf(nf);
  if (gcmp0(cy)) err(talker, "cannot invert zero ideal");

  x = gdiv(x0,cy); Nx = idealnorm(nf,x);
  if (gcmp0(Nx)) { avma = av; return gcopy(x0); } /* numerator is zero */

  y = gdiv(y0,cy); Ny = idealnorm(nf,y);
  if (!gcmp1(denom(x)) || !divise(Nx,Ny))
    err(talker, "quotient not integral in idealdivexact");
  /* Find a norm Nz | Ny such that gcd(Nx/Nz, Nz) = 1 */
  for (Nz = Ny;;)
  {
    GEN p1 = mppgcd(Nz, divii(Nx,Nz));
    if (is_pm1(p1)) break;
    Nz = divii(Nz,p1);
  }
  /* Replace x/y  by  x+(Nx/Nz) / y+(Ny/Nz) */
  x = idealhermite_aux(nf, x);
  x = hnfmodid(x, divii(Nx,Nz));
  /* y reduced to unit ideal ? */
  if (Nz == Ny) return gerepileupto(av, x);

  y = idealhermite_aux(nf, y);
  y = hnfmodid(y, divii(Ny,Nz));
  y = hnfideal_inv(nf,y);
  return gerepileupto(av, idealmat_mul(nf,x,y));
}

GEN
idealintersect(GEN nf, GEN x, GEN y)
{
  pari_sp av=avma;
  long lz,i,N;
  GEN z,dx,dy;

  nf=checknf(nf); N=degpol(nf[1]);
  if (idealtyp(&x,&z)!=t_MAT || lg(x)!=N+1) x=idealhermite_aux(nf,x);
  if (idealtyp(&y,&z)!=t_MAT || lg(y)!=N+1) y=idealhermite_aux(nf,y);
  if (lg(x) == 1 || lg(y) == 1) { avma = av; return cgetg(1, t_MAT); }
  dx=denom(x); if (!gcmp1(dx))   y = gmul(y,dx);
  dy=denom(y); if (!gcmp1(dy)) { x = gmul(x,dy); dx = mulii(dx,dy); }
  z = kerint(concatsp(x,y)); lz=lg(z);
  for (i=1; i<lz; i++) setlg(z[i], N+1);
  z = gmul(x,z);
  z = hnfmodid(z, glcm(gcoeff(x,1,1), gcoeff(y,1,1)));
  if (!gcmp1(dx)) z = gdiv(z,dx);
  return gerepileupto(av,z);
}

/*******************************************************************/
/*                                                                 */
/*                      T2-IDEAL REDUCTION                         */
/*                                                                 */
/*******************************************************************/

GEN
computeGtwist(GEN nf, GEN vdir)
{
  long i, j, k, l, lG, v, r1, r2;
  GEN p1, G = gmael(nf,5,2);

  if (!vdir) return G;
  l = lg(vdir); lG = lg(G);
  p1 = dummycopy(G);
  nf_get_sign(nf, &r1, &r2);
  for (i=1; i<l; i++)
  {
    v = vdir[i]; if (!v) continue;
    if (i <= r1) {
      for (j=1; j<lG; j++) coeff(p1,i,j) = lmul2n(gcoeff(p1,i,j), v);
    } else {
      k = (i<<1) - r1;
      for (j=1; j<lG; j++)
      {
        coeff(p1,k-1,j) = lmul2n(gcoeff(p1,k-1,j), v);
        coeff(p1,k  ,j) = lmul2n(gcoeff(p1,k  ,j), v);
      }
    }
  }
  return p1;
}

static GEN
chk_vdir(GEN nf, GEN vdir)
{
  long l, i, t;
  GEN v;
  if (!vdir || gcmp0(vdir)) return NULL;
  l = lg(vdir);
  if (l != lg(nf[6])) err(talker, "incorrect vector length in idealred");
  t = typ(vdir);
  if (t == t_VECSMALL) return vdir;
  if (t != t_VEC) err(talker, "not a vector in idealred");
  v = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) v[i] = itos(gceil((GEN)vdir[i]));
  return v;
}

/* assume I in NxN matrix form (not necessarily HNF) */
static GEN
idealred_elt_i(GEN *ptnf, GEN I, GEN vdir, long *ptprec)
{
  GEN G, u, y, nf = *ptnf;
  long i, e, prec = *ptprec;

  e = gexpo(I)>>TWOPOTBITS_IN_LONG;
  if (e < 0) e = 0;
  for (i=1; ; i++)
  {
    G = computeGtwist(nf,vdir);
    y = gmul(G, I);
    u = lllintern(y, 100, 1, prec);
    if (u) break;

    if (i == MAXITERPOL) err(accurer,"ideallllred");
    prec = (prec<<1)-2;
    if (DEBUGLEVEL) err(warnprec,"ideallllred",prec);
    nf = nfnewprec(nf, e + prec);
  }
  *ptprec = prec;
  *ptnf = nf;
  return gmul(I, (GEN)u[1]); /* small elt in I */
}

GEN
ideallllred_elt(GEN nf, GEN I, GEN vdir)
{
  long prec = DEFAULTPREC;
  return idealred_elt_i(&nf, I, vdir, &prec);
}
GEN
idealred_elt(GEN nf, GEN I)
{
  return ideallllred_elt(nf, I, NULL);
}

GEN
ideallllred(GEN nf, GEN I, GEN vdir, long prec)
{
  pari_sp av = avma;
  long N,i,nfprec;
  GEN J,I0,Ired,res,aI,y,x,Nx,b,c1,c,pol;

  nf = checknf(nf); nfprec = nfgetprec(nf);
  if (prec <= 0) prec = nfprec;
  pol = (GEN)nf[1]; N = degpol(pol);
  Nx = x = c = c1 = NULL;
  if (idealtyp(&I,&aI) == id_PRINCIPAL)
  {
    if (gcmp0(I)) { y=gun; I=cgetg(1,t_MAT); } else { y=I; I=idmat(N); }
    goto END;
  }

  if (DEBUGLEVEL>5) msgtimer("entering idealllred");
  I0 = I;
  if (typ(I) != id_MAT || lg(I) != N+1) I = idealhermite_aux(nf,I);
  I = primitive_part(I, &c1);
  if (2 * expi(gcoeff(I,1,1)) >= bit_accuracy(nfprec))
    Ired = lllint_ip(I,4);
  else
    Ired = I;
  y = idealred_elt_i(&nf, Ired, chk_vdir(nf,vdir), &prec);

  if (isnfscalar(y))
  { /* already reduced */
    if (!aI) I = gcopy(I);
    y = NULL; goto END;
  }
  if (DEBUGLEVEL>5) msgtimer("LLL reduction");

  x = gmul((GEN)nf[7], y); Nx = subres(pol,x);
  b = gmul(Nx, QX_invmod(x,pol));
  b = algtobasis_i(nf,b);
  J = cgetg(N+1,t_MAT); /* = I Nx / x integral */
  for (i=1; i<=N; i++)
    J[i] = (long)element_muli(nf,b,(GEN)Ired[i]);
  J = Q_primitive_part(J, &c);
 /* c = content (I Nx / x) = Nx / den(I/x) --> d = den(I/x) = Nx / c
  * J = (d I / x); I[1,1] = I \cap Z --> d I[1,1] belongs to J and Z */
  if (isnfscalar((GEN)I[1]))
    b = mulii(gcoeff(I,1,1), c? diviiexact(Nx, c): Nx);
  else
    b = detint(J);
  I = hnfmodid(J,b);
  if (DEBUGLEVEL>5) msgtimer("new ideal");

END:
  if (!aI) return gerepileupto(av, I);

  switch(typ(aI))
  {
    case t_POLMOD: /* compute y, I0 = J y */
      if (!Nx) y = c1;
      else
      {
        c = mul_content(c,c1);
        y = c? gmul(x, gdiv(c,Nx)): gdiv(x, Nx);
      }
      break;

    case t_MAT: /* compute y, I0 = J y */
      if (!Nx) y = c1;
      else
      {
        c = mul_content(c,c1);
        y = c? gmul(y, gdiv(c,Nx)): gdiv(y, Nx);
      }
      break;

    case t_COL:
      if (y) y = vecinv(gmul(gmael(nf,5,1), y));
      break;

    default:
      if (y) y = gneg_i(get_arch(nf,y,prec));
      break;
  }
  if (y) aI = arch_mul(aI,y);
  res = cgetg(3,t_VEC);
  res[1] = (long)I;
  res[2] = (long)aI; return gerepilecopy(av, res);
}

GEN
minideal(GEN nf, GEN x, GEN vdir, long prec)
{
  pari_sp av = avma;
  long N, tx;
  GEN y;

  nf = checknf(nf);
  vdir = chk_vdir(nf,vdir);
  N = degpol(nf[1]);
  tx = idealtyp(&x,&y);
  if (tx == id_PRINCIPAL) return gcopy(x);
  if (tx != id_MAT || lg(x) != N+1) x = idealhermite_aux(nf,x);

  y = gmul(computeGtwist(nf,vdir), x);
  y = gmul(x, (GEN)lll(y,prec)[1]);
  return gerepileupto(av, principalidele(nf,y,prec));
}

/*******************************************************************/
/*                                                                 */
/*                   APPROXIMATION THEOREM                         */
/*                                                                 */
/*******************************************************************/

/* write x = x1 x2, x2 maximal s.t. (x2,f) = 1, return x2 */
static GEN
coprime_part(GEN x, GEN f)
{
  for (;;)
  {
    f = mppgcd(x, f); if (is_pm1(f)) break;
    x = diviiexact(x, f);
  }
  return x;
}

/* x t_INT, f ideal. Write x = x1 x2, sqf(x1) | f, (x2,f) = 1. Return x2 */
static GEN
nf_coprime_part(GEN nf, GEN x, GEN *listpr)
{
  long v, j, lp = lg(listpr), N = degpol(nf[1]);
  GEN x1, x2, ex, p, pr;

#if 0 /*1) via many gcds. Expensive ! */
  GEN f = idealprodprime(nf, (GEN)listpr);
  f = hnfmodid(f, x); /* first gcd is less expensive since x in Z */
  x = gscalmat(x, N);
  for (;;)
  {
    if (gcmp1(gcoeff(f,1,1))) break;
    x = idealdivexact(nf, x, f);
    f = hnfmodid(concatsp(f,x), gcoeff(x,1,1)); /* gcd(f,x) */
  }
  x2 = x;
#else /*2) from prime decomposition */
  x1 = NULL;
  for (j=1; j<lp; j++)
  {
    pr = listpr[j]; p = (GEN)pr[1];
    v = ggval(x, p); if (!v) continue;

    ex = mulsi(v, (GEN)pr[3]); /* = v_pr(x) > 0 */
    x1 = x1? idealmulpowprime(nf, x1, pr, ex)
           : idealpow(nf, pr, ex);
  }
  x = gscalmat(x, N);
  x2 = x1? idealdivexact(nf, x, x1): x;
#endif
  return x2;
}

/* L0 in K^*, assume (L0,f) = 1. Return L integral, L0 = L mod f  */
GEN
make_integral(GEN nf, GEN L0, GEN f, GEN *listpr)
{
  GEN fZ, t, L, D2, d1, d2, d;

  L = Q_remove_denom(L0, &d);
  if (!d) return L0;

  /* L0 = L / d, L integral */
  fZ = gcoeff(f,1,1);
  /* Kill denom part coprime to fZ */
  d2 = coprime_part(d, fZ);
  t = mpinvmod(d2, fZ); if (!is_pm1(t)) L = gmul(L,t);
  if (egalii(d, d2)) return L;

  d1 = diviiexact(d, d2);
  /* L0 = (L / d1) mod f. d1 not coprime to f
   * write (d1) = D1 D2, D2 minimal, (D2,f) = 1. */
  D2 = nf_coprime_part(nf, d1, listpr);
  t = idealaddtoone_i(nf, D2, f); /* in D2, 1 mod f */
  L = element_muli(nf,t,L);

  /* if (L0, f) = 1, then L in D1 ==> in D1 D2 = (d1) */
  return Q_div_to_int(L, d1); /* exact division */
}

/* assume L is a list of prime ideals. Return the product */
GEN
idealprodprime(GEN nf, GEN L)
{
  long l = lg(L), i;
  GEN z;

  if (l == 1) return idmat(degpol(nf[1]));
  z = prime_to_ideal(nf, (GEN)L[1]);
  for (i=2; i<l; i++) z = idealmulprime(nf,z, (GEN)L[i]);
  return z;
}

/* assume L is a list of prime ideals. Return prod L[i]^e[i] */
GEN
factorbackprime(GEN nf, GEN L, GEN e)
{
  long l = lg(L), i;
  GEN z;

  if (l == 1) return idmat(degpol(nf[1]));
  z = idealpow(nf, (GEN)L[1], (GEN)e[1]);
  for (i=2; i<l; i++)
    if (signe(e[i])) z = idealmulpowprime(nf,z, (GEN)L[i],(GEN)e[i]);
  return z;
}

/* F in Z squarefree, multiple of p. Return F-uniformizer for pr/p */
GEN
unif_mod_fZ(GEN pr, GEN F)
{
  GEN p = (GEN)pr[1], t = (GEN)pr[2];
  if (!egalii(F, p))
  {
    GEN u, v, q, e = (GEN)pr[3], a = diviiexact(F,p);
    q = is_pm1(e)? sqri(p): p;
    if (!gcmp1(bezout(q, a, &u,&v))) err(bugparier,"unif_mod_fZ");
    u = mulii(u,q);
    v = mulii(v,a);
    t = gmul(v, t); /* return u + vt */
    t[1] = laddii((GEN)t[1], u);
  }
  return t;
}
/* L = list of prime ideals, return lcm_i (L[i] \cap \ZM) */
GEN
init_unif_mod_fZ(GEN L)
{
  long i, r = lg(L);
  GEN pr, p, F = gun;
  for (i = 1; i < r; i++)
  {
    pr = (GEN)L[i]; p = (GEN)pr[1];
    if (!divise(F, p)) F = mulii(F,p);
  }
  return F;
}

void
check_listpr(GEN x)
{
  long l = lg(x), i;
  for (i=1; i<l; i++) checkprimeid((GEN)x[i]);
}

#if 0
/* p / pr^e(pr/p) */
static GEN
p_div_pr_e(GEN nf, GEN pr)
{
  GEN t = special_anti_uniformizer(nf, pr);
  return hnfmodid(eltmul_get_table(nf, t), (GEN)pr[1]);
}
#endif

/* Given a prime ideal factorization with possibly zero or negative
 * exponents, gives b such that v_p(b) = v_p(x) for all prime ideals pr | x
 * and v_pr(b)> = 0 for all other pr.
 * For optimal performance, all [anti-]uniformizers should be precomputed,
 * but no support for this yet.
 *
 * If nored, do not reduce result.
 * No garbage collecting */
GEN
idealapprfact_i(GEN nf, GEN x, int nored)
{
  GEN z, d, L, e, e2, F;
  long i, r;
  int flagden;

  nf = checknf(nf);
  L = (GEN)x[1];
  e = (GEN)x[2];
  F = init_unif_mod_fZ(L);
  flagden = 0;
  z = NULL; r = lg(e);
  for (i = 1; i < r; i++)
  {
    long s = signe(e[i]);
    GEN pi, q;
    if (!s) continue;
    if (s < 0) flagden = 1;
    pi = unif_mod_fZ((GEN)L[i], F);
    q = element_pow(nf, pi, (GEN)e[i]);
    z = z? element_mul(nf, z, q): q;
  }
  if (!z) return gscalcol_i(gun, degpol(nf[1]));
  if (nored)
  {
    if (flagden) err(impl,"nored + denominator in idealapprfact");
    return z;
  }
  e2 = cgetg(r, t_VEC);
  for (i=1; i<r; i++) e2[i] = laddis((GEN)e[i], 1);
  x = factorbackprime(nf, L,e2);
  if (flagden) /* denominator */
  {
    z = Q_remove_denom(z, &d);
    d = diviiexact(d, coprime_part(d, F));
    x = gmul(x, d);
  }
  else
    d = NULL;
  z = lllreducemodmatrix(z, x);
  return d? gdiv(z,d): z;
}

GEN
idealapprfact(GEN nf, GEN x) {
  pari_sp av = avma;
  if (typ(x) != t_MAT || lg(x) != 3)
    err(talker,"not a factorization in idealapprfact");
  check_listpr((GEN)x[1]);
  return gerepileupto(av, idealapprfact_i(nf, x, 0));
}

GEN
idealappr(GEN nf, GEN x) {
  pari_sp av = avma;
  return gerepileupto(av, idealapprfact_i(nf, idealfactor(nf, x), 0));
}

GEN
idealappr0(GEN nf, GEN x, long fl) {
  return fl? idealapprfact(nf, x): idealappr(nf, x);
}

/* merge a^e b^f. Assume a and b sorted. Keep 0 exponents */
static void
merge_factor(GEN *pa, GEN *pe, GEN b, GEN f)
{
  GEN A, E, a = *pa, e = *pe;
  long k, i, la = lg(a), lb = lg(b), l = la+lb-1;

  A = cgetg(l, t_COL);
  E = cgetg(l, t_COL);
  k = 1;
  for (i=1; i<la; i++)
  {
    A[i] = a[i];
    E[i] = e[i];
    if (k < lb && gegal((GEN)A[i], (GEN)b[k]))
    {
      E[i] = laddii((GEN)E[i], (GEN)f[k]);
      k++;
    }
  }
  for (; k < lb; i++,k++)
  {
    A[i] = b[k];
    E[i] = f[k];
  }
  setlg(A, i); *pa = A;
  setlg(E, i); *pe = E;
}

/* Given a prime ideal factorization x with possibly zero or negative exponents,
 * and a vector w of elements of nf, gives a b such that
 * v_p(b-w_p)>=v_p(x) for all prime ideals p in the ideal factorization
 * and v_p(b)>=0 for all other p, using the (standard) proof given in GTM 138.
 * Certainly not the most efficient, but sure. */
GEN
idealchinese(GEN nf, GEN x, GEN w)
{
  pari_sp av = avma;
  long ty = typ(w), i, N, r;
  GEN y, L, e, F, s, den;

  nf = checknf(nf); N = degpol(nf[1]);
  if (typ(x) != t_MAT || lg(x) != 3)
    err(talker,"not a prime ideal factorization in idealchinese");
  L = (GEN)x[1]; r = lg(L);
  e = (GEN)x[2];
  if (!is_vec_t(ty) || lg(w) != r)
    err(talker,"not a suitable vector of elements in idealchinese");
  if (r == 1) return gscalcol_i(gun,N);

  w = Q_remove_denom(w, &den);
  if (den)
  {
    GEN p = gen_sort(x, cmp_IND|cmp_C, &cmp_prime_ideal);
    GEN fa = idealfactor(nf, den); /* sorted */
    L = vecextract_p(L, p);
    e = vecextract_p(e, p);
    w = vecextract_p(w, p); settyp(w, t_VEC); /* make sure typ = t_VEC */
    merge_factor(&L, &e, (GEN)fa[1], (GEN)fa[2]);
    i = lg(L);
    w = concatsp(w, zerovec(i - r));
    r = i;
  }
  else
    e = dummycopy(e); /* do not destroy x[2] */
  for (i=1; i<r; i++)
    if (signe(e[i]) < 0) e[i] = zero;

  F = factorbackprime(nf, L, e);
  s = NULL;
  for (i=1; i<r; i++)
  {
    GEN u, t;
    if (gcmp0((GEN)w[i])) continue;
    u = hnfmerge_get_1(idealdivpowprime(nf,F, (GEN)L[i], (GEN)e[i]),
                       idealpow(nf, (GEN)L[i], (GEN)e[i]));
    t = element_mul(nf, u, (GEN)w[i]);
    s = s? gadd(s,t): t;
  }
  if (!s) { avma = av; return zerocol(N); }
  y = lllreducemodmatrix(s, F);
  return gerepileupto(av, den? gdiv(y,den): y);
}

static GEN
mat_ideal_two_elt2(GEN nf, GEN x, GEN a)
{
  GEN L, e, fact = idealfactor(nf,a);
  long i, r;
  L = (GEN)fact[1];
  e = (GEN)fact[2]; r = lg(e);
  for (i=1; i<r; i++) e[i] = lstoi( idealval(nf,x,(GEN)L[i]) );
  return centermod(idealapprfact_i(nf,fact,1), gcoeff(x,1,1));
}

/* Given an integral ideal x and a in x, gives a b such that
 * x = aZ_K + bZ_K using the approximation theorem */
GEN
ideal_two_elt2(GEN nf, GEN x, GEN a)
{
  pari_sp av = avma;
  GEN cx, b;

  nf = checknf(nf);
  a = _algtobasis(nf, a);
  x = idealhermite_aux(nf,x);
  if (gcmp0(x))
  {
    if (!gcmp0(a)) err(talker,"element not in ideal in ideal_two_elt2");
    avma = av; return gcopy(a);
  }
  x = Q_primitive_part(x, &cx);
  if (cx) a = gdiv(a, cx);
  if (!hnf_invimage(x, a))
    err(talker,"element does not belong to ideal in ideal_two_elt2");

  b = mat_ideal_two_elt2(nf, x, a);
  b = cx? gmul(b,cx): gcopy(b);
  return gerepileupto(av, b);
}

/* Given 2 integral ideals x and y in nf, returns a beta in nf such that
 * beta * x is an integral ideal coprime to y */
GEN
idealcoprime(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  long i, r;
  GEN L, e, fact = idealfactor(nf,y);

  L = (GEN)fact[1];
  e = (GEN)fact[2]; r = lg(e);
  for (i=1; i<r; i++) e[i] = lstoi( -idealval(nf,x,(GEN)L[i]) );
  return gerepileupto(av, idealapprfact_i(nf,fact,0));
}

/*******************************************************************/
/*                                                                 */
/*                  LINEAR ALGEBRA OVER Z_K  (HNF,SNF)             */
/*                                                                 */
/*******************************************************************/
void
check_ZKmodule(GEN x, char *s)
{
  if (typ(x) != t_VEC || lg(x) < 3) err(talker,"not a module in %s", s);
  if (typ(x[1]) != t_MAT) err(talker,"not a matrix in %s", s);
  if (typ(x[2]) != t_VEC || lg(x[2]) != lg(x[1]))
    err(talker,"not a correct ideal list in %s", s);
}

/* returns the first index i<=n such that x=v[i] if it exits, 0 otherwise */
long
isinvector(GEN v, GEN x, long n)
{
  long i;

  for (i=1; i<=n; i++)
    if (gegal((GEN)v[i],x)) return i;
  return 0;
}

static GEN
scalmul(GEN x, GEN v)
{
  long i, l;
  GEN y;
  if (gcmp1(x)) return dummycopy(v);
  if (gcmp_1(x)) return gneg(v);
  l = lg(v); y = cgetg(l, typ(v));
  for (i = 1; i < l; i++) y[i] = lmul(x, (GEN)v[i]);
  return y;
}

GEN
element_mulvec(GEN nf, GEN x, GEN v)
{
  long l, i;
  GEN M, y;

  if (typ(x) != t_COL) return scalmul(x, v);
  if (isnfscalar(x)) return scalmul((GEN)x[1], v);
  l = lg(v); y = cgetg(l, typ(v));
  M = eltmul_get_table(nf,x);
  for (i=1; i < l; i++) y[i] = lmul(M, (GEN)v[i]);
  return y;
}

static GEN
element_mulvecrow(GEN nf, GEN x, GEN m, long i, long lim)
{
  long l, j;
  GEN y, M = eltmul_get_table(nf,x);

  l = min(lg(m), lim+1); y = cgetg(l, t_VEC);
  for (j=1; j<l; j++) y[j] = lmul(M, gcoeff(m,i,j));
  return y;
}

/* Given an element x and an ideal in matrix form (not necessarily HNF),
 * gives an r such that x-r is in ideal and r is small. No checks */
GEN
element_reduce(GEN nf, GEN x, GEN ideal)
{
  pari_sp av = avma;
  long tx = typ(x);
  if (is_extscalar_t(tx)) x = algtobasis_i(checknf(nf), x);
  return gerepileupto(av, reducemodinvertible(x, ideal));
}
extern GEN close_modinvertible(GEN x, GEN y);
/* Given an element x and an ideal in matrix form (not necessarily HNF),
 * gives an a in ideal such that x-a is small. No checks */
static GEN 
element_close(GEN nf, GEN x, GEN ideal)
{
  pari_sp av = avma;
  long tx = typ(x);
  if (is_extscalar_t(tx)) x = algtobasis_i(checknf(nf), x);
  return gerepileupto(av, close_modinvertible(x, ideal));
}

/* A torsion-free module M over Z_K will be given by a row vector [A,I] with
 * two components. I=[\a_1,...,\a_k] is a row vector of k fractional ideals
 * given in HNF. A is an nxk matrix (same k and n the rank of the module)
 * such that if A_j is the j-th column of A then M=\a_1A_1+...\a_kA_k. We say
 * that [A,I] is a pseudo-basis if k=n */

#define swap(x,y) { long _t=x; x=y; y=_t; }

static GEN
colcomb(GEN nf, GEN u, GEN v, GEN A, GEN B)
{
  GEN z;
  if (gcmp0(u))
    z = element_mulvec(nf,v,B);
  else
  {
    z = u==gun? A: element_mulvec(nf,u,A);
    if (!gcmp0(v)) z = gadd(z, element_mulvec(nf,v,B));
  }
  return z;
}

/* u Z[s,] + v Z[t,] */
static GEN
rowcomb(GEN nf, GEN u, GEN v, long s, long t, GEN Z, long lim)
{
  GEN z;
  if (gcmp0(u))
    z = element_mulvecrow(nf,v,Z,t, lim);
  else
  {
    z = element_mulvecrow(nf,u,Z,s, lim);
    if (!gcmp0(v)) z = gadd(z, element_mulvecrow(nf,v,Z,t, lim));
  }
  return z;
}

static GEN
zero_nfbezout(GEN nf,GEN b, GEN A,GEN B,GEN *u,GEN *v,GEN *w,GEN *di)
{
  GEN d = idealmulelt(nf,b,B);
  pari_sp av;

  *di = idealinv(nf,d);
  av = avma; 
  *w = gerepileupto(av, idealmul(nf, idealmul(nf,A,B), *di));
  *v = element_inv(nf,b);
  *u = gzero; return d;
}

/* Given elements a,b and ideals A, B, outputs d = a.A+b.B and gives
 * di=d^-1, w=A.B.di, u, v such that au+bv=1 and u in A.di, v in B.di.
 * Assume A, B non-zero, but a or b can be zero (not both) */
static GEN
nfbezout(GEN nf,GEN a,GEN b, GEN A,GEN B, GEN *pu,GEN *pv,GEN *pw,GEN *pdi)
{
  GEN w, u,v, d, di, aA, bB;

  if (gcmp0(a)) return zero_nfbezout(nf,b,A,B,pu,pv,pw,pdi);
  if (gcmp0(b)) return zero_nfbezout(nf,a,B,A,pv,pu,pw,pdi);

  if (a != gun) /* frequently called with a = gun */
  {
    if (isnfscalar(a)) a = (GEN)a[1];
    if (gcmp1(a)) a = gun;
  }

  aA = (a == gun)? A: idealmulelt(nf,a,A);
  bB = idealmulelt(nf,b,B);
  d = idealadd(nf,aA,bB);
  di = hnfideal_inv(nf,d);
  if (gegal(aA, d))
  { /* aA | bB  (frequent) */
    w = B;
    v = gzero;
    if (a == gun)
      u = vec_ei(lg(B)-1, 1);
    else
    {
      u =  element_inv(nf, a);
      w = idealmulelt(nf, u, w); /* AB/d */
    }
  }
  else if (gegal(bB, d))
  { /* bB | aA  (slightly less frequent) */
    w = A;
    u = gzero;
    v = element_inv(nf, b);
    w = idealmulelt(nf, v, w); /* AB/d */
  }
  else
  { /* general case. Slow */
    GEN uv;
    w = idealmul(nf,aA,di); /* integral */
    uv = idealaddtoone(nf, w, idealmul(nf,bB,di));
    w = idealmul(nf,w,B);
    u = (GEN)uv[1];
    v = element_div(nf,(GEN)uv[2],b);
    if (a != gun)
    {
      GEN inva = element_inv(nf, a);
      u =  element_mul(nf,u,inva);
      w = idealmulelt(nf, inva, w); /* AB/d */
    }
  }
  *pu = u;
  *pv = v;
  *pw = w;
  *pdi = di; return d;
}

/* Given a torsion-free module x as above outputs a pseudo-basis for x in HNF */
GEN
nfhermite(GEN nf, GEN x)
{
  long i, j, def, k, m;
  pari_sp av0 = avma, av, lim;
  GEN y, A, I, J;

  nf = checknf(nf);
  check_ZKmodule(x, "nfhermite");
  A = (GEN)x[1];
  I = (GEN)x[2]; k = lg(A)-1;
  if (!k) err(talker,"not a matrix of maximal rank in nfhermite");
  m = lg(A[1])-1;
  if (k < m) err(talker,"not a matrix of maximal rank in nfhermite");

  av = avma; lim = stack_lim(av, 2);
  A = matalgtobasis(nf,A);
  I = dummycopy(I);
  J = zerovec(k); def = k+1;
  for (i=m; i>=1; i--)
  {
    GEN d, di = NULL;

    def--; j=def; while (j>=1 && gcmp0(gcoeff(A,i,j))) j--;
    if (!j) err(talker,"not a matrix of maximal rank in nfhermite");
    if (j==def) j--; else { swap(A[j], A[def]); swap(I[j], I[def]); }

    y = gcoeff(A,i,def);
    A[def] = (long)element_mulvec(nf, element_inv(nf,y), (GEN)A[def]);
    I[def] = (long)idealmulelt(nf, y, (GEN)I[def]);
    for (  ; j; j--)
    {
      GEN b, u,v,w, S, T, S0, T0 = (GEN)A[j];
      b = (GEN)T0[i]; if (gcmp0(b)) continue;

      S0 = (GEN)A[def];
      d = nfbezout(nf, gun,b, (GEN)I[def],(GEN)I[j], &u,&v,&w,&di);
      S = colcomb(nf, u,v, S0,T0);
      T = colcomb(nf, gun,gneg(b), T0,S0);
      A[def] = (long)S; A[j] = (long)T;
      I[def] = (long)d; I[j] = (long)w;
    }
    d = (GEN)I[def];
    if (!di) di = hnfideal_inv(nf,d);
    J[def] = (long)di;
    for (j=def+1; j<=k; j++)
    {
      GEN c = element_close(nf,gcoeff(A,i,j), idealmul(nf,d,(GEN)J[j]));
      A[j] = (long)colcomb(nf, gun,gneg(c), (GEN)A[j],(GEN)A[def]);
    }
    if (low_stack(lim, stack_lim(av1,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"nfhermite, i = %ld", i);
      gerepileall(av,3, &A,&I,&J);
    }
  }
  y = cgetg(3,t_VEC);
  A += k-m; A[0] = evaltyp(t_MAT)|evallg(m+1); y[1] = (long)A;
  I += k-m; I[0] = evaltyp(t_VEC)|evallg(m+1); y[2] = (long)I;
  return gerepilecopy(av0, y);
}

/* A torsion module M over Z_K will be given by a row vector [A,I,J] with
 * three components. I=[b_1,...,b_n] is a row vector of k fractional ideals
 * given in HNF, J=[a_1,...,a_n] is a row vector of n fractional ideals in
 * HNF. A is an nxn matrix (same n) such that if A_j is the j-th column of A
 * and e_n is the canonical basis of K^n, then
 * M=(b_1e_1+...+b_ne_n)/(a_1A_1+...a_nA_n) */

/* x=[A,I,J] a torsion module as above. Output the
 * smith normal form as K=[c_1,...,c_n] such that x = Z_K/c_1+...+Z_K/c_n */
GEN
nfsmith(GEN nf, GEN x)
{
  long i, j, k, l, c, n, m, N;
  pari_sp av, lim;
  GEN p1,p3,p4,z,u,v,w,d,dinv,A,I,J;

  nf = checknf(nf); N = degpol(nf[1]);
  if (typ(x)!=t_VEC || lg(x)!=4) err(talker,"not a module in nfsmith");
  A = (GEN)x[1];
  I = (GEN)x[2];
  J = (GEN)x[3];
  if (typ(A)!=t_MAT) err(talker,"not a matrix in nfsmith");
  n = lg(A)-1;
  if (typ(I)!=t_VEC || lg(I)!=n+1 || typ(J)!=t_VEC || lg(J)!=n+1)
    err(talker,"not a correct ideal list in nfsmith");
  if (!n) err(talker,"not a matrix of maximal rank in nfsmith");
  m = lg(A[1])-1;
  if (n < m) err(talker,"not a matrix of maximal rank in nfsmith");
  if (n > m) err(impl,"nfsmith for non square matrices");

  av = avma; lim = stack_lim(av,1);
  A = dummycopy(A);
  I = dummycopy(I);
  J = dummycopy(J);
  for (j=1; j<=n; j++)
    if (typ(I[j])!=t_MAT) I[j]=(long)idealhermite_aux(nf,(GEN)I[j]);
  for (j=1; j<=n; j++)
    if (typ(J[j])!=t_MAT) J[j]=(long)idealhermite_aux(nf,(GEN)J[j]);
  for (i=n; i>=2; i--)
  {
    do
    {
      GEN a, b;
      c = 0;
      for (j=i-1; j>=1; j--)
      {
        GEN S, T, S0, T0 = (GEN)A[j];
	b = (GEN)T0[i]; if (gcmp0(b)) continue;

        S0 = (GEN)A[i]; a = (GEN)S0[i];
        d = nfbezout(nf, a,b, (GEN)J[i],(GEN)J[j], &u,&v,&w,&dinv);
        S = colcomb(nf, u,v, S0,T0);
        T = colcomb(nf, a,gneg(b), T0,S0);
        A[i] = (long)S; A[j] = (long)T;
        J[i] = (long)d; J[j] = (long)w;
      }
      for (j=i-1; j>=1; j--)
      {
        GEN ri, rj;
	b = gcoeff(A,j,i); if (gcmp0(b)) continue;

        a = gcoeff(A,i,i);
        d = nfbezout(nf, a,b, (GEN)I[i],(GEN)I[j], &u,&v,&w,&dinv);
        ri = rowcomb(nf, u,v,       i,j, A, i);
        rj = rowcomb(nf, a,gneg(b), j,i, A, i);
        for (k=1; k<=i; k++) { coeff(A,j,k) = rj[k]; coeff(A,i,k) = ri[k]; }
        I[i] = (long)d; I[j] = (long)w; c = 1;
      }
      if (c) continue;

      b = gcoeff(A,i,i); if (gcmp0(b)) break;
      b = idealmulelt(nf, b, idealmul(nf,(GEN)J[i],(GEN)I[i]));
      for (k=1; k<i; k++)
        for (l=1; l<i; l++)
        {
          p3 = gcoeff(A,k,l);
          if (gcmp0(p3)) continue;

          p4 = idealmulelt(nf, p3, idealmul(nf,(GEN)J[l],(GEN)I[k]));
          if (hnfdivide(b, p4)) continue;

          b = idealdiv(nf,(GEN)I[k],(GEN)I[i]);
          p1 = idealdiv(nf,(GEN)J[i], idealmulelt(nf,p3,(GEN)J[l]));
          p4 = gauss(p4, b);
          l=1; while (l<=N && gcmp1(denom((GEN)p4[l]))) l++;
          if (l>N) err(talker,"bug2 in nfsmith");
          p3 = element_mulvecrow(nf,(GEN)b[l],A,k,i);
          for (l=1; l<=i; l++)
            coeff(A,i,l) = ladd(gcoeff(A,i,l),(GEN)p3[l]);

          k = l = i; c = 1;
        }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if(DEBUGMEM>1) err(warnmem,"nfsmith");
        gerepileall(av,3, &A,&I,&J);
      }
    }
    while (c);
  }
  J[1] = (long)idealmul(nf, gcoeff(A,1,1), (GEN)J[1]);
  z = cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++) z[i] = (long)idealmul(nf,(GEN)I[i],(GEN)J[i]);
  return gerepileupto(av, z);
}

#define trivlift(x) ((typ(x)==t_POLMOD)? (GEN)x[2]: lift_intern(x))

GEN
element_mulmodpr(GEN nf, GEN x, GEN y, GEN modpr)
{
  pari_sp av=avma;
  nf = checknf(nf);
  return gerepileupto(av, nfreducemodpr(nf, element_mul(nf,x,y), modpr));
}

GEN
element_divmodpr(GEN nf, GEN x, GEN y, GEN modpr)
{
  pari_sp av = avma;
  GEN p1;

  nf = checknf(nf);
  p1 = lift_intern(gdiv(gmodulcp(gmul((GEN)nf[7],trivlift(x)), (GEN)nf[1]),
                        gmodulcp(gmul((GEN)nf[7],trivlift(y)), (GEN)nf[1])));
  p1 = algtobasis_i(nf,p1);
  return gerepileupto(av,nfreducemodpr(nf,p1,modpr));
}

GEN
element_invmodpr(GEN nf, GEN y, GEN modpr)
{
  pari_sp av=avma;
  GEN p1;

  p1 = QX_invmod(gmul((GEN)nf[7],trivlift(y)), (GEN)nf[1]);
  p1 = algtobasis_i(nf,p1);
  return gerepileupto(av, nfreducemodpr(nf,p1,modpr));
}

GEN
element_powmodpr(GEN nf,GEN x,GEN k,GEN pr)
{
  pari_sp av=avma;
  GEN z,T,p,modpr;

  nf = checknf(nf);
  modpr = nf_to_ff_init(nf,&pr,&T,&p);
  z = nf_to_ff(nf,x,modpr);
  z = FpXQ_pow(z,k,T,p);
  z = ff_to_nf(z,modpr);
  return gerepilecopy(av, _algtobasis(nf,z));
}

GEN
nfkermodpr(GEN nf, GEN x, GEN pr)
{
  pari_sp av = avma;
  GEN T,p,modpr;

  nf = checknf(nf);
  if (typ(x)!=t_MAT) err(typeer,"nfkermodpr");
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  x = modprM(lift(x), nf, modpr);
  return gerepilecopy(av, modprM_lift(FqM_ker(x,T,p), modpr));
}

GEN
nfsolvemodpr(GEN nf, GEN a, GEN b, GEN pr)
{
  pari_sp av = avma;
  GEN T,p,modpr;

  nf = checknf(nf);
  if (typ(a)!=t_MAT) err(typeer,"nfsolvemodpr");
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  a = modprM(lift(a), nf, modpr);
  b = modprM(lift(b), nf, modpr);
  return gerepilecopy(av, modprM_lift(FqM_gauss(a,b,T,p), modpr));
}

#if 0
GEN
nfsuppl(GEN nf, GEN x, GEN pr)
{
  pari_sp av = avma;
  GEN T,p,modpr;

  nf = checknf(nf);
  if (typ(x)!=t_MAT) err(typeer,"nfkermodpr");
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  x = modprM(lift(x), nf, modpr);
  return gerepilecopy(av, modprM_lift(FqM_suppl(x,T,p), modpr));
}
#endif

/* Given a pseudo-basis x, outputs a multiple of its ideal determinant */
GEN
nfdetint(GEN nf, GEN x)
{
  GEN pass,c,v,det1,piv,pivprec,vi,p1,A,I,id,idprod;
  long i, j, k, rg, n, m, m1, cm=0, N;
  pari_sp av = avma, av1, lim;

  nf = checknf(nf); N = degpol(nf[1]);
  check_ZKmodule(x, "nfdetint");
  A = (GEN)x[1];
  I = (GEN)x[2];
  n = lg(A)-1; if (!n) return gun;

  m1 = lg(A[1]); m = m1-1;
  id = idmat(N);
  c = new_chunk(m1); for (k=1; k<=m; k++) c[k] = 0;
  piv = pivprec = gscalcol_i(gun,N);

  av1 = avma; lim = stack_lim(av1,1);
  det1 = idprod = gzero; /* dummy for gerepilemany */
  pass = cgetg(m1,t_MAT);
  v = cgetg(m1,t_COL);
  for (j=1; j<=m; j++)
  {
    pass[j] = (long)zerocol(m);
    v[j] = zero; /* dummy */
  }
  for (rg=0,k=1; k<=n; k++)
  {
    long t = 0;
    for (i=1; i<=m; i++)
      if (!c[i])
      {
	vi=element_mul(nf,piv,gcoeff(A,i,k));
	for (j=1; j<=m; j++)
	  if (c[j]) vi=gadd(vi,element_mul(nf,gcoeff(pass,i,j),gcoeff(A,j,k)));
	v[i]=(long)vi; if (!t && !gcmp0(vi)) t=i;
      }
    if (t)
    {
      pivprec = piv;
      if (rg == m-1)
      {
        if (!cm)
        {
          cm=1; idprod = id;
          for (i=1; i<=m; i++)
            if (i!=t)
              idprod = (idprod==id)? (GEN)I[c[i]]
                                   : idealmul(nf,idprod,(GEN)I[c[i]]);
        }
        p1 = idealmul(nf,(GEN)v[t],(GEN)I[k]); c[t]=0;
        det1 = (typ(det1)==t_INT)? p1: idealadd(nf,p1,det1);
      }
      else
      {
        rg++; piv=(GEN)v[t]; c[t]=k;
	for (i=1; i<=m; i++)
	  if (!c[i])
          {
	    for (j=1; j<=m; j++)
	      if (c[j] && j!=t)
	      {
		p1=gsub(element_mul(nf,piv,gcoeff(pass,i,j)),
		        element_mul(nf,(GEN)v[i],gcoeff(pass,t,j)));
		coeff(pass,i,j) = rg>1? (long) element_div(nf,p1,pivprec)
		                      : (long) p1;
	      }
            coeff(pass,i,t)=lneg((GEN)v[i]);
          }
      }
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"nfdetint");
      gerepileall(av1,6, &det1,&piv,&pivprec,&pass,&v,&idprod);
    }
  }
  if (!cm) { avma = av; return gscalmat(gzero,N); }
  return gerepileupto(av, idealmul(nf,idprod,det1));
}

/* clean in place (destroy x) */
static void
nfcleanmod(GEN nf, GEN x, long lim, GEN D)
{
  long i;
  GEN c;
  D = lllint_ip(Q_primitive_part(D, &c), 4);
  if (c) D = gmul(D,c);
  for (i=1; i<=lim; i++) x[i] = (long)element_reduce(nf, (GEN)x[i], D);
}

GEN
nfhermitemod(GEN nf, GEN x, GEN detmat)
{
  long li, co, i, j, def, ldef, N;
  pari_sp av0=avma, av, lim;
  GEN d0, w, p1, d, u, v, A, I, J, di, unnf;

  nf = checknf(nf); N = degpol(nf[1]);
  check_ZKmodule(x, "nfhermitemod");
  A = (GEN)x[1];
  I = (GEN)x[2];
  co = lg(A); if (co==1) return cgetg(1,t_MAT);

  li = lg(A[1]);
  unnf = gscalcol(gun,N);
  detmat = lllint_ip(Q_remove_denom(detmat, NULL), 100);

  av = avma; lim = stack_lim(av,2);
  A = matalgtobasis(nf, A);
  I = dummycopy(I);
  def = co; ldef = (li>co)? li-co+1: 1;
  for (i=li-1; i>=ldef; i--)
  {
    def--; j=def; while (j>=1 && gcmp0(gcoeff(A,i,j))) j--;
    if (j==def) j--; else { swap(A[j], A[def]); swap(I[j], I[def]); }
    for (  ; j; j--)
    {
      GEN a, b, S, T, S0, T0 = (GEN)A[j];
      b = (GEN)T0[i]; if (gcmp0(b)) continue;

      S0 = (GEN)A[def]; a = (GEN)S0[i];
      d = nfbezout(nf, a,b, (GEN)I[def],(GEN)I[j], &u,&v,&w,&di);
      S = colcomb(nf, u,v, S0,T0);
      T = colcomb(nf, a,gneg(b), T0,S0);
      if (u != gzero && v != gzero) /* already reduced otherwise */
        nfcleanmod(nf, S, i, idealmul(nf,detmat,di));
      nfcleanmod(nf, T, i, idealdiv(nf,detmat,w));
      A[def] = (long)S; A[j] = (long)T;
      I[def] = (long)d; I[j] = (long)w;
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"[1]: nfhermitemod, i = %ld", i);
      gerepileall(av,2, &A,&I);
    }
  }
  def--; d0 = detmat;
  A += def; A[0] = evaltyp(t_MAT)|evallg(li);
  I += def; I[0] = evaltyp(t_VEC)|evallg(li);
  for (i=li-1; i>=1; i--)
  {
    d = nfbezout(nf, gun,gcoeff(A,i,i), d0,(GEN)I[i], &u,&v,&w,&di);
    p1 = element_mulvec(nf,v,(GEN)A[i]);
    if (i > 1)
    {
      d0 = idealmul(nf,d0,di);
      nfcleanmod(nf, p1, i, d0);
    }
    A[i] = (long)p1; p1[i] = (long)unnf;
    I[i] = (long)d;
  }
  J = cgetg(li,t_VEC); J[1] = zero;
  for (j=2; j<li; j++) J[j] = (long)idealinv(nf,(GEN)I[j]);
  for (i=li-2; i>=1; i--)
  {
    d = (GEN)I[i];
    for (j=i+1; j<li; j++)
    {
      GEN c = element_close(nf, gcoeff(A,i,j), idealmul(nf,d,(GEN)J[j]));
      A[j] = (long)colcomb(nf, gun,gneg(c), (GEN)A[j],(GEN)A[i]);
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"[2]: nfhermitemod, i = %ld", i);
      gerepileall(av,3, &A,&I,&J);
    }
  }
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)A;
  p1[2] = (long)I; return gerepilecopy(av0, p1);
}
