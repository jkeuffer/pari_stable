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

#define principalideal_aux(nf,x) (principalideal0((nf),(x),0))

extern GEN hnfall_i(GEN A, GEN *ptB, long remove);
extern GEN makeprimetoideal(GEN nf,GEN UV,GEN uv,GEN x);
extern GEN gauss_triangle_i(GEN A, GEN B,GEN t);
extern GEN hnf_invimage(GEN A, GEN b);
extern GEN colreducemodHNF(GEN x, GEN y, GEN *Q);
extern GEN zinternallog_pk(GEN nf,GEN a0,GEN y,GEN pr,GEN prk,GEN list,GEN *psigne);
extern GEN special_anti_uniformizer(GEN nf, GEN pr);
extern GEN set_sign_mod_idele(GEN nf, GEN x, GEN y, GEN idele, GEN sarch);
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
  gpmem_t av=avma;
  if (typ(vp) == t_INT) return gscalmat(vp, degpol(nf[1]));
  return gerepileupto(av, prime_to_ideal_aux(nf,vp));
}

/* x = ideal in matrix form. Put it in hnf. */
static GEN
idealmat_to_hnf(GEN nf, GEN x)
{
  long rx,i,j,N;
  GEN m, cx;

  N=degpol(nf[1]); rx=lg(x)-1;
  if (!rx) return gscalmat(gzero,N);

  x = Q_primitive_part(x, &cx);
  if (rx >= N) m = x;
  else
  {
    m=cgetg(rx*N + 1,t_MAT);
    for (i=1; i<=rx; i++)
      for (j=1; j<=N; j++)
        m[(i-1)*N + j] = (long) element_mulid(nf,(GEN)x[i],j);
  }
  x = hnfmod(m, detint(m));
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
    x = principalideal(nf,x);
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
  gpmem_t av=avma;
  GEN p1;
  nf = checknf(nf); p1 = idealhermite_aux(nf,x);
  if (p1==x || p1==(GEN)x[1]) return gcopy(p1);
  return gerepileupto(av,p1);
}

static GEN
principalideal0(GEN nf, GEN x, long copy)
{
  GEN z = cgetg(2,t_MAT);
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      if (copy) x = gcopy(x);
      x = gscalcol_i(x, degpol(nf[1])); break;

    case t_POLMOD:
      x = checknfelt_mod(nf,x,"principalideal");
      /* fall through */
    case t_POL:
      x = copy? algtobasis(nf,x): algtobasis_i(nf,x);
      break;

    case t_MAT:
      if (lg(x)!=2) err(typeer,"principalideal");
      x = (GEN)x[1];
    case t_COL:
      if (lg(x)==lgef(nf[1])-2)
      {
        if (copy) x = gcopy(x);
        break;
      }
    default: err(typeer,"principalideal");
  }
  z[1]=(long)x; return z;
}

GEN
principalideal(GEN nf, GEN x)
{
  nf = checknf(nf); return principalideal0(nf,x,1);
}

static GEN
mylog(GEN x, long prec)
{
  if (gcmp0(x))
    err(precer,"get_arch");
  return glog(x,prec);
}

/* for internal use */
GEN
get_arch(GEN nf,GEN x,long prec)
{
  long i,R1,RU;
  GEN v,p1,p2;

  R1=itos(gmael(nf,2,1)); RU = R1+itos(gmael(nf,2,2));
  if (typ(x)!=t_COL) x = algtobasis_i(nf,x);
  v = cgetg(RU+1,t_VEC);
  if (isnfscalar(x)) /* rational number */
  {
    p1 = glog((GEN)x[1],prec);
    p2 = (RU > R1)? gmul2n(p1,1): NULL;
    for (i=1; i<=R1; i++) v[i]=(long)p1;
    for (   ; i<=RU; i++) v[i]=(long)p2;
  }
  else
  {
    x = gmul(gmael(nf,5,1),x);
    for (i=1; i<=R1; i++) v[i] = (long)mylog((GEN)x[i],prec);
    for (   ; i<=RU; i++) v[i] = lmul2n(mylog((GEN)x[i],prec),1);
  }
  return v;
}

/* as above but return NULL if precision problem, and set *emb to the
 * embeddings of x */
GEN
get_arch_real(GEN nf,GEN x,GEN *emb,long prec)
{
  long i,R1,RU;
  GEN v,p1,p2;

  R1=itos(gmael(nf,2,1)); RU = R1+itos(gmael(nf,2,2));
  if (typ(x)!=t_COL) x = algtobasis_i(nf,x);
  v = cgetg(RU+1,t_COL);
  if (isnfscalar(x)) /* rational number */
  {
    GEN u = (GEN)x[1];
    i = signe(u);
    if (!i) err(talker,"0 in get_arch_real");
    p1= (i > 0)? glog(u,prec): gzero;
    p2 = (RU > R1)? gmul2n(p1,1): NULL;
    for (i=1; i<=R1; i++) v[i]=(long)p1;
    for (   ; i<=RU; i++) v[i]=(long)p2;
  }
  else
  {
    GEN t;
    x = gmul(gmael(nf,5,1),x);
    for (i=1; i<=R1; i++)
    {
      t = gabs((GEN)x[i],prec); if (gcmp0(t)) return NULL;
      v[i] = llog(t,prec);
    }
    for (   ; i<=RU; i++)
    {
      t = gnorm((GEN)x[i]); if (gcmp0(t)) return NULL;
      v[i] = llog(t,prec);
    }
  }
  *emb = x; return v;
}

GEN
principalidele(GEN nf, GEN x, long prec)
{
  GEN p1,y = cgetg(3,t_VEC);
  gpmem_t av;

  nf = checknf(nf);
  p1 = principalideal0(nf,x,1);
  y[1] = (long)p1;
  av =avma; p1 = get_arch(nf,(GEN)p1[1],prec);
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

static GEN
two_to_hnf(GEN nf, GEN a, GEN b)
{
  a = principalideal_aux(nf,a);
  b = principalideal_aux(nf,b);
  a = concatsp(a,b);
  if (lgef(nf[1])==5) /* quadratic field: a has to be turned into idealmat */
    a = idealmul(nf,idmat(2),a);
  return idealmat_to_hnf(nf, a);
}

GEN
idealhnf0(GEN nf, GEN a, GEN b)
{
  gpmem_t av;
  if (!b) return idealhermite(nf,a);

  /* HNF of aZ_K+bZ_K */
  av = avma; nf=checknf(nf);
  return gerepileupto(av, two_to_hnf(nf,a,b));
}

GEN
idealhermite2(GEN nf, GEN a, GEN b)
{
  return idealhnf0(nf,a,b);
}

static int
ok_elt(GEN x, GEN xZ, GEN y)
{
  gpmem_t av = avma;
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
  gpmem_t av,tetpil;

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
    y[1] = lpilecopy(av,cx);
    y[2] = (long)gscalcol(cx, N); return y;
  }
  a = NULL; /* gcc -Wall */
  beta= cgetg(N+1, t_VEC);
  mul = cgetg(N+1, t_VEC); lm = 1; /* = lg(mul) */
  /* look for a in x such that a O/xZ = x O/xZ */
  for (i=2; i<=N; i++)
  {
    GEN t, y = eltmul_get_table(nf, (GEN)x[i]);
    t = gmod(y, xZ);
    if (gcmp0(t)) continue;
    if (ok_elt(x,xZ, t)) { a = (GEN)x[i]; break; }
    beta[lm]= x[i];
    /* mul[i] = { canonical generators for x[i] O/xZ as Z-module } */
    mul[lm] = (long)t; lm++;
  }
  if (i>N)
  {
    GEN z = cgetg(lm, t_VECSMALL);
    gpmem_t av1;
    ulong c = 0;

    setlg(mul, lm);
    setlg(beta,lm);
    if (DEBUGLEVEL>3) fprintferr("ideal_two_elt, hard case: ");
    for(av1=avma;;avma=av1)
    {
      if (DEBUGLEVEL>3) fprintferr("%ld ", ++c);
      for (a=NULL,i=1; i<lm; i++)
      {
        long t = (mymyrand() >> (BITS_IN_RANDOM-5)) - 7; /* in [-7,8] */
        z[i] = t;
        a = addmul_mat(a, t, (GEN)mul[i]);
      }
      /* a = matrix (NOT HNF) of ideal generated by beta.z in O/xZ */
      if (a && ok_elt(x,xZ, a)) break;
    }
    for (a=NULL,i=1; i<lm; i++)
      a = addmul_col(a, z[i], (GEN)beta[i]);
    if (DEBUGLEVEL>3) fprintferr("\n");
  }
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

  nf=checknf(nf);
  if (tx==id_MAT) return mat_ideal_two_elt(nf,x);

  N=degpol(nf[1]); z=cgetg(3,t_VEC);
  if (tx == id_PRINCIPAL)
  {
    switch(typ(x))
    {
      case t_INT: case t_FRAC: case t_FRACN:
        z[1]=lcopy(x);
	z[2]=(long)zerocol(N); return z;

      case t_POLMOD:
        x = checknfelt_mod(nf, x, "ideal_two_elt");
        /* fall through */
      case t_POL:
        z[1]=zero; z[2]=(long)algtobasis(nf,x); return z;
      case t_COL:
        if (lg(x)==N+1) { z[1]=zero; z[2]=lcopy(x); return z; }
    }
  }
  else if (tx == id_PRIME)
  {
    z[1]=lcopy((GEN)x[1]);
    z[2]=lcopy((GEN)x[2]); return z;
  }
  err(typeer,"ideal_two_elt");
  return NULL; /* not reached */
}

/* factorization */

/* x integral ideal in HNF, return v_p(Nx), *vz = v_p(x \cap Z)
 * Use x[i,i] | x[1,1], i > 0 */
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
  gpmem_t av,tetpil;
  long tx,i,j,k,lf,lc,N,l,v,vc,e;
  GEN f,f1,f2,c1,c2,y1,y2,y,p1,p2,cx,P;

  tx = idealtyp(&x,&y);
  if (tx == id_PRIME)
  {
    y=cgetg(3,t_MAT);
    y[1]=(long)_col(gcopy(x));
    y[2]=(long)_col(gun); return y;
  }
  nf=checknf(nf); av=avma;
  if (tx == id_PRINCIPAL) x = principalideal_aux(nf,x);

  N=degpol(nf[1]); if (lg(x) != N+1) x = idealmat_to_hnf(nf,x);
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
  y1 = cgetg((lf+lc-2)*N+1,t_COL);
  y2 = cgetg((lf+lc-2)*N+1,t_VECSMALL);
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
  tetpil=avma; y=cgetg(3,t_MAT);
  p1=cgetg(k,t_COL); y[1]=(long)p1;
  p2=cgetg(k,t_COL); y[2]=(long)p2;
  for (i=1; i<k; i++) { p1[i]=lcopy((GEN)y1[i]); p2[i]=lstoi(y2[i]); }
  y = gerepile(av,tetpil,y);
  return sort_factor_gen(y, cmp_prime_ideal);
}

/* P prime ideal in primedec format. Return valuation(ix) at P */
long
idealval(GEN nf, GEN ix, GEN P)
{
  gpmem_t av=avma,av1,lim;
  long N,v,vd,w,e,f,i,j,k, tx = typ(ix);
  GEN mul,mat,a,x,y,r,bp,p,pk,cx;

  nf=checknf(nf); checkprimeid(P);
  if (is_extscalar_t(tx) || tx==t_COL) return element_val(nf,ix,P);
  p=(GEN)P[1]; N=degpol(nf[1]);
  tx = idealtyp(&ix,&a);
  ix = Q_primitive_part(ix, &cx);
  if (tx != id_MAT)
    ix = idealhermite_aux(nf,ix);
  else
  {
    checkid(ix,N);
    if (lg(ix) != N+1) ix=idealmat_to_hnf(nf,ix);
  }
  e = itos((GEN)P[3]);
  f = itos((GEN)P[4]);
  /* 0 <= v_P(ix) <= floor[v_p(Nix) / f] */
  i = val_norm(ix,p, &k) / f;
  /* 0 <= ceil[v_P(ix) / e] <= v_p(ix \cap Z) --> v_P <= e * v_p */
  j = k * e;
  v = min(i,j); /* v_P(ix) <= v */
  vd = cx? ggval(cx,p) * e: 0;
  if (!v) { avma = av; return vd; }

  mul = cgetg(N+1,t_MAT); bp=(GEN)P[5];
  mat = cgetg(N+1,t_MAT);
  for (j=1; j<=N; j++)
  {
    mul[j] = (long)element_mulid(nf,bp,j);
    x = (GEN)ix[j];
    y = cgetg(N+1, t_COL); mat[j] = (long)y;
    for (i=1; i<=N; i++)
    { /* compute (x.b)_i, ix in HNF ==> x[j+1..N] = 0 */
      a = mulii((GEN)x[1], gcoeff(mul,i,1));
      for (k=2; k<=j; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
      /* is it divisible by p ? */
      y[i] = ldvmdii(a,p,&r);
      if (signe(r)) { avma = av; return vd; }
    }
  }
  pk = gpowgs(p, v-1);
  av1 = avma; lim=stack_lim(av1,3);
  y = cgetg(N+1,t_COL);
  /* can compute mod p^(v-w) */
  for (w=1; w<v; w++)
  {
    for (j=1; j<=N; j++)
    {
      x = (GEN)mat[j];
      for (i=1; i<=N; i++)
      { /* compute (x.b)_i */
        a = mulii((GEN)x[1], gcoeff(mul,i,1));
        for (k=2; k<=N; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
        /* is it divisible by p ? */
        y[i] = ldvmdii(a,p,&r);
        if (signe(r)) { avma = av; return w + vd; }
        if (lgefint(y[i]) > lgefint(pk)) y[i] = lresii((GEN)y[i], pk);
      }
      r=x; mat[j]=(long)y; y=r;
      if (low_stack(lim,stack_lim(av1,3)))
      {
        GEN *gptr[3]; gptr[0]=&y; gptr[1]=&mat; gptr[2]=&pk;
	if(DEBUGMEM>1) err(warnmem,"idealval");
        gerepilemany(av1,gptr,3);
      }
    }
    pk = gdivexact(pk,p);
  }
  avma = av; return w + vd;
}

/* gcd and generalized Bezout */

GEN
idealadd(GEN nf, GEN x, GEN y)
{
  gpmem_t av=avma;
  long N,tx,ty;
  GEN z,p1,dx,dy,dz;
  int modid;

  tx = idealtyp(&x,&z);
  ty = idealtyp(&y,&z);
  nf=checknf(nf); N=degpol(nf[1]);
  z = cgetg(N+1, t_MAT);
  if (tx != id_MAT || lg(x)!=N+1) x = idealhermite_aux(nf,x);
  if (ty != id_MAT || lg(y)!=N+1) y = idealhermite_aux(nf,y);
  if (lg(x) == 1) return gerepileupto(av,y);
  if (lg(y) == 1) return gerepileupto(av,x); /* check for 0 ideal */
  dx=denom(x);
  dy=denom(y); dz=mulii(dx,dy);
  if (gcmp1(dz)) dz = NULL; else {
    x = Q_remove_denom(x, dz);
    y = Q_remove_denom(y, dz);
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
    long i,j;
    if (!dz) { avma=av; return idmat(N); }
    avma = (gpmem_t)dz; dz = gerepileupto((gpmem_t)z, ginv(dz));
    for (i=1; i<=N; i++)
    {
      z[i]=lgetg(N+1,t_COL);
      for (j=1; j<=N; j++)
        coeff(z,j,i) = (i==j)? (long)dz: zero;
    }
    return z;
  }
  z = concatsp(x,y);
  z = modid? hnfmodid(z,p1): hnfmod(z, p1);
  if (dz) z=gdiv(z,dz);
  return gerepileupto(av,z);
}

/* assume x,y integral non zero */
static GEN
addone_aux2(GEN nf, GEN x, GEN y)
{
  GEN U, H;
  long i, l;

  H = hnfall_i(concatsp(x,y), &U, 1);
  l = lg(H);
  for (i=1; i<l; i++)
    if (!gcmp1(gcoeff(H,i,i)))
      err(talker,"ideals don't sum to Z_K in idealaddtoone");
  U = (GEN)U[l]; setlg(U, lg(x));
  return gmul(x, U);
}

/* assume x,y integral, non zero in HNF */
static GEN
addone_aux(GEN nf, GEN x, GEN y)
{
  GEN a, b, u, v;

  a = gcoeff(x,1,1);
  b = gcoeff(y,1,1);
  if (typ(a) != t_INT || typ(b) != t_INT)
    err(talker,"ideals don't sum to Z_K in idealaddtoone");
  if (gcmp1(bezout(a,b,&u,&v)))
    return gmul(u,(GEN)x[1]);
  return addone_aux2(nf, x, y);
}

GEN
idealaddtoone_i(GEN nf, GEN x, GEN y)
{
  long t, fl = 1;
  GEN p1,xh,yh;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entering idealaddtoone:\n");
    fprintferr(" x = %Z\n",x);
    fprintferr(" y = %Z\n",y);
  }
  t = idealtyp(&x,&p1);
  if (t != id_MAT || lg(x) == 1 || lg(x) != lg(x[1]))
    xh = idealhermite_aux(nf,x);
  else
    { xh = x; fl = isnfscalar((GEN)x[1]); }
  t = idealtyp(&y,&p1);
  if (t != id_MAT || lg(y) == 1 || lg(y) != lg(y[1]))
    yh = idealhermite_aux(nf,y);
  else
    { yh = y; if (fl) fl = isnfscalar((GEN)y[1]); }
  if (lg(xh) == 1)
  {
    if (lg(yh) == 1 || !gcmp1(gabs(gcoeff(yh,1,1),0)))
      err(talker,"ideals don't sum to Z_K in idealaddtoone");
    return algtobasis(nf, gzero);
  }
  if (lg(yh) == 1)
  {
    p1 = gcoeff(xh,1,1);
    if (!gcmp1(gabs(p1,0)))
      err(talker,"ideals don't sum to Z_K in idealaddtoone");
    return algtobasis(nf, gneg(p1));
  }

  if (fl) p1 = addone_aux(nf, xh,yh); /* xh[1], yh[1] scalar */
  else    p1 = addone_aux2(nf,xh,yh);
  p1 = element_reduce(nf,p1, idealmullll(nf,x,y));
  if (DEBUGLEVEL>4 && !gcmp0(p1))
    fprintferr(" leaving idealaddtoone: %Z\n",p1);
  return p1;
}

/* ideal should be an idele (not mandatory). For internal use. */
GEN
ideleaddone_aux(GEN nf,GEN x,GEN ideal)
{
  long i,nba,R1;
  GEN p1,p2,p3,arch;

  (void)idealtyp(&ideal,&arch);
  if (!arch) return idealaddtoone_i(nf,x,ideal);

  R1=itos(gmael(nf,2,1));
  if (typ(arch)!=t_VEC && lg(arch)!=R1+1)
    err(talker,"incorrect idele in idealaddtoone");
  for (nba=0,i=1; i<lg(arch); i++)
    if (signe(arch[i])) nba++;
  if (!nba) return idealaddtoone_i(nf,x,ideal);

  p3 = idealaddtoone_i(nf,x,ideal);
  if (gcmp0(p3)) p3=(GEN)idealhermite_aux(nf,x)[1];
  p1=idealmullll(nf,x,ideal);

  p2=zarchstar(nf,p1,arch,nba);
  p1=lift_intern(gmul((GEN)p2[3],zsigne(nf,p3,arch)));
  p2=(GEN)p2[2]; nba=0;
  for (i=1; i<lg(p1); i++)
    if (signe(p1[i])) { nba=1; p3=element_mul(nf,p3,(GEN)p2[i]); }
  if (gcmp0(p3)) return gcopy((GEN)x[1]); /* can happen if ideal = Z_K */
  return nba? p3: gcopy(p3);
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
  GEN z = cgetg(3,t_VEC);
  gpmem_t av=avma;

  nf=checknf(nf); x = gerepileupto(av, f(nf,x,y));
  z[1]=(long)x; z[2]=(long)unnf_minus_x(x); return z;
}

/* assume x,y HNF, non-zero */
static GEN
addone_nored(GEN nf, GEN x, GEN y)
{
  return addone(addone_aux, nf,x,y);
}

GEN
idealaddtoone(GEN nf, GEN x, GEN y)
{
  return addone(idealaddtoone_i,nf,x,y);
}

GEN
ideleaddone(GEN nf,GEN x,GEN idele)
{
  return addone(ideleaddone_aux,nf,x,idele);
}

/* given an element x in Z_K and an integral ideal y with x, y coprime,
   outputs an element inverse of x modulo y */
GEN
element_invmodideal(GEN nf, GEN x, GEN y)
{
  gpmem_t av=avma;
  long N,i, fl = 1;
  GEN v,p1,xh,yh;

  nf=checknf(nf); N=degpol(nf[1]);
  if (gcmp1(gcoeff(y,1,1))) return zerocol(N);
  i = lg(y);
  if (typ(y)!=t_MAT || i==1 || i != lg(y[1])) yh=idealhermite_aux(nf,y);
  else
    { yh=y; fl = isnfscalar((GEN)y[1]); }
  switch (typ(x))
  {
    case t_POL: case t_POLMOD: case t_COL:
      xh = idealhermite_aux(nf,x); break;
    default: err(typeer,"element_invmodideal");
      return NULL; /* not reached */
  }
  if (fl) p1 = addone_aux(nf, xh,yh);
  else    p1 = addone_aux2(nf,xh,yh);
  p1 = element_div(nf,p1,x);
  v = gerepileupto(av, nfreducemodideal(nf,p1,y));
  return v;
}

GEN
idealaddmultoone(GEN nf, GEN list)
{
  gpmem_t av=avma,tetpil;
  long N,i,i1,j,k;
  GEN z,v,v1,v2,v3,p1;

  nf=checknf(nf); N=degpol(nf[1]);
  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans idealaddmultoone() :\n");
    fprintferr(" list = "); outerr(list);
  }
  if (typ(list)!=t_VEC && typ(list)!=t_COL)
    err(talker,"not a list in idealaddmultoone");
  k=lg(list); z=cgetg(1,t_MAT); list = dummycopy(list);
  if (k==1) err(talker,"ideals don't sum to Z_K in idealaddmultoone");
  for (i=1; i<k; i++)
  {
    p1=(GEN)list[i];
    if (typ(p1)!=t_MAT || lg(p1)!=lg(p1[1]))
      list[i] = (long)idealhermite_aux(nf,p1);
    z = concatsp(z,(GEN)list[i]);
  }
  v=hnfperm(z); v1=(GEN)v[1]; v2=(GEN)v[2]; v3=(GEN)v[3]; j=0;
  for (i=1; i<=N; i++)
  {
    if (!gcmp1(gcoeff(v1,i,i)))
      err(talker,"ideals don't sum to Z_K in idealaddmultoone");
    if (gcmp1((GEN)v3[i])) j=i;
  }

  v=(GEN)v2[(k-2)*N+j]; z=cgetg(k,t_VEC);
  for (i=1; i<k; i++)
  {
    p1=cgetg(N+1,t_COL); z[i]=(long)p1;
    for (i1=1; i1<=N; i1++) p1[i1]=v[(i-1)*N+i1];
  }
  tetpil=avma; v=cgetg(k,typ(list));
  for (i=1; i<k; i++) v[i]=lmul((GEN)list[i],(GEN)z[i]);
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de idealaddmultoone v = "); outerr(v); }
  return gerepile(av,tetpil,v);
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

static GEN
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
    h[1] = (long)concat((GEN)f[1], x);
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
static GEN
famat_inv(GEN f)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  h = cgetg(3,t_MAT);
  h[1] = lcopy((GEN)f[1]);
  h[2] = lneg((GEN)f[2]);
  return h;
}
static GEN
famat_pow(GEN f, GEN n)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
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
    return tx == t_POL? cmp_pol(x,y): lexcmp(x,y);
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
  F = cgetg(3, t_MAT);
  setlg(G, k); F[1] = (long)G;
  setlg(E, k); F[2] = (long)E; return F;
}

GEN
to_famat(GEN g, GEN e)
{
  GEN h = cgetg(3,t_MAT);
  h[1] = (long)g;
  h[2] = (long)e; return h;
}

GEN
to_famat_all(GEN x, GEN y) { return to_famat(_col(x), _col(y)); }

/* assume (num(g[i]), id) = 1 and for all i. return prod g[i]^e[i] mod id */
GEN
famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id)
{
  GEN t = NULL, ch,h,n,z,idZ = gcoeff(id,1,1);
  long i, lx = lg(g);
  if (is_pm1(idZ)) lx = 1; /* id = Z_K */
  for (i=1; i<lx; i++)
  {
    n = (GEN)e[i]; if (!signe(n)) continue;
    h = (GEN)g[i]; ch = denom(h);
    if (!is_pm1(ch))
    {
      h = gmul(h,ch); ch = mpinvmod(ch,idZ);
      h = gmod(gmul(h,ch), idZ);
    }
    z = element_powmodideal(nf, h, n, id);
    t = (t == NULL)? z: element_mulmodideal(nf, t, z, id);
  }
  return t? t: gscalcol(gun, lg(id)-1);
}

/* assume prh has degree 1 and coprime to numerator(x) */
GEN
nf_to_Fp_simple(GEN x, GEN prh)
{
  GEN ch = denom(x), p = gcoeff(prh,1,1);
  if (!is_pm1(ch))
  {
    x = gmul(gmul(x,ch), mpinvmod(ch,p));
  }
  ch = colreducemodHNF(gmod(x, p), prh, NULL);
  return (GEN)ch[1]; /* in Fp^* */
}

GEN
famat_to_Fp_simple(GEN nf, GEN g, GEN e, GEN prh)
{
  GEN t = gun, h,n, p = gcoeff(prh,1,1), q = subis(p,1);
  long i, th, lx = lg(g);
  for (i=1; i<lx; i++)
  {
    n = (GEN)e[i]; n = modii(n,q);
    if (!signe(n)) continue;
    h = (GEN)g[i]; th = typ(h);
    if (th == t_POL || th == t_POLMOD) h = algtobasis(nf, h);
    if (th != t_COL) h = gmod(h, p); else h = nf_to_Fp_simple(h, prh);
    t = mulii(t, powmodulo(h, n, p)); /* not worth reducing */
  }
  return modii(t, p);
}

/* cf famat_to_nf_modideal_coprime, but id is a prime of degree 1 (=prh) */
GEN
to_Fp_simple(GEN nf, GEN x, GEN prh)
{
  switch(typ(x))
  {
    case t_COL: return nf_to_Fp_simple(x,prh);
    case t_MAT: return famat_to_Fp_simple(nf,(GEN)x[1],(GEN)x[2],prh);
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
 * EX = exponent of (O_K / pr^k)^* used to reduce the product in case the
 * e[i] are large */
static GEN
famat_makecoprime(GEN nf, GEN g, GEN e, GEN pr, GEN prk, GEN EX)
{
  long i,k, l = lg(g);
  GEN prkZ,cx,x,u, zpow = gzero, p = (GEN)pr[1], b = (GEN)pr[5];
  GEN mul = eltmul_get_table(nf, b);
  GEN newg = cgetg(l+1, t_VEC); /* room for z */

  prkZ = gcoeff(prk, 1,1);
  for (i=1; i < l; i++)
  {
    x = (GEN)g[i];
    if (typ(x) != t_COL) x = algtobasis(nf, x);
    cx = denom(x); x = gmul(x,cx);
    k = pvaluation(cx, p, &u);
    if (!gcmp1(u)) /* could avoid the inversion, but prkZ is small--> cheap */
      x = gmul(x, mpinvmod(u, prkZ));
    if (k)
      zpow = addii(zpow, mulsi(k, (GEN)e[i]));
    (void)int_elt_val(nf, x, p, mul, &x);
    newg[i] = (long)colreducemodHNF(x, prk, NULL);
  }
  if (zpow == gzero) setlg(newg, l);
  else
  {
    newg[i] = (long)FpV_red(special_anti_uniformizer(nf, pr), prkZ);
    e = concatsp(e, negi(zpow));
  }
  e = gmod(e, EX);
  return famat_to_nf_modideal_coprime(nf, newg, e, prk);
}

GEN
famat_ideallog(GEN nf, GEN g, GEN e, GEN bid)
{
  gpmem_t av = avma;
  GEN vp = gmael(bid, 3,1), ep = gmael(bid, 3,2), arch = gmael(bid,1,2);
  GEN cyc = gmael(bid,2,2), list_set = (GEN)bid[4], U = (GEN)bid[5];
  GEN p1,y0,x,y, psigne;
  long i;
  if (lg(cyc) == 1) return cgetg(1,t_COL);
  y0 = y = cgetg(lg(U), t_COL);
  psigne = zsigne(nf, to_famat(g,e), arch);
  for (i=1; i<lg(vp); i++)
  {
    GEN pr = (GEN)vp[i], prk;
    prk = idealpow(nf, pr, (GEN)ep[i]);
    /* TODO: FIX group exponent (should be mod prk, not f !) */
    x = famat_makecoprime(nf, g, e, pr, prk, (GEN)cyc[1]);
    y = zinternallog_pk(nf, x, y, pr, prk, (GEN)list_set[i], &psigne);
  }
  p1 = lift_intern(gmul(gmael(list_set,i,3), psigne));
  for (i=1; i<lg(p1); i++) *++y = p1[i];
  y = gmul(U,y0);
  avma = av; x = cgetg(lg(y), t_COL);
  for (i=1; i<lg(y); i++)
    x[i] = lmodii((GEN)y[i], (GEN)cyc[i]);
  return x;
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
    t = famat_to_nf_modideal_coprime(nf,g, gmod(e,EX), id);
  }
  if (!t) t = gun;
  return set_sign_mod_idele(nf, to_famat(g,e), t, module, sarch);
}

GEN
famat_to_arch(GEN nf, GEN fa, long prec)
{
  GEN g,e, y = NULL;
  long i,l;

  if (lg(fa) == 1) return zerovec(lg(nf[6])-1);
  g = (GEN)fa[1];
  e = (GEN)fa[2]; l = lg(e);
  for (i=1; i<l; i++)
  {
    GEN t, x = (GEN)g[i];
    if (typ(x) != t_COL) x = algtobasis(nf,x);
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

/* output the ideal product ix.iy (don't reduce) */
GEN
idealmul(GEN nf, GEN x, GEN y)
{
  gpmem_t av;
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
          p1 = gmul((GEN)y[1],x);
          p1 = two_to_hnf(nf,p1, element_mul(nf,(GEN)y[2],x));
          break;
        default: /* id_MAT */
          p1 = idealmat_mul(nf,y, principalideal_aux(nf,x));
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
  gpmem_t av = avma,tetpil;
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
  tetpil=avma; return gerepile(av,tetpil,gabs(x,0));
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
  GEN J, dI = denom(I), IZ,dual;

  if (gcmp1(dI)) dI = NULL; else I = Q_remove_denom(I, dI);
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
  gpmem_t av=avma;
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
  gpmem_t av;
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

GEN
init_idele(GEN nf)
{
  GEN x = cgetg(3,t_VEC);
  long RU;
  nf = checknf(nf); RU = lg(nf[6])-1;
  x[2] = (long)zerovec(RU); return x;
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
  gpmem_t av=avma;
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
  gpmem_t av = avma;
  return gerepileupto(av, _idealmulred(nf,x,y,prec));
}

long
isideal(GEN nf,GEN x)
{
  gpmem_t av;
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

  av = avma;
  if (lx-1 != N) x = idealmat_to_hnf(nf,x);
  x = primpart(x);

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
  gpmem_t av=avma,tetpil;
  GEN z=idealinv(nf,y);

  tetpil=avma; return gerepile(av,tetpil,idealmul(nf,x,z));
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
  gpmem_t av = avma;
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
  gpmem_t av=avma;
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

static GEN
computet2twist(GEN nf, GEN vdir)
{
  long j, ru = lg(nf[6]);
  GEN p1,MC, mat = (GEN)nf[5];

  if (!vdir) return (GEN)mat[3];
  MC=(GEN)mat[2]; p1=cgetg(ru,t_MAT);
  for (j=1; j<ru; j++)
  {
    GEN v = (GEN)vdir[j];
    if (gcmp0(v))
      p1[j] = MC[j];
    else if (typ(v) == t_INT)
      p1[j] = lmul2n((GEN)MC[j],itos(v)<<1);
    else
      p1[j] = lmul((GEN)MC[j],powgi(stoi(4),v));
  }
  return mulmat_real(p1,(GEN)mat[1]);
}

static GEN
chk_vdir(GEN nf, GEN vdir)
{
  if (!vdir || gcmp0(vdir)) return NULL;
  if (typ(vdir)!=t_VEC || lg(vdir) != lg(nf[6])) err(idealer5);
  return vdir;
}

/* assume I in NxN matrix form (not necessarily HNF) */
static GEN
ideallllred_elt_i(GEN *ptnf, GEN I, GEN vdir, long *ptprec)
{
  GEN T2, u, y, nf = *ptnf;
  long i, e, prec = *ptprec;

  for (i=1; ; i++)
  {
    T2 = computet2twist(nf,vdir);
    y = qf_base_change(T2,I,1);
    e = 1 + (gexpo(y)>>TWOPOTBITS_IN_LONG);
    if (e < 0) e = 0;
    u = lllgramintern(y,100,1, e + prec);
    if (u) break;

    if (i == MAXITERPOL) err(accurer,"ideallllred");
    prec = (prec<<1)-2;
    if (DEBUGLEVEL) err(warnprec,"ideallllred",prec);
    nf = nfnewprec(nf, (e>>1)+prec);
  }
  *ptprec = prec;
  *ptnf = nf;
  return gmul(I, (GEN)u[1]); /* small elt in I */
}

GEN
ideallllred_elt(GEN nf, GEN I)
{
  long prec = DEFAULTPREC;
  return ideallllred_elt_i(&nf, I, NULL, &prec);
}

GEN
ideallllred(GEN nf, GEN I, GEN vdir, long prec)
{
  gpmem_t av = avma;
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
  y = ideallllred_elt_i(&nf, Ired, chk_vdir(nf,vdir), &prec);

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
    case t_POLMOD: case t_MAT: /* compute y, I0 = J y */
      if (!Nx) y = c1;
      else
      {
        c = mul_content(c,c1);
        y = c? gmul(x, gdiv(c,Nx)): gdiv(x, Nx);
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
  gpmem_t av = avma;
  long N, tx;
  GEN p1,y;

  nf = checknf(nf);
  vdir = chk_vdir(nf,vdir);
  N = degpol(nf[1]);
  tx = idealtyp(&x,&y);
  if (tx == id_PRINCIPAL) return gcopy(x);
  if (tx != id_MAT || lg(x) != N+1) x = idealhermite_aux(nf,x);

  p1 = computet2twist(nf,vdir);
  y = qf_base_change(p1,x,0);
  y = gmul(x, (GEN)lllgram(y,prec)[1]);
  return gerepileupto(av, principalidele(nf,y,prec));
}

/*******************************************************************/
/*                                                                 */
/*                   APPROXIMATION THEOREM                         */
/*                                                                 */
/*******************************************************************/

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

/* compute anti-uniformizer for pr, coprime to f outside of pr, integral
 * outside of p below pr.
 * sqf = product or primes dividing f, NULL if f a prime power*/
GEN
anti_unif_mod_f(GEN nf, GEN pr, GEN sqf)
{
  GEN U, V, UV, uv, cx, t, p = (GEN)pr[1];
  if (!sqf) return gdiv((GEN)pr[5], p);
  else
  {
    U = idealpow(nf,pr,gdeux);
    V = idealdivpowprime(nf,sqf,pr,gun);
    uv = addone_nored(nf, U, V);
    UV = idealmul(nf,sqf,pr);
    t = (GEN)pr[2];
    t = makeprimetoideal(nf, UV, uv, t); /* cf unif_mod_f */

    t = element_inv(nf, t);
    t = primitive_part(t, &cx);
    cx = gmod(gmul(cx,p), gcoeff(sqf,1,1)); /* mod (sqf \cap Z) = VZ * p */
    t = gdiv(colreducemodHNF(gmul(cx,t), gmul(p,V), NULL), p);
    return t; /* v_pr[i](t) = -1, v_pr[j](t) = 0 if i != j */
  }
}

/* compute integral uniformizer for pr, coprime to f outside of pr.
 * sqf = product or primes dividing f, NULL if f a prime power*/
GEN
unif_mod_f(GEN nf, GEN pr, GEN sqf)
{
  GEN U, V, UV, uv, t = (GEN)pr[2];
  if (!sqf) return t;
  else
  {
    U = idealpow(nf,pr,gdeux);
    V = idealdivpowprime(nf,sqf,pr,gun);
    uv = addone_nored(nf, U, V);
    UV = idealmulprime(nf,sqf,pr);
    return makeprimetoideal(nf, UV, uv, t);
  }
}

static GEN
appr_reduce(GEN s, GEN y)
{
  long i, N = lg(y)-1;
  GEN d, u, z = cgetg(N+2,t_MAT);

  s = gmod(s, gcoeff(y,1,1));
  y = lllint_ip(y,100);
  for (i=1; i<=N; i++) z[i] = y[i];
  z[N+1] = (long)s;
  u = (GEN)ker(z)[1];
  d = denom(u);
  if (!gcmp1(d)) u = Q_remove_denom(u, d);
  d = (GEN)u[N+1]; setlg(u,N+1);
  for (i=1; i<=N; i++) u[i] = (long)diviiround((GEN)u[i],d);
  return gadd(s, gmul(y,u));
}

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
nf_coprime_part(GEN nf, GEN x, GEN f, GEN *listpr)
{
  long v, j, lp = lg(listpr), N = degpol(nf[1]);
  GEN x1, x2, ex, p, pr;

#if 0 /*1) via many gcds. Expensive ! */
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

/* L0 in K^*. 
 * If ptd1 == NULL, assume (L0,f) = 1
 *   return L integral, L0 = L mod f 
 *
 * Otherwise, assume v_pr(L0) <= 0 for all pr | f and set *ptd1 = d1
 *   return L integral, L0 = L/d1 mod f, and such that 
 *   if (L*I,f) = 1 for some integral I, then d1 | L*I  */
GEN
make_integral(GEN nf, GEN L0, GEN f, GEN *listpr, GEN *ptd1)
{
  GEN fZ, t, L, D2, d1, d2, d = denom(L0);

  if (ptd1) *ptd1 = NULL;

  if (is_pm1(d)) return L0;
  
  L = Q_remove_denom(L0, d); /* L0 = L / d, L integral */
  fZ = gcoeff(f,1,1);
  /* Kill denom part coprime to fZ */
  d2 = coprime_part(d, fZ);
  t = mpinvmod(d2, fZ); if (!is_pm1(t)) L = gmul(L,t);
  if (egalii(d, d2)) return L;

  d1 = diviiexact(d, d2);
  /* L0 = (L / d1) mod f. d1 not coprime to f
   * write (d1) = D1 D2, D2 minimal, (D2,f) = 1. */
  D2 = nf_coprime_part(nf, d1, f, listpr);
  t = idealaddtoone_i(nf, D2, f); /* in D2, 1 mod f */
  L = element_muli(nf,t,L);

  /* if (L0, f) = 1, then L in D1 ==> in D1 D2 = (d1) */
  if (!ptd1) return Q_div_to_int(L, d1); /* exact division */

  *ptd1 = d1; return L;
}

/* Given a prime ideal factorization with possibly zero or negative
 * exponents, gives b such that v_p(b) = v_p(x) for all prime ideals pr | x
 * and v_pr(b)> = 0 for all other pr.
 * For optimal performance, all [anti-]uniformizers should be precomputed,
 * but no support for this yet.
 * No garbage collecting */
GEN
idealapprfact_i(GEN nf, GEN x)
{
  gpmem_t av = avma;
  GEN tau, pi, z, d, sqf, sqfsafe, list, e, e2;
  long s, flag, i, r, N;

  nf = checknf(nf);
  if (typ(x) != t_MAT || lg(x) != 3)
    err(talker,"not a prime ideal factorization in idealapprfact");
  if (DEBUGLEVEL>4) {
    fprintferr(" entering idealapprfact() :\n");
    fprintferr(" x = %Z\n", x);
  }
  list= (GEN)x[1];
  e   = (GEN)x[2]; r = lg(e); N = degpol(nf[1]);
  if (r==1) return gscalcol_i(gun, N);

  sqf = (r == 2)? NULL: idealprodprime(nf, list);
  sqfsafe = NULL;
  z = gun; flag = 0;
  for (i=1; i<r; i++)
  {
    s = signe(e[i]);
    if (s < 0)
    {
      flag = 1;
      if (!sqfsafe) sqfsafe = sqf? sqf: prime_to_ideal(nf, (GEN)list[1]);
      tau = anti_unif_mod_f(nf, (GEN)list[i], sqf);
      tau = make_integral(nf, tau, sqfsafe, (GEN*)list, &d);
      tau = gdiv(tau, d);
      z = element_mul(nf, z, element_pow(nf, tau, negi((GEN)e[i])));
    }
    else if (s > 0)
    {
      pi = unif_mod_f(nf, (GEN)list[i], sqf);
      z = element_mul(nf, z, element_pow(nf, pi, (GEN)e[i]));
    }
  }
  if (z == gun) { avma = av; return gscalcol_i(gun, N); }
  e2 = cgetg(r, t_VEC);
  for (i=1; i<r; i++) e2[i] = laddis((GEN)e[i], 1);
  x = factorbackprime(nf, list,e2);
  if (flag) /* denominator */
  {
    d = denom(z); z = Q_remove_denom(z, d);
    x = Q_remove_denom(x, d);
  }
  else d = NULL;
  z = appr_reduce(z, x);
  if (d) z = gdiv(z, d);
  return z;
}

GEN
idealapprfact(GEN nf, GEN x) {
  gpmem_t av = avma;
  return gerepileupto(av, idealapprfact_i(nf, x));
}

GEN
idealappr(GEN nf, GEN x) {
  gpmem_t av = avma;
  return gerepileupto(av, idealapprfact_i(nf, idealfactor(nf, x)));
}

GEN
idealappr0(GEN nf, GEN x, long fl) {
  return fl? idealapprfact(nf, x): idealappr(nf, x);
}

/* Given a prime ideal factorization x with possibly zero or negative exponents,
 * and a vector w of elements of nf, gives a b such that
 * v_p(b-w_p)>=v_p(x) for all prime ideals p in the ideal factorization
 * and v_p(b)>=0 for all other p, using the (standard) proof given in GTM 138.
 * Certainly not the most efficient, but sure. */
GEN
idealchinese(GEN nf, GEN x, GEN w)
{
  gpmem_t av = avma;
  long ty = typ(w), i,N,r;
  GEN L,e,z,t,y,v,s,den;

  nf=checknf(nf); N=degpol(nf[1]);
  if (typ(x) != t_MAT || lg(x) != 3)
    err(talker,"not a prime ideal factorization in idealchinese");
  L = (GEN)x[1]; r = lg(L);
  e = (GEN)x[2];
  if (!is_vec_t(ty) || lg(w) != r)
    err(talker,"not a suitable vector of elements in idealchinese");
  if (r==1) return gscalcol_i(gun,N);

  den = denom(w);
  if (!gcmp1(den))
  {
    GEN fa = famat_reduce(famat_mul(x, idealfactor(nf,den)));
    L = (GEN)fa[1]; r = lg(L);
    e = (GEN)fa[2];
  }
  for (i=1; i<r; i++)
    if (signe(e[i]) < 0) e[i] = zero;

  y = factorbackprime(nf, L, e);
  z = cgetg(r,t_VEC);
  for (i=1; i<r; i++)
    z[i] = (long)idealdivpowprime(nf,y, (GEN)L[i], (GEN)e[i]);
  v = idealaddmultoone(nf,z); s = NULL;
  for (i=1; i<r; i++)
  {
    t = element_mul(nf, (GEN)v[i], (GEN)w[i]);
    s = s? gadd(s,t): t;
  }
  return gerepileupto(av, appr_reduce(s,y));
}

static GEN
mat_ideal_two_elt2(GEN nf, GEN x, GEN a)
{
  GEN L, e, fact = idealfactor(nf,a);
  long i, r;
  L = (GEN)fact[1]; r = lg(L);
  e = (GEN)fact[2];
  for (i=1; i<r; i++) e[i] = lstoi( idealval(nf,x,(GEN)L[i]) );
  return centermod(idealapprfact_i(nf,fact), gcoeff(x,1,1));
}

/* Given an integral ideal x and a in x, gives a b such that
 * x = aZ_K + bZ_K using the approximation theorem */
GEN
ideal_two_elt2(GEN nf, GEN x, GEN a)
{
  gpmem_t av = avma;
  GEN cx, b;

  nf = checknf(nf);
  if (typ(a) != t_COL) a = algtobasis(nf, a);
  x = idealhermite_aux(nf,x);
  if (gcmp0(x))
  {
    if (!gcmp0(a)) err(talker,"element not in ideal in ideal_two_elt2");
    avma=av; return gcopy(a);
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
  gpmem_t av = avma;
  long i, r;
  GEN list, ep, fact = idealfactor(nf,y);

  list = (GEN)fact[1];
  ep   = (GEN)fact[2]; r = lg(ep);
  for (i=1; i<r; i++) ep[i] = lstoi(-idealval(nf,x,(GEN)list[i]));
  return gerepileupto(av, idealapprfact_i(nf,fact));
}

/*******************************************************************/
/*                                                                 */
/*                  LINEAR ALGEBRA OVER Z_K  (HNF,SNF)             */
/*                                                                 */
/*******************************************************************/

/* returns the first index i<=n such that x=v[i] if it exits, 0 otherwise */
long
isinvector(GEN v, GEN x, long n)
{
  long i;

  for (i=1; i<=n; i++)
    if (gegal((GEN)v[i],x)) return i;
  return 0;
}

GEN
element_mulvec(GEN nf, GEN x, GEN v)
{
  long lv = lg(v), i;
  GEN y = cgetg(lv,t_COL);

  if (typ(x) == t_COL)
  {
    GEN mul = eltmul_get_table(nf,x);
    for (i=1; i<lv; i++) y[i] = lmul(mul,(GEN)v[i]);
  }
  else
  { /* scalar */
    for (i=1; i<lv; i++) y[i] = lmul(x, (GEN)v[i]);
  }
  return y;
}

static GEN
element_mulvecrow(GEN nf, GEN x, GEN m, long i, long lim)
{
  long lv,j;
  GEN y, mul = eltmul_get_table(nf,x);

  lv=min(lg(m),lim+1); y=cgetg(lv,t_VEC);
  for (j=1; j<lv; j++) y[j] = lmul(mul,gcoeff(m,i,j));
  return y;
}

/* Given an element x and an ideal in matrix form (not necessarily HNF),
 * gives an r such that x-r is in ideal and r is small. No checks */
GEN
element_reduce(GEN nf, GEN x, GEN ideal)
{
  long tx = typ(x), N, i;
  gpmem_t av=avma;
  GEN u,d;

  if (is_extscalar_t(tx))
    x = algtobasis_i(checknf(nf), x);
  N = lg(x);
  if (typ(ideal) != t_MAT || lg(ideal) != N) err(typeer,"element_reduce");
  u = deplin( concatsp(ideal,x) );
  d = (GEN)u[N]; setlg(u,N);
  for (i=1; i<N; i++) u[i] = (long)gdivround((GEN)u[i],d);
  return gerepileupto(av, gadd(x, gmul(ideal,u)));
}

/* A torsion-free module M over Z_K will be given by a row vector [A,I] with
 * two components. I=[\a_1,...,\a_k] is a row vector of k fractional ideals
 * given in HNF. A is an nxk matrix (same k and n the rank of the module)
 * such that if A_j is the j-th column of A then M=\a_1A_1+...\a_kA_k. We say
 * that [A,I] is a pseudo-basis if k=n
 */

#define swap(x,y) { long _t=x; x=y; y=_t; }

/* Given a torsion-free module x as above outputs a pseudo-basis for x in HNF */
GEN
nfhermite(GEN nf, GEN x)
{
  long i, j, def, k, m;
  gpmem_t av0 = avma, av, lim;
  GEN p1,p2,y,A,I,J;

  nf = checknf(nf);
  if (typ(x)!=t_VEC || lg(x)!=3) err(talker,"not a module in nfhermite");
  A = (GEN)x[1];
  I = (GEN)x[2]; k = lg(A)-1;
  if (typ(A)!=t_MAT) err(talker,"not a matrix in nfhermite");
  if (typ(I)!=t_VEC || lg(I)!=k+1)
    err(talker,"not a correct ideal list in nfhermite");
  if (!k) err(talker,"not a matrix of maximal rank in nfhermite");
  m = lg(A[1])-1;
  if (k < m) err(talker,"not a matrix of maximal rank in nfhermite");

  av = avma; lim = stack_lim(av, 1);
  A = matalgtobasis(nf,A);
  I = dummycopy(I);
  J = zerovec(k); def = k+1;
  for (i=m; i>=1; i--)
  {
    GEN den,p4,p5,p6,u,v,newid, invnewid = NULL;

    def--; j=def; while (j>=1 && gcmp0(gcoeff(A,i,j))) j--;
    if (!j) err(talker,"not a matrix of maximal rank in nfhermite");
    if (j==def) j--; else { swap(A[j], A[def]); swap(I[j], I[def]); }
    p1 = gcoeff(A,i,def);
    p2 = element_inv(nf, p1);
    A[def] = (long)element_mulvec(nf,p2,(GEN)A[def]);
    I[def] = (long)idealmul(nf,p1,(GEN)I[def]);
    for (  ; j; j--)
    {
      p1 = gcoeff(A,i,j);
      if (gcmp0(p1)) continue;

      p2 = idealmul(nf,p1,(GEN)I[j]);
      newid = idealadd(nf,p2,(GEN)I[def]);

      invnewid = hnfideal_inv(nf,newid);
      p4 = idealmul(nf, p2,        invnewid);
      p5 = idealmul(nf,(GEN)I[def],invnewid);
      y = idealaddtoone(nf,p4,p5);
      u = (GEN)y[1]; u = element_div(nf, u, p1);
      v = (GEN)y[2];
      p6 = gsub((GEN)A[j], element_mulvec(nf, p1,(GEN)A[def]));
      A[def] = ladd(element_mulvec(nf, u, (GEN)A[j]),
                    element_mulvec(nf, v, (GEN)A[def]));
      A[j] = (long)p6;
      I[j] = (long)idealmul(nf,idealmul(nf,(GEN)I[j],(GEN)I[def]),invnewid);
      I[def] = (long)newid; den = denom((GEN)I[j]);
      if (!gcmp1(den))
      {
        I[j] = lmul(den,(GEN)I[j]);
        A[j] = ldiv((GEN)A[j],den);
      }
    }
    if (!invnewid) invnewid = hnfideal_inv(nf,(GEN)I[def]);
    J[def] = (long)invnewid;
    p1 = (GEN)I[def];
    for (j=def+1; j<=k; j++)
    {
      GEN c = gcoeff(A,i,j);
      p2 = gsub(element_reduce(nf,c, idealmul(nf,p1,(GEN)J[j])), c);
      A[j] = ladd((GEN)A[j], element_mulvec(nf, p2,(GEN)A[def]));
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[3]; gptr[0]=&A; gptr[1]=&I; gptr[2]=&J;
      if(DEBUGMEM>1) err(warnmem,"nfhermite, i = %ld", i);
      gerepilemany(av,gptr,3);
    }
  }
  y = cgetg(3,t_VEC);
  A += k-m; A[0] = evaltyp(t_MAT)|evallg(m+1); y[1] = (long)A;
  I += k-m; I[0] = evaltyp(t_VEC)|evallg(m+1); y[2] = (long)I;
  return gerepilecopy(av0, y);
}

static GEN
idealmulelt(GEN nf, GEN elt, GEN x)
{
  long t = typ(elt);
  GEN z;
  if (t == t_POL || t == t_POLMOD) elt = algtobasis(nf,elt);
  if (isnfscalar(elt)) elt = (GEN)elt[1];
  z = element_mulvec(nf, elt, x);
  settyp(z, t_MAT); return z;
}

static GEN
zero_nfbezout(GEN nf,GEN b, GEN A,GEN B,GEN *u,GEN *v,GEN *w,GEN *di)
{
  gpmem_t av, tetpil;
  GEN pab,d;

  d=idealmulelt(nf,b,B); *di=idealinv(nf,idealmat_to_hnf(nf,d));
  av=avma; pab=idealmul(nf,A,B); tetpil=avma;
  *w=gerepile(av,tetpil, idealmul(nf,pab,*di));
  *v=element_inv(nf,b);
  *u=gzero; return d;
}

/* Given elements a,b and ideals A, B, outputs d = a.A+b.B and gives
 * di=d^-1, w=A.B.di, u, v such that au+bv=1 and u in A.di, v in
 * B.di. Assume A, B non-zero, but a or b can be zero (not both)
 */
static GEN
nfbezout(GEN nf,GEN a,GEN b, GEN A,GEN B, GEN *u,GEN *v,GEN *w,GEN *di)
{
  GEN pab,pu,pv,pw,uv,d,dinv,pa,pb,pa1,pb1, *gptr[5];
  gpmem_t av, tetpil;

  if (gcmp0(a))
  {
    if (gcmp0(b)) err(talker,"both elements zero in nfbezout");
    return zero_nfbezout(nf,b,A,B,u,v,w,di);
  }
  if (gcmp0(b))
    return zero_nfbezout(nf,a,B,A,v,u,w,di);

  av = avma;
  pa = idealmulelt(nf,a,A);
  pb = idealmulelt(nf,b,B);

  d=idealadd(nf,pa,pb); dinv=idealinv(nf,d);
  pa1=idealmullll(nf,pa,dinv);
  pb1=idealmullll(nf,pb,dinv);
  uv=idealaddtoone(nf,pa1,pb1);
  pab=idealmul(nf,A,B); tetpil=avma;

  pu=element_div(nf,(GEN)uv[1],a);
  pv=element_div(nf,(GEN)uv[2],b);
  d=gcopy(d); dinv=gcopy(dinv);
  pw=idealmul(nf,pab,dinv);

  *u=pu; *v=pv; *w=pw; *di=dinv;
  gptr[0]=u; gptr[1]=v; gptr[2]=w; gptr[3]=di;
  gptr[4]=&d; gerepilemanysp(av,tetpil,gptr,5);
  return d;
}

/* A torsion module M over Z_K will be given by a row vector [A,I,J] with
 * three components. I=[b_1,...,b_n] is a row vector of k fractional ideals
 * given in HNF, J=[a_1,...,a_n] is a row vector of n fractional ideals in
 * HNF. A is an nxn matrix (same n) such that if A_j is the j-th column of A
 * and e_n is the canonical basis of K^n, then
 * M=(b_1e_1+...+b_ne_n)/(a_1A_1+...a_nA_n)
 */

/* We input a torsion module x=[A,I,J] as above, and output the
 * smith normal form as K=[\c_1,...,\c_n] such that x=Z_K/\c_1+...+Z_K/\c_n.
 */
GEN
nfsmith(GEN nf, GEN x)
{
  long i, j, k, l, c, n, m, N;
  gpmem_t av, tetpil, lim;
  GEN p1,p2,p3,p4,z,b,u,v,w,d,dinv,unnf,A,I,J;

  nf=checknf(nf); N=degpol(nf[1]);
  if (typ(x)!=t_VEC || lg(x)!=4) err(talker,"not a module in nfsmith");
  A=(GEN)x[1]; I=(GEN)x[2]; J=(GEN)x[3];
  if (typ(A)!=t_MAT) err(talker,"not a matrix in nfsmith");
  n=lg(A)-1;
  if (typ(I)!=t_VEC || lg(I)!=n+1 || typ(J)!=t_VEC || lg(J)!=n+1)
    err(talker,"not a correct ideal list in nfsmith");
  if (!n) err(talker,"not a matrix of maximal rank in nfsmith");
  m=lg(A[1])-1;
  if (n<m) err(talker,"not a matrix of maximal rank in nfsmith");
  if (n>m) err(impl,"nfsmith for non square matrices");

  av=avma; lim=stack_lim(av,1);
  p1 = cgetg(n+1,t_MAT); for (j=1; j<=n; j++) p1[j]=A[j];
  A = p1; I = dummycopy(I); J=dummycopy(J);
  for (j=1; j<=n; j++)
    if (typ(I[j])!=t_MAT) I[j]=(long)idealhermite_aux(nf,(GEN)I[j]);
  for (j=1; j<=n; j++)
    if (typ(J[j])!=t_MAT) J[j]=(long)idealhermite_aux(nf,(GEN)J[j]);
  for (i=n; i>=2; i--)
  {
    do
    {
      c = 0;
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(A,i,j); if (gcmp0(p1)) continue;

        p2 = gcoeff(A,i,i);
        d = nfbezout(nf,p2,p1,(GEN)J[i],(GEN)J[j],&u,&v,&w,&dinv);
        if (gcmp0(u)) b = element_mulvec(nf,v,(GEN)A[j]);
        else
        {
          if (gcmp0(v)) b = element_mulvec(nf,u,(GEN)A[i]);
          else
            b = gadd(element_mulvec(nf,u,(GEN)A[i]),
                     element_mulvec(nf,v,(GEN)A[j]));
        }
        A[j] = lsub(element_mulvec(nf,p2,(GEN)A[j]),
                    element_mulvec(nf,p1,(GEN)A[i]));
        A[i] = (long)b; J[j] = (long)w; J[i] = (long)d;
      }
      for (j=i-1; j>=1; j--)
      {
	p1 = gcoeff(A,j,i); if (gcmp0(p1)) continue;

        p2 = gcoeff(A,i,i);
        d = nfbezout(nf,p2,p1,(GEN)I[i],(GEN)I[j],&u,&v,&w,&dinv);
        if (gcmp0(u)) b = element_mulvecrow(nf,v,A,j,i);
        else
        {
          if (gcmp0(v))
            b = element_mulvecrow(nf,u,A,i,i);
          else
            b = gadd(element_mulvecrow(nf,u,A,i,i),
                     element_mulvecrow(nf,v,A,j,i));
        }
        p3 = gsub(element_mulvecrow(nf,p2,A,j,i),
                  element_mulvecrow(nf,p1,A,i,i));
        for (k=1; k<=i; k++) { coeff(A,j,k) = p3[k]; coeff(A,i,k) = b[k]; }
        I[j] = (long)w; I[i] = (long)d; c = 1;
      }
      if (c) continue;

      b=gcoeff(A,i,i); if (gcmp0(b)) break;

      b=idealmul(nf,b,idealmul(nf,(GEN)J[i],(GEN)I[i]));
      for (k=1; k<i; k++)
        for (l=1; l<i; l++)
        {
          p3 = gcoeff(A,k,l);
          if (gcmp0(p3)) continue;

          p4 = idealmul(nf,p3,idealmul(nf,(GEN)J[l],(GEN)I[k]));
          if (hnfdivide(b, p4)) continue;

          b = idealdiv(nf,(GEN)I[k],(GEN)I[i]);
          p1 = idealdiv(nf,(GEN)J[i], idealmul(nf,p3,(GEN)J[l]));
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
        GEN *gptr[3]; gptr[0]=&A; gptr[1]=&I; gptr[2]=&J;
	if(DEBUGMEM>1) err(warnmem,"nfsmith");
        gerepilemany(av,gptr,3);
      }
    }
    while (c);
  }
  unnf=gscalcol_i(gun,N);
  p1=gcoeff(A,1,1); coeff(A,1,1)=(long)unnf;
  J[1]=(long)idealmul(nf,p1,(GEN)J[1]);
  for (i=2; i<=n; i++)
    if (!gegal(gcoeff(A,i,i),unnf)) err(talker,"bug in nfsmith");
  tetpil=avma; z=cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++) z[i]=(long)idealmul(nf,(GEN)I[i],(GEN)J[i]);
  return gerepile(av,tetpil,z);
}

#define trivlift(x) ((typ(x)==t_POLMOD)? (GEN)x[2]: lift_intern(x))

GEN
element_mulmodpr2(GEN nf, GEN x, GEN y, GEN modpr)
{
  gpmem_t av=avma;
  GEN p1;

  nf=checknf(nf); checkmodpr(modpr);
  p1 = element_mul(nf,x,y);
  return gerepileupto(av,nfreducemodpr(nf,p1,modpr));
}

GEN
element_divmodpr(GEN nf, GEN x, GEN y, GEN modpr)
{
  gpmem_t av=avma;
  GEN p1;

  nf=checknf(nf); checkmodpr(modpr);
  p1=lift_intern(gdiv(gmodulcp(gmul((GEN)nf[7],trivlift(x)), (GEN)nf[1]),
                      gmodulcp(gmul((GEN)nf[7],trivlift(y)), (GEN)nf[1])));
  p1=algtobasis_i(nf,p1);
  return gerepileupto(av,nfreducemodpr(nf,p1,modpr));
}

GEN
element_invmodpr(GEN nf, GEN y, GEN modpr)
{
  gpmem_t av=avma;
  GEN p1;

  p1=QX_invmod(gmul((GEN)nf[7],trivlift(y)), (GEN)nf[1]);
  p1=algtobasis_i(nf,p1);
  return gerepileupto(av,nfreducemodpr(nf,p1,modpr));
}

GEN
element_powmodpr(GEN nf,GEN x,GEN k,GEN pr)
{
  gpmem_t av=avma;
  GEN z,T,p,modpr;

  nf = checknf(nf);
  modpr = nf_to_ff_init(nf,&pr,&T,&p);
  z = nf_to_ff(nf,x,modpr);
  z = FpXQ_pow(z,k,T,p);
  return gerepileupto(av, algtobasis(nf, ff_to_nf(z,modpr)));
}

GEN
nfkermodpr(GEN nf, GEN x, GEN pr)
{
  gpmem_t av = avma;
  GEN T,p,modpr;

  nf = checknf(nf);
  if (typ(x)!=t_MAT) err(typeer,"nfkermodpr");
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  x = modprM(lift(x), nf, modpr);
  return gerepilecopy(av, modprM_lift(FqM_ker(x,T,p), modpr));
}

/* a.x=b ou b est un vecteur */
GEN
nfsolvemodpr(GEN nf, GEN a, GEN b, GEN pr)
{
  gpmem_t av = avma;
  GEN T,p,modpr;

  nf = checknf(nf);
  if (typ(a)!=t_MAT) err(typeer,"nfsolvemodpr");
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  a = modprM(lift(a), nf, modpr);
  b = modprM(lift(b), nf, modpr);
  return gerepilecopy(av, modprM_lift(FqM_gauss(a,b,T,p), modpr));
}

GEN
nfsuppl(GEN nf, GEN x, long n, GEN pr)
{
  gpmem_t av = avma;
  GEN T,p,modpr;

  nf = checknf(nf);
  if (typ(x)!=t_MAT) err(typeer,"nfkermodpr");
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  x = modprM(lift(x), nf, modpr);
  return gerepilecopy(av, modprM_lift(FqM_suppl(x,T,p), modpr));
}

/* Given a pseudo-basis pseudo, outputs a multiple of its ideal determinant */
GEN
nfdetint(GEN nf,GEN pseudo)
{
  GEN pass,c,v,det1,piv,pivprec,vi,p1,x,I,unnf,zeronf,id,idprod;
  long i, j, k, rg, n, n1, m, m1, cm=0, N;
  gpmem_t av=avma, av1, tetpil, lim;

  nf=checknf(nf); N=degpol(nf[1]);
  if (typ(pseudo)!=t_VEC || lg(pseudo)!=3)
    err(talker,"not a module in nfdetint");
  x=(GEN)pseudo[1]; I=(GEN)pseudo[2];
  if (typ(x)!=t_MAT) err(talker,"not a matrix in nfdetint");
  n1=lg(x); n=n1-1; if (!n) return gun;

  m1=lg(x[1]); m=m1-1;
  if (typ(I)!=t_VEC || lg(I)!=n1)
    err(talker,"not a correct ideal list in nfdetint");

  unnf=gscalcol_i(gun,N); zeronf=zerocol(N);
  id=idmat(N); c=new_chunk(m1); for (k=1; k<=m; k++) c[k]=0;
  piv = pivprec = unnf;

  av1=avma; lim=stack_lim(av1,1);
  det1=idprod=gzero; /* dummy for gerepilemany */
  pass=cgetg(m1,t_MAT); v=cgetg(m1,t_COL);
  for (j=1; j<=m; j++)
  {
    v[j] = zero; /* dummy */
    p1=cgetg(m1,t_COL); pass[j]=(long)p1;
    for (i=1; i<=m; i++) p1[i]=(long)zeronf;
  }
  for (rg=0,k=1; k<=n; k++)
  {
    long t = 0;
    for (i=1; i<=m; i++)
      if (!c[i])
      {
	vi=element_mul(nf,piv,gcoeff(x,i,k));
	for (j=1; j<=m; j++)
	  if (c[j]) vi=gadd(vi,element_mul(nf,gcoeff(pass,i,j),gcoeff(x,j,k)));
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
      GEN *gptr[6];
      if(DEBUGMEM>1) err(warnmem,"nfdetint");
      gptr[0]=&det1; gptr[1]=&piv; gptr[2]=&pivprec; gptr[3]=&pass;
      gptr[4]=&v; gptr[5]=&idprod; gerepilemany(av1,gptr,6);
    }
  }
  if (!cm) { avma=av; return gscalmat(gzero,N); }
  tetpil=avma; return gerepile(av,tetpil,idealmul(nf,idprod,det1));
}

/* clean in place (destroy x) */
static void
nfcleanmod(GEN nf, GEN x, long lim, GEN detmat)
{
  long lx=lg(x),i;

  if (lim<=0 || lim>=lx) lim=lx-1;
  for (i=1; i<=lim; i++)
    x[i]=(long)element_reduce(nf,(GEN)x[i],detmat);
}

/* A usage interne. Pas de verifs ni gestion de pile */
GEN
idealoplll(GEN op(GEN,GEN,GEN), GEN nf, GEN x, GEN y)
{
  GEN z = op(nf,x,y), den = denom(z);

  if (gcmp1(den)) den = NULL; else z=gmul(den,z);
  z=gmul(z,lllintpartial(z));
  return den? gdiv(z,den): z;
}

GEN
nfhermitemod(GEN nf, GEN pseudo, GEN detmat)
{
  long li, co, i, j, jm1, def, ldef, N;
  gpmem_t av0=avma, av, lim;
  GEN b,q,w,p1,d,u,v,den,x,I,J,dinv,wh,unnf;

  nf=checknf(nf); N=degpol(nf[1]);
  if (typ(pseudo)!=t_VEC || lg(pseudo)!=3)
    err(talker,"not a module in nfhermitemod");
  x = (GEN)pseudo[1];
  I = (GEN)pseudo[2];
  if (typ(x) != t_MAT) err(talker,"not a matrix in nfhermitemod");
  co = lg(x);
  if (typ(I) != t_VEC || lg(I) != co)
    err(talker,"not a correct ideal list in nfhermitemod");
  if (co==1) return cgetg(1,t_MAT);

  li= lg(x[1]);
  x = matalgtobasis(nf, x);
  I = dummycopy(I);
  unnf = gscalcol(gun,N);

  den = denom(detmat); if (!gcmp1(den)) detmat = gmul(den,detmat);
  detmat = lllint_ip(detmat,100);

  av = avma; lim = stack_lim(av,1);
  def = co; ldef = (li>co)? li-co+1: 1;
  for (i=li-1; i>=ldef; i--)
  {
    def--; j=def-1; while (j && gcmp0(gcoeff(x,i,j))) j--;
    while (j)
    {
      jm1=j-1; if (!jm1) jm1=def;
      d=nfbezout(nf,gcoeff(x,i,j),gcoeff(x,i,jm1),(GEN)I[j],(GEN)I[jm1],
                 &u,&v,&w,&dinv);
      if (gcmp0(u))
        p1 = element_mulvec(nf,v,(GEN)x[jm1]);
      else
      {
	p1 = element_mulvec(nf,u,(GEN)x[j]);
	if (!gcmp0(v)) p1=gadd(p1, element_mulvec(nf,v,(GEN)x[jm1]));
      }
      x[j]=lsub(element_mulvec(nf,gcoeff(x,i,j),(GEN)x[jm1]),
                element_mulvec(nf,gcoeff(x,i,jm1),(GEN)x[j]));
      nfcleanmod(nf,(GEN)x[j],i,idealdivlll(nf,detmat,w));
      nfcleanmod(nf,p1,i,idealmullll(nf,detmat,dinv));
      x[jm1]=(long)p1; I[j]=(long)w; I[jm1]=(long)d;
      j--; while (j && gcmp0(gcoeff(x,i,j))) j--;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[2]; gptr[0]=&x; gptr[1]=&I;
      if(DEBUGMEM>1) err(warnmem,"[1]: nfhermitemod");
      gerepilemany(av,gptr,2);
    }
  }
  b = detmat; wh = cgetg(li,t_MAT); def--;
  for (i=li-1; i>=1; i--)
  {
    d = nfbezout(nf,gcoeff(x,i,i+def),unnf,(GEN)I[i+def],b,&u,&v,&w,&dinv);
    p1 = element_mulvec(nf,u,(GEN)x[i+def]);
    nfcleanmod(nf,p1,i,idealmullll(nf,b,dinv));
    wh[i] = (long)p1; coeff(wh,i,i) = (long)unnf;
    I[i+def] = (long)d;
    if (i>1) b = idealmul(nf,b,dinv);
  }
  J=cgetg(li,t_VEC); J[1]=zero;
  for (j=2; j<li; j++) J[j] = (long)idealinv(nf,(GEN)I[j+def]);
  for (i=li-2; i>=1; i--)
  {
    for (j=i+1; j<li; j++)
    {
      q = idealmul(nf,(GEN)I[i+def],(GEN)J[j]);
      p1 = gsub(element_reduce(nf,gcoeff(wh,i,j),q), gcoeff(wh,i,j));
      wh[j] = ladd((GEN)wh[j],element_mulvec(nf,p1,(GEN)wh[i]));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[3]; gptr[0]=&wh; gptr[1]=&I; gptr[2]=&J;
      if(DEBUGMEM>1) err(warnmem,"[2]: nfhermitemod");
      gerepilemany(av,gptr,3);
    }
  }
  I += def; I[0] = evaltyp(t_VEC)|evallg(li);
  p1=cgetg(3,t_VEC);
  p1[1] = (long)wh;
  p1[2] = (long)I; return gerepilecopy(av0, p1);
}
