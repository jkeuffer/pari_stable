/* $Id$

Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**             GENERIC ALGORITHMS ON BLACKBOX GROUP                  **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"
#undef pow /* AIX: pow(a,b) is a macro, wrongly expanded on grp->pow(a,b,c) */

/***********************************************************************/
/**                                                                   **/
/**                    POWERING                                       **/
/**                                                                   **/
/***********************************************************************/

/* return (n>>(i+1-l)) & ((1<<l)-1) */
static ulong
int_block(GEN n, long i, long l)
{
  long q = divsBIL(i), r = remsBIL(i)+1, lr;
  GEN nw = int_W(n, q);
  ulong w = (ulong) *nw, w2;
  if (r>=l) return (w>>(r-l))&((1UL<<l)-1);
  w &= (1UL<<r)-1; lr = l-r;
  w2 = (ulong) *int_precW(nw); w2 >>= (BITS_IN_LONG-lr);
  return (w<<lr)|w2;
}

/* assume n != 0, t_INT. Compute x^|n| using sliding window powering */
static GEN
sliding_window_powu(GEN x, ulong n, long e, void *E, GEN (*sqr)(void*,GEN),
                                                     GEN (*mul)(void*,GEN,GEN))
{
  pari_sp ltop = avma, av, lim;
  long i, l = expu(n), u = (1UL<<(e-1));
  long w, v;
  GEN tab = cgetg(1+u, t_VEC);
  GEN x2 = sqr(E, x), z = NULL, tw;
  gel(tab, 1) = x;
  for (i=2; i<=u; i++) gel(tab,i) = mul(E, gel(tab,i-1), x2);
  av = avma; lim = stack_lim(av, 1);
  while (l>=0)
  {
    if (e > l+1) e = l+1;
    w = (n>>(l+1-e)) & ((1UL<<e)-1); v = vals(w); l-=e;
    tw = gel(tab, 1+(w>>(v+1)));
    if (z)
    {
      for (i=1; i<=e-v; i++) z = sqr(E, z);
      z = mul(E, z, tw);
    } else z = tw;
    for (i=1; i<=v; i++) z = sqr(E, z);
    while (l>=0)
    {
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"sliding_window_powu");
        z = gerepilecopy(av, z);
      }
      if (n&(1UL<<l)) break;
      z = sqr(E, z); l--;
    }
  }
  return gerepilecopy(ltop, z);
}


/* assume n != 0, t_INT. Compute x^|n| using sliding window powering */
static GEN
sliding_window_pow(GEN x, GEN n, long e, void *E, GEN (*sqr)(void*,GEN),
                                                  GEN (*mul)(void*,GEN,GEN))
{
  pari_sp ltop = avma, av, lim;
  long i, l = expi(n), u = (1UL<<(e-1));
  long w, v;
  GEN tab = cgetg(1+u, t_VEC);
  GEN x2 = sqr(E, x), z = NULL, tw;
  gel(tab, 1) = x;
  for (i=2; i<=u; i++) gel(tab,i) = mul(E, gel(tab,i-1), x2);
  av = avma; lim = stack_lim(av, 1);
  while (l>=0)
  {
    if (e > l+1) e = l+1;
    w = int_block(n,l,e); v = vals(w); l-=e;
    tw = gel(tab, 1+(w>>(v+1)));
    if (z)
    {
      for (i=1; i<=e-v; i++) z = sqr(E, z);
      z = mul(E, z, tw);
    } else z = tw;
    for (i=1; i<=v; i++) z = sqr(E, z);
    while (l>=0)
    {
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"sliding_window_pow");
        z = gerepilecopy(av, z);
      }
      if (int_bit(n,l)) break;
      z = sqr(E, z); l--;
    }
  }
  return gerepilecopy(ltop, z);
}

/* assume n != 0, t_INT. Compute x^|n| using leftright binary powering */
static GEN
leftright_binary_powu(GEN x, long n, void *E, GEN (*sqr)(void*,GEN),
                                              GEN (*mul)(void*,GEN,GEN))
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN  y = x;
  long m = (long) n, j = 1+bfffo(m);

  /* normalize, i.e set highest bit to 1 (we know m != 0) */
  m<<=j; j = BITS_IN_LONG-j;
  /* first bit is now implicit */
  for (; j; m<<=1,j--)
  {
    y = sqr(E,y);
    if (m < 0) y = mul(E,y,x); /* first bit set: multiply by base */
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"leftright_powu");
      y = gerepilecopy(av, y);
    }
  }
  return gerepilecopy(av, y);
}

GEN
gen_powu(GEN x, ulong n, void *E, GEN (*sqr)(void*,GEN),
                                  GEN (*mul)(void*,GEN,GEN))
{
  long l;
  if (n == 1) return gcopy(x);
  l = expu(n);
  if (l<=8) return leftright_binary_powu(x, n, E, sqr, mul);
  if (l<=24)  return sliding_window_powu(x, n, 2, E, sqr, mul);
  return sliding_window_powu(x, n, 3, E, sqr, mul);
}

GEN
gen_pow(GEN x, GEN n, void *E, GEN (*sqr)(void*,GEN),
                               GEN (*mul)(void*,GEN,GEN))
{
  long l;
  if (lgefint(n)==3) return gen_powu(x,(ulong)n[2],E,sqr,mul);
  l = expi(n);
  if (l<=64)  return sliding_window_pow(x, n, 3, E, sqr, mul);
  if (l<=160) return sliding_window_pow(x, n, 4, E, sqr, mul);
  if (l<=384) return sliding_window_pow(x, n, 5, E, sqr, mul);
  if (l<=896) return sliding_window_pow(x, n, 6, E, sqr, mul);
  return sliding_window_pow(x, n, 7, E, sqr, mul);
}

/***********************************************************************/
/**                                                                   **/
/**                    DISCRETE LOGARITHM                             **/
/**                                                                   **/
/***********************************************************************/

static GEN
iter_rho(GEN x, GEN g, GEN q, GEN A, ulong h, void *E, const struct bb_group *grp)
{
  GEN a = gel(A,1);
  switch((h|grp->hash(a))%3UL)
  {
    case 0:
      return mkvec3(grp->pow(E,a,gen_2),Fp_mulu(gel(A,2),2,q),
                                        Fp_mulu(gel(A,3),2,q));
    case 1:
      return mkvec3(grp->mul(E,a,x),addis(gel(A,2),1),gel(A,3));
    case 2:
      return mkvec3(grp->mul(E,a,g),gel(A,2),addis(gel(A,3),1));
  }
  return NULL;
}

/*Generic Pollard rho discrete log algorithm*/
static GEN
gen_Pollard_log(GEN x, GEN g, GEN q, void *E, const struct bb_group *grp)
{
  pari_sp av=avma, lim=stack_lim(av,2);
  GEN A, B, l, sqrt4q = sqrti(shifti(q,4));
  ulong i, h = 0, imax = itou_or_0(sqrt4q);
  if (!imax) imax = ULONG_MAX;
  do {
 rho_restart:
    A = B = mkvec3(x,gen_1,gen_0);
    i=0;
    do {
      if (i>imax)
      {
        h++;
        if (DEBUGLEVEL)
          pari_warn(warner,"changing Pollard rho hash seed to %ld",h);
        goto rho_restart;
      }
      A = iter_rho(x, g, q, A, h, E, grp);
      B = iter_rho(x, g, q, B, h, E, grp);
      B = iter_rho(x, g, q, B, h, E, grp);
      if (low_stack(lim, stack_lim(av,2)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"gen_Pollard_log");
        gerepileall(av, 2, &A, &B);
      }
      i++;
    } while (grp->cmp(gel(A,1), gel(B,1)));
    gel(A,2) = modii(gel(A,2), q);
    gel(B,2) = modii(gel(B,2), q);
    h++;
  } while (equalii(gel(A,2), gel(B,2)));
  l = Fp_div(Fp_sub(gel(B,3), gel(A,3),q),Fp_sub(gel(A,2), gel(B,2), q), q);
  return gerepileuptoint(av, l);
}

/*Generic Shanks baby-step/giant-step algorithm*/
static GEN
gen_Shanks_log(GEN x, GEN g0,GEN q, void *E, const struct bb_group *grp)
{
  pari_sp av=avma,av1,lim;
  long lbaby,i,k;
  GEN p1,smalltable,giant,perm,v,g0inv;
  p1 = sqrti(q);
  if (cmpiu(p1,LGBITS) >= 0)
    pari_err_OVERFLOW("gen_Shanks_log() [order too large]");
  lbaby = itos(p1)+1; smalltable = cgetg(lbaby+1,t_VEC);
  g0inv = grp->pow(E,g0,gen_m1);

  for (p1=x, i=1;;i++)
  {
    av1 = avma;
    if (grp->equal1(p1)) { avma = av; return stoi(i-1); }
    gel(smalltable,i) = p1; if (i==lbaby) break;
    p1 = gerepileupto(av1, grp->mul(E,p1,g0inv));
  }
  p1 = giant = grp->mul(E,x,grp->pow(E, p1, gen_m1));
  gen_sort_inplace(smalltable, (void*)grp->cmp, &cmp_nodata, &perm);

  av1 = avma; lim=stack_lim(av1,2);
  for (k=1; k<= lbaby; k++)
  {
    i=tablesearch(smalltable,p1,grp->cmp);
    if (i)
    {
      v=addis(mulss(lbaby-1,k),perm[i]);
      return gerepileuptoint(av,addsi(-1,v));
    }
    p1 = grp->mul(E,p1,giant);

    if (low_stack(lim, stack_lim(av1,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_log, k = %ld", k);
      p1 = gerepileupto(av1, p1);
    }
  }
  avma = av; return cgetg(1, t_VEC); /* no solution */
}

/*Generic discrete logarithme in a group of prime order p*/
GEN
gen_plog(GEN x, GEN g, GEN p, void *E, const struct bb_group *grp,
    GEN easy(void*E, GEN, GEN, GEN))
{
  if (easy)
  {
    GEN e = easy(E, x, g, p);
    if (e) return e;
  }
  if (grp->equal1(x)) return gen_0;
  if (!grp->cmp(x,g)) return gen_1;
  if (grp->hash==NULL || expi(p)<32) return gen_Shanks_log(x,g,p,E,grp);
  return gen_Pollard_log(x, g, p, E, grp);
}

GEN
dlog_get_ordfa(GEN o)
{
  if (!o) return NULL;
  switch(typ(o))
  {
    case t_INT:
      if (signe(o) > 0) return mkvec2(o, Z_factor(o));
      break;
    case t_MAT:
      if (is_Z_factor(o)) return mkvec2(factorback(o), o);
      break;
    case t_VEC:
      if (lg(o) == 3 && signe(gel(o,1)) > 0 && is_Z_factor(gel(o,2))) return o;
      break;
  }
  pari_err_TYPE("generic discrete logarithm (order factorization)",o);
  return NULL; /* not reached */
}
GEN
dlog_get_ord(GEN o)
{
  if (!o) return NULL;
  switch(typ(o))
  {
    case t_INT:
      if (signe(o) > 0) return o;
      break;
    case t_MAT:
      o = factorback(o);
      if (typ(o) == t_INT && signe(o) > 0) return o;
      break;
    case t_VEC:
      if (lg(o) != 3) break;
      o = gel(o,1);
      if (typ(o) == t_INT && signe(o) > 0) return o;
      break;
  }
  pari_err_TYPE("generic discrete logarithm (order factorization)",o);
  return NULL; /* not reached */
}

/* easy() is an optional trapdoor function that catch easy logarithms*/
/* Generic Pohlig-Hellman discrete logarithm*/
/* smallest integer n such that g^n=a. Assume g has order ord */
GEN
gen_PH_log(GEN a, GEN g, GEN ord, void *E, const struct bb_group *grp,
    GEN easy(void *E, GEN, GEN, GEN))
{
  pari_sp av = avma;
  GEN v,t0,a0,b,q,g_q,n_q,ginv0,qj,ginv;
  GEN fa, ex;
  long e,i,j,l;

  if (grp->cmp(g, a)==0) /* frequent special case */
    return grp->equal1(g)? gen_0: gen_1;
  if (easy)
  {
    GEN e = easy(E, a, g, ord);
    if (e) return e;
  }
  v = dlog_get_ordfa(ord);
  ord= gel(v,1);
  fa = gel(v,2);
  ex = gel(fa,2);
  fa = gel(fa,1); l = lg(fa);
  ginv = grp->pow(E,g,gen_m1);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    q = gel(fa,i);
    e = itos(gel(ex,i));
    if (DEBUGLEVEL>5)
      err_printf("Pohlig-Hellman: DL mod %Ps^%ld\n",q,e);
    qj = new_chunk(e+1);
    gel(qj,0) = gen_1;
    gel(qj,1) = q;
    for (j=2; j<=e; j++) gel(qj,j) = mulii(gel(qj,j-1), q);
    t0 = diviiexact(ord, gel(qj,e));
    a0 = grp->pow(E, a, t0);
    ginv0 = grp->pow(E, ginv, t0); /* order q^e */
    g_q = grp->pow(E,g, mulii(t0, gel(qj,e-1))); /* order q */
    n_q = gen_0;
    for (j=0;; j++)
    { /* n_q = sum_{i<j} b_i q^i */
      b = grp->pow(E,a0, gel(qj,e-1-j));
      /* early abort: cheap and very effective */
      if (j == 0 && !grp->equal1(grp->pow(E,b,q))) {
        avma = av; return cgetg(1, t_VEC);
      }
      b = gen_plog(b, g_q, q, E, grp, easy);
      if (typ(b) != t_INT) { avma = av; return cgetg(1, t_VEC); }
      n_q = addii(n_q, mulii(b, gel(qj,j)));
      if (j == e-1) break;

      a0 = grp->mul(E,a0, grp->pow(E,ginv0, b));
      ginv0 = grp->pow(E,ginv0, q);
    }
    gel(v,i) = mkintmod(n_q, gel(qj,e));
  }
  return gerepileuptoint(av, lift(chinese1_coprime_Z(v)));
}

/***********************************************************************/
/**                                                                   **/
/**                    ORDER OF AN ELEMENT                            **/
/**                                                                   **/
/***********************************************************************/
/*Find the exact order of a assuming a^o==1*/
GEN
gen_order(GEN a, GEN o, void *E, const struct bb_group *grp)
{
  pari_sp av = avma;
  long i, l;
  GEN m;

  m = dlog_get_ordfa(o);
  if (!m) pari_err_TYPE("gen_order [missing order]",a);
  o = gel(m,1);
  m = gel(m,2); l = lg(m[1]);
  for (i = l-1; i; i--)
  {
    GEN t, y, p = gcoeff(m,i,1);
    long j, e = itos(gcoeff(m,i,2));
    if (l == 1) {
      t = gen_1;
      y = a;
    } else {
      t = diviiexact(o, powiu(p,e));
      y = grp->pow(E, a, t);
    }
    if (grp->equal1(y)) o = t;
    else {
      for (j = 1; j < e; j++)
      {
        y = grp->pow(E, y, p);
        if (grp->equal1(y)) break;
      }
      if (j < e) {
        if (j > 1) p = powiu(p, j);
        o = mulii(t, p);
      }
    }
  }
  return gerepilecopy(av, o);
}

/*Find the exact order of a assuming a^o==1, return [order,factor(order)] */
GEN
gen_factored_order(GEN a, GEN o, void *E, const struct bb_group *grp)
{
  pari_sp av = avma;
  long i, l, ind;
  GEN m, F, P;

  m = dlog_get_ordfa(o);
  if (!m) pari_err_TYPE("gen_factored_order [missing order]",a);
  o = gel(m,1);
  m = gel(m,2); l = lg(m[1]);
  P = cgetg(l, t_COL); ind = 1;
  F = cgetg(l, t_COL);
  for (i = l-1; i; i--)
  {
    GEN t, y, p = gcoeff(m,i,1);
    long j, e = itos(gcoeff(m,i,2));
    if (l == 1) {
      t = gen_1;
      y = a;
    } else {
      t = diviiexact(o, powiu(p,e));
      y = grp->pow(E, a, t);
    }
    if (grp->equal1(y)) o = t;
    else {
      for (j = 1; j < e; j++)
      {
        y = grp->pow(E, y, p);
        if (grp->equal1(y)) break;
      }
      gel(P,ind) = p;
      gel(F,ind) = utoipos(j);
      if (j < e) {
        if (j > 1) p = powiu(p, j);
        o = mulii(t, p);
      }
      ind++;
    }
  }
  setlg(P, ind);
  setlg(F, ind);
  return gerepilecopy(av, mkvec2(o, mkmat2(P,F)));
}

/*******************************************************************/
/*                                                                 */
/*                          n-th ROOT                              */
/*                                                                 */
/*******************************************************************/
/* Assume l is prime. Return a generator of the l-th Sylow and set *zeta to an element
 * of order l.
 *
 * q = l^e*r, e>=1, (r,l)=1
 * UNCLEAN */
static GEN
gen_lgener(GEN l, long e, GEN r,GEN *zeta, void *E, const struct bb_group *grp)
{
  const pari_sp av1 = avma;
  GEN m, m1;
  long i;
  for (;; avma = av1)
  {
    m1 = m = grp->pow(E, grp->rand(E), r);
    if (grp->equal1(m)) continue;
    for (i=1; i<e; i++)
    {
      m = grp->pow(E,m,l);
      if (grp->equal1(m)) break;
    }
    if (i==e) break;
  }
  *zeta = m; return m1;
}

/* Let G be a cyclic group of order o>1. Returns a (random) generator */

GEN
gen_gener(GEN o, void *E, const struct bb_group *grp)
{
  GEN F = dlog_get_ordfa(o);
  GEN N = gel(F,1), pr = gel(F,2), z = NULL;
  long i, lpr = lg(gel(pr,1));
  pari_sp av = avma, lim = stack_lim(av,2);
  for (i = 1; i < lpr; i++)
  {
    GEN l = gcoeff(pr,i,1);
    long e = itos(gcoeff(pr,i,2));
    GEN r = diviiexact(N,powis(l,e));
    GEN zetan, zl = gen_lgener(l,e,r,&zetan,E,grp);
    z = i==1 ? zl: grp->mul(E,z, zl);
    if (low_stack(lim, stack_lim(av,2)))
    { /* n can have lots of prime factors*/
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_sqrtn");
      z = gerepileupto(av, z);
    }
  }
  return gerepileupto(av, z);
}

/* solve x^l = a , l prime in G of order q.
 *
 * q =  (l^e)*r, e >= 1, (r,l) = 1
 * y is not an l-th power, hence generates the l-Sylow of G
 * m = y^(q/l) != 1 */
static GEN
gen_Shanks_sqrtl(GEN a, GEN l, GEN q,long e, GEN r, GEN y, GEN m,void *E, const struct bb_group *grp)
{
  pari_sp av = avma,lim;
  long k;
  GEN p1, u1, u2, v, w, z, dl;

  (void)bezout(r,l,&u1,&u2);
  v = grp->pow(E,a,u2);
  w = grp->pow(E,a,Fp_mul(negi(u1),r,q));
  lim = stack_lim(av,1);
  while (!grp->equal1(w))
  {
    k = 0;
    p1 = w;
    do
    {
      z = p1; p1 = grp->pow(E,p1,l);
      k++;
    } while(!grp->equal1(p1));
    if (k==e) { avma = av; return NULL; }
    dl = gen_plog(z,m,l,E,grp,NULL);
    if (typ(dl) != t_INT) { avma = av; return NULL; }
    dl = negi(dl);
    p1 = grp->pow(E,y, Fp_mul(dl,powiu(l,e-k-1),q));
    m = grp->pow(E,m,dl);
    e = k;
    v = grp->mul(E,p1,v);
    y = grp->pow(E,p1,l);
    w = grp->mul(E,y,w);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_sqrtl");
      gerepileall(av,4, &y,&v,&w,&m);
    }
  }
  return gerepilecopy(av, v);
}
/* Return one solution of x^n = a in a cyclic group of order q
 *
 * 1) If there is no solution, return NULL.
 *
 * 2) If there is a solution, there are exactly m of them [m = gcd(q-1,n)].
 * If zetan!=NULL, *zetan is set to a primitive m-th root of unity so that
 * the set of solutions is { x*zetan^k; k=0..m-1 }
 */
GEN
gen_Shanks_sqrtn(GEN a, GEN n, GEN q, GEN *zetan, void *E, const struct bb_group *grp)
{
  pari_sp ltop = avma, lim;
  GEN m, u1, u2, z;
  int is_1;

  if (is_pm1(n))
  {
    if (zetan) *zetan = grp->pow(E,a,gen_0);
    return gcopy(a);
  }
  is_1 = grp->equal1(a);
  if (is_1 && !zetan) return gcopy(a);

  m = bezout(n,q,&u1,&u2);
  z = grp->pow(E,a,gen_0);
  lim = stack_lim(ltop,1);
  if (!is_pm1(m))
  {
    GEN F = Z_factor(m);
    long i, j, e;
    GEN r, zeta, y, l;
    pari_sp av1 = avma;
    for (i = lg(F[1])-1; i; i--)
    {
      l = gcoeff(F,i,1);
      j = itos(gcoeff(F,i,2));
      e = Z_pvalrem(q,l,&r);
      y = gen_lgener(l,e,r,&zeta,E,grp);
      if (zetan) z = grp->mul(E,z, grp->pow(E,y,powiu(l,e-j)));
      if (!is_1) {
        do
        {
          a = gen_Shanks_sqrtl(a,l,q,e,r,y,zeta,E,grp);
          if (!a) { avma = ltop; return NULL;}
        } while (--j);
      }
      if (low_stack(lim, stack_lim(ltop,1)))
      { /* n can have lots of prime factors*/
        if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_sqrtn");
        gerepileall(av1, zetan? 2: 1, &a, &z);
      }
    }
  }
  if (!equalii(m, n))
    a = grp->pow(E,a,modii(u1,q));
  if (zetan)
  {
    *zetan = z;
    gerepileall(ltop,2,&a,zetan);
  }
  else /* is_1 is 0: a was modified above -> gerepileupto valid */
    a = gerepileupto(ltop, a);
  return a;
}

/*******************************************************************/
/*                                                                 */
/*               structure of groups with pairing                  */
/*                                                                 */
/*******************************************************************/

static GEN
ellgroup_d2(GEN N, GEN d)
{
  GEN r = gcdii(N, d);
  GEN F1 = gel(Z_factor(r), 1);
  long i, j, l1 = lg(F1);
  GEN F = cgetg(3, t_MAT);
  gel(F,1) = cgetg(l1, t_COL);
  gel(F,2) = cgetg(l1, t_COL);
  for (i = 1, j = 1; i < l1; ++i)
  {
    long v = Z_pval(N, gel(F1, i));
    if (v<=1) continue;
    gcoeff(F, j  , 1) = gel(F1, i);
    gcoeff(F, j++, 2) = stoi(v);
  }
  setlg(F[1],j); setlg(F[2],j);
  return j==1 ? NULL : mkvec2(factorback(F), F);
}

GEN
gen_ellgroup(GEN N, GEN d, GEN *pt_m, void *E, const struct bb_group *grp,
             GEN pairorder(void *E, GEN P, GEN Q, GEN m, GEN F))
{
  pari_sp av = avma;
  GEN N0, N1, F = ellgroup_d2(N, d);
  if (!F) {avma = av; return mkveccopy(N);}
  N0 = gel(F,1); N1 = diviiexact(N, N0);
  while(1)
  {
    pari_sp av2 = avma;
    GEN P, Q, d, s, t, m;

    P = grp->pow(E,grp->rand(E), N1);
    s = gen_order(P, F, E, grp); if (equalii(s, N0)) {avma = av; return mkveccopy(N);}

    Q = grp->pow(E,grp->rand(E), N1);
    t = gen_order(Q, F, E, grp); if (equalii(t, N0)) {avma = av; return mkveccopy(N);}

    m = lcmii(s, t);
    d = pairorder(E, P, Q, m, F);
    /* structure is [N/d, d] iff m d == N0. Note that N/d = N1 m */
    if (is_pm1(d) && equalii(m, N0)) {avma = av; return mkveccopy(N);}
    if (equalii(mulii(m, d), N0))
    {
      GEN g = mkvec2(mulii(N1,m), d);
      if (pt_m) *pt_m = m;
      gerepileall(av,pt_m?2:1,&g,pt_m);
      return g;
    }
    avma = av2;
  }
}

GEN
gen_ellgens(GEN d1, GEN d2, GEN m, void *E, const struct bb_group *grp,
             GEN pairorder(void *E, GEN P, GEN Q, GEN m, GEN F))
{
  GEN F = mkvec2(d1, Z_factor(d1));
  GEN dm = diviiexact(d1,m);
  pari_sp av = avma;
  while(1)
  {
    GEN P = grp->rand(E);
    GEN s = gen_order(P, F, E, grp);
    if (equalii(s, d1))
    {
      GEN Q = grp->rand(E);
      GEN d = pairorder(E, grp->pow(E, P, dm), grp->pow(E, Q, dm), m, F);
      if (equalii(d, d2)) return mkvec2(P,Q);
    }
    avma = av;
  }
}
