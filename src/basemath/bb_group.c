/* $Id$

Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

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
GEN
gen_Pollard_log(GEN x, GEN g, GEN q, void *E, const struct bb_group *grp,
    GEN easy(void*E, GEN, GEN, GEN))
{
  pari_sp av=avma, lim=stack_lim(av,2);
  GEN A,B,l;
  ulong h=0;
  if (grp->hash==NULL) return gen_Shanks_log(x,g,q,E,grp,easy);
  if (easy)
  {
    GEN e = easy(E, x, g, q);
    if (e) return e;
  }
  if (grp->cmp1(x)) {avma=av; return gen_0;}
  if (!grp->cmp(x,g)) {avma=av; return gen_1;}
  long i,imax=itou(sqrti(shifti(q,4)));
  do {
 rho_restart:
    A = B = mkvec3(grp->pow(E,g,gen_0),gen_0,gen_0);
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
GEN
gen_Shanks_log(GEN x, GEN g0,GEN q, void *E, const struct bb_group *grp,
    GEN easy(void*E, GEN, GEN, GEN))
{
  pari_sp av=avma,av1,lim;
  long lbaby,i,k;
  GEN p1,smalltable,giant,perm,v,g0inv;
  if (easy)
  {
    GEN e = easy(E, x, g0, q);
    if (e) return e;
  }
  if (grp->cmp1(x)) {avma=av; return gen_0;}
  if (!grp->cmp(x,g0)) {avma=av; return gen_1;}
  p1 = sqrti(q);
  if (cmpiu(p1,LGBITS) >= 0)
    pari_err(talker,"order too large in gen_Shanks_log");
  lbaby = itos(p1)+1; smalltable = cgetg(lbaby+1,t_VEC);
  g0inv = grp->pow(E,g0,gen_m1);

  for (p1=x, i=1;;i++)
  {
    av1 = avma;
    if (grp->cmp1(p1)) { avma = av; return stoi(i-1); }
    gel(smalltable,i) = p1; if (i==lbaby) break;
    p1 = gerepileupto(av1, grp->mul(E,p1,g0inv));
  }
  p1 = giant = grp->mul(E,x,grp->pow(E, p1, gen_m1));
  gen_sort_inplace(smalltable, (void*)grp->cmp, &cmp_nodata, &perm);

  av1 = avma; lim=stack_lim(av1,2);
  for (k=1;;k++)
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

  if (grp->cmp(g, a)==0) return gen_1; /* frequent special case */
  if (easy)
  {
    GEN e = easy(E, a, g, ord);
    if (e) return e;
  }
  if (typ(ord) == t_MAT)
  {
    fa = ord;
    ord= factorback(fa);
  }
  else
    fa = Z_factor(ord);
  ex = gel(fa,2);
  fa = gel(fa,1);
  l = lg(fa);
  ginv = grp->pow(E,g,gen_m1);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    q = gel(fa,i);
    e = itos(gel(ex,i));
    if (DEBUGLEVEL>5)
      fprintferr("Pohlig-Hellman: DL mod %Ps^%ld\n",q,e);
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
      b = gen_Pollard_log(b, g_q, q, E, grp, easy);
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
gen_eltorder(GEN a, GEN o, void *E, const struct bb_group *grp)
{
  pari_sp av = avma;
  long i;
  GEN m;

  if (typ(o) == t_MAT)
  {
    m = o;
    o = factorback(m);
    if (typ(o) != t_INT)
      pari_err(talker, "incorrect order in gen_eltorder: %Ps", o);
  }
  else
    m = Z_factor(o);
  for (i = lg(m[1])-1; i; i--)
  {
    GEN t, y, p = gcoeff(m,i,1);
    long j, e = itos(gcoeff(m,i,2));
    t = diviiexact(o, powiu(p,e));
    y = grp->pow(E, a, t);
    if (grp->cmp1(y)) o = t;
    else {
      for (j = 1; j < e; j++)
      {
	y = grp->pow(E, y, p);
	if (grp->cmp1(y)) break;
      }
      if (j > 1) p = powiu(p, j);
      o = mulii(t, p);
    }
  }
  return gerepilecopy(av, o);
}

/*******************************************************************/
/*                                                                 */
/*                          n-th ROOT                              */
/*                                                                 */
/*******************************************************************/
/* Assume l is prime. Return a non l-th power and set *zeta to an element
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
    if (grp->cmp1(m)) continue;
    for (i=1; i<e; i++)
    {
      m = grp->pow(E,m,l);
      if (grp->cmp1(m)) break;
    }
    if (i==e) break;
  }
  *zeta = m; return m1;
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
  while (!grp->cmp1(w))
  {
    k = 0;
    p1 = w;
    do
    {
      z = p1; p1 = grp->pow(E,p1,l);
      k++;
    } while(!grp->cmp1(p1));
    if (k==e) { avma = av; return NULL; }
    dl = negi(gen_Shanks_log(z,m,l,E,grp,NULL));
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
  is_1 = grp->cmp1(a);
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

