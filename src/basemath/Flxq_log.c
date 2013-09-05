/* $Id$

Copyright (C) 2013 The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/* Let [ be the following order on Fp: 0 [ p-1 [ 1 [ p-2 [ 2 .. [ p\2
and [[ the lexicographic extension of [ to Fp[T]. Compute the
isomorphism (Fp[X], [[) -> (N,<) on P */

static long
Flx_cindex(GEN P, ulong p)
{
  long d = degpol(P), i;
  ulong s = 0, p2 = (p-1)>>1;
  for (i = 0; i <= d; ++i)
  {
    ulong x = P[d-i+2];
    if (x<=p2) x = 2*x; else x = 1+2*(p-1-x);
    s = p*s+x;
  }
  return s;
}

/* Compute the polynomial immediately after t for the [[ order */

static void
Flx_cnext(GEN t, ulong p)
{
  long i;
  long p2 = p>>1;
  for(i=2;;i++)
    if (t[i]==p2)
      t[i]=0;
    else
    {
      t[i] = t[i]<p2 ? p-1-t[i]: p-t[i];
      break;
    }
}

static GEN
smallirred_Flx(long p, ulong n, long sv)
{
  long i;
  GEN a = zero_zv(n+2);
  a[1] = sv; a[n+2] = 1;
  while (!Flx_is_irred(a, p))
   for(i=2;;i++)
     if (++a[i]==p) a[i]=0;
     else break;
  return a;
}

struct Flxq_log_rel
{
  long nbrel;
  GEN rel;
  long nb;
  long r, off,nbmax;
  ulong nbtest;
};

static GEN
factorel(GEN h, ulong p)
{
  GEN F = Flx_factcantor(h, p, 0);
  GEN F1 = gel(F, 1), F2 = gel(F, 2);
  long i, l1 = lg(F1)-1;
  GEN p2 = cgetg(l1+1, t_VECSMALL);
  GEN e2 = cgetg(l1+1, t_VECSMALL);
  for (i = 1; i <= l1; ++i)
  {
    p2[i] = Flx_cindex(gel(F1, i), p);
    e2[i] = F2[i];
  }
  return mkmat2(p2, e2);
}

static long
Flx_addifsmooth3(pari_sp *av, struct Flxq_log_rel *r, GEN h, long u, long v, long w, ulong p)
{
  long off = r->off;
  r->nbtest++;
  if (Flx_is_smooth(h, r->r, p))
  {
    GEN z = factorel(h, p);
    if (v<0)
      z = mkmat2(vecsmall_append(gel(z,1),off+u),vecsmall_append(gel(z,2),-1));
    else
      z = famatsmall_reduce(mkmat2(
            vecsmall_concat(gel(z,1),mkvecsmall3(off+u,off+v,off+w)),
            vecsmall_concat(gel(z,2),mkvecsmall3(-1,-1,-1))));
    gel(r->rel,++r->nbrel) = gerepilecopy(*av,z);
    *av = avma;
  } else avma = *av;
  return r->nbrel==r->nb || r->nbrel==r->nbmax;
}

static void
Flx_renormalize_inplace(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (x[i]) break;
  setlg(x, i+1);
}

/*
   Let T*X^e=C^3-R
   a+b+c = 0
   (C+a)*(C+b)*(C+c) = C^3+ (a*b+a*c+b*c)*C+a*b*c
   = R + (a*b+a*c+b*c)*C+a*b*c
   = R + (a*b-c^2)*C+a*b*c
 */
static void
Flxq_log_cubic(struct Flxq_log_rel *r, GEN C, GEN R, ulong p)
{
  long l = lg(C);
  GEN a = zero_zv(l); /*We allocate one extra word to catch overflow*/
  GEN b = zero_zv(l);
  pari_sp av = avma;
  long i,j,k, dh=0;
  for(i=0; ; i++, Flx_cnext(a, p))
  {
    Flx_renormalize_inplace(a, l+1);
    if (DEBUGLEVEL && (i&127)==127)
      err_printf("%ld%%[%ld] ",200*(r->nbrel-1)/r->nbmax, dh);
    r->nb++;
    if (Flx_addifsmooth3(&av, r, Flx_add(a, C, p), i, -1, -1, p)) return;
    for(j=2; j<=l; j++) b[j] = 0;
    for(j=0; j<=i; j++, Flx_cnext(b, p))
    {
      GEN h,c;
      GEN pab,pabc,pabc2;
      Flx_renormalize_inplace(b, l+1);
      c = Flx_neg(Flx_add(a,b,p),p);
      k = Flx_cindex(c, p);
      if (k > j) continue;
      pab  = Flx_mul(a, b, p);
      pabc = Flx_mul(pab,c,p);
      pabc2= Flx_sub(pab,Flx_sqr(c,p),p);
      h = Flx_add(R,Flx_add(Flx_mul(C,pabc2,p),pabc,p), p);
      h = Flx_normalize(h, p);
      dh = maxss(dh,degpol(h));
      if (Flx_addifsmooth3(&av, r, h, i, j, k, p)) return;
    }
  }
}

static GEN
Flxq_log_find_rel(GEN b, long r, GEN T, ulong p, GEN *g, long *e)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  while (1)
  {
    GEN M;
    *g = Flxq_mul(*g, b, T, p); (*e)++;
    M = Flx_halfgcd(*g,T,p);
    if (Flx_is_smooth(gcoeff(M,1,1), r, p))
    {
      GEN z = Flx_add(Flx_mul(gcoeff(M,1,1),*g,p), Flx_mul(gcoeff(M,1,2),T,p),p);
      if (Flx_is_smooth(z, r, p))
      {
        GEN F = factorel(z, p);
        GEN G = factorel(gcoeff(M,1,1), p);
        GEN rel = mkmat2(vecsmall_concat(gel(F, 1),gel(G, 1)),
                         vecsmall_concat(gel(F, 2),zv_neg(gel(G, 2))));
        gerepileall(av,2,g,&rel); return rel;
      }
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flxq_log_find_rel");
      *g = gerepilecopy(av, *g);
    }
  }
}

/* Generalised Odlyzko formulae ( EUROCRYPT '84, LNCS 209, pp. 224-314, 1985. ) */
/* Return the number of monic, k smooth, degree n polynomials for k=1..r */
static GEN
smoothness_vec(ulong p, long r, long n)
{
  long i,j,k;
  GEN R = cgetg(r+1, t_VEC);
  GEN V = cgetg(n+1, t_VEC);
  for (j = 1; j <= n; ++j)
    gel(V, j) =  binomialuu(p+j-1,j);
  gel(R, 1) = gel(V, n);
  for (k = 2; k <= r; ++k)
  {
    GEN W = cgetg(n+1, t_VEC);
    GEN Ik = ffnbirred(utoi(p),k);
    for (j = 1; j <= n; ++j)
    {
      long l = j/k;
      GEN s = gen_0;
      pari_sp av2 = avma;
      if (l*k == j)
      {
        s = binomial(addis(Ik,l-1), l);
        l--;
      }
      for (i = 0; i <= l; ++i)
        s = addii(s, mulii(gel(V, j-k*i), binomial(addis(Ik,i-1), i)));
      gel(W, j) = gerepileuptoint(av2, s);
    }
    V = W;
    gel(R, k) = gel(V, n);
  }
  return R;
}

/* Solve N^2*pr/6 + N*prC = N+fb
   N^2*pr/6 + N*(prC-1) -fb = 0
 */

static GEN
smooth_cost(GEN fb, GEN pr, GEN prC)
{
  GEN a = gdivgs(pr,6);
  GEN b = gsubgs(prC,1);
  GEN c = gneg(fb);
  GEN vD = gsqrt(gsub(gsqr(b),gmul2n(gmul(a,c),2)),BIGDEFAULTPREC);
  return ceil_safe(gdiv(gsub(vD,b),gmul2n(a,1)));
}

/* Return best choice of r.
   We loop over d until there is sufficiently many triples (a,b,c) (a+b+c=0)
   of degree <=d with respect to the probability of smoothness of (a*b-c^2)*C
 */

static GEN
smooth_best(long p, long n, long *pt_r, long *pt_nb)
{
  pari_sp av = avma, av2;
  GEN bestc = NULL;
  long bestr = 0, bestFB = 0;
  long r,d, dC = (n+2)/3;
  for (r = 1; r < dC; ++r)
  {
    GEN fb = ffsumnbirred(utoi(p), r);
    GEN smoothC = smoothness_vec(p,r,dC);
    GEN prC = gdiv(gel(smoothC,r), powuu(p,dC));
    ulong rels = 0;
    av2 = avma;
    for(d=0; d<dC && rels < ULONG_MAX; d++)
    {
      GEN c;
      long dt = dC+2*d;
      GEN smooth = smoothness_vec(p,r,dt);
      GEN pr = gdiv(gel(smooth,r), powuu(p,dt));
      GEN FB = addii(fb,powuu(p,d));
      GEN N = smooth_cost(subiu(FB,rels),pr,prC);
      GEN Nmax = powuu(p,d+1);
      if (gcmp(N,Nmax) >= 0)
      {
        rels = itou_or_0(addui(rels, gceil(gmul(gdivgs(sqri(Nmax),6),pr))));
        if (!rels) rels = ULONG_MAX;
        avma = av2;
        continue;
      }
      c = gdivgs(addii(powuu(p,2*d),sqri(N)),6);
      FB = addii(FB,N);
      if ((!bestc || gcmp(gmul2n(c,r), gmul2n(bestc,bestr)) < 0))
      {
        if (DEBUGLEVEL)
          err_printf("d=%ld r=%ld fb=%Ps early rels=%lu P=%.5Pe -> C=%.5Pe \n"
                     ,dt,r,FB,rels,pr,c);
        bestc = c;
        bestr = r;
        bestFB = itos_or_0(FB);
      }
      break;
    }
  }
  *pt_r=bestr;
  *pt_nb=bestFB;
  return bestc ? gerepileupto(av, gceil(bestc)): NULL;
}

GEN
Flxq_log_index(GEN a0, GEN b0, GEN m, GEN T0, ulong p)
{
  pari_sp av = avma;
  struct Flxq_log_rel rel;
  long nbi, e, AV;
  GEN g,aa;
  GEN M, V, A, S, T, a, b;
  pari_timer ti;
  long n = get_Flx_degree(T0), r, nb;
  GEN cost = smooth_best(p, n, &r, &nb);
  GEN cost_rho = sqrti(shifti(m,2));
  if (!cost || gcmp(cost,cost_rho)>=0) { avma = av; return NULL; }
  nbi = itos(ffsumnbirred(stoi(p), r));
  if (DEBUGLEVEL)
  {
    err_printf("Size FB=%ld, looking for %ld relations, %Ps tests needed\n", nbi, nb,cost);
    timer_start(&ti);
  }
  T = smallirred_Flx(p,n,get_Flx_var(T0));
  S = Flx_ffisom(T0,T,p);
  a = Flx_Flxq_eval(a0, S, T, p);
  b = Flx_Flxq_eval(b0, S, T, p);
  if (DEBUGLEVEL) timer_printf(&ti," model change");
  AV = 0; aa=a;
  M = cgetg(2*nb+1, t_VEC);
  V = zero_zv(2*nb);
  e = 0; g = pol1_Flx(b[1]);
  gel(M, 1) = Flxq_log_find_rel(b, r, T, p, &g, &e);
  V[1] = e;
  if (DEBUGLEVEL) timer_printf(&ti,"log generator");
  rel.rel = M;
  rel.nbrel = 1;
  rel.r = r; rel.off = 3*upowuu(p,r);
  rel.nb = nbi; rel.nbmax=2*nb; rel.nbtest=0;

  if (rel.nbrel<rel.nb)
  {
    GEN C = Flx_shift(pol1_Flx(get_Flx_var(T)), (n+2)/3);
    GEN R = Flxq_powu(C,3,T,p);
    Flxq_log_cubic(&rel, C, R, p);
  }
  setlg(M,1+rel.nbrel);
  setlg(V,1+rel.nbrel);
  if (DEBUGLEVEL)
  {
    err_printf("\n");
    timer_printf(&ti," %ld relations, %ld generators (%ld tests)",rel.nbrel,rel.nb,rel.nbtest);
  }
  while (1)
  {
    pari_sp av2;
    GEN R;
    if (DEBUGLEVEL) timer_start(&ti);
    A = Flxq_log_find_rel(b, r, T, p, &aa, &AV);
    if (DEBUGLEVEL) timer_printf(&ti,"log element");
    av2 = avma;
    R = FpMs_FpCs_solve_safe(M,A,rel.off+rel.nb*3,m);
    if (!R) continue;
    if (typ(R) == t_COL)
    {
      GEN l = Fp_sub(FpV_dotproduct(zv_to_ZV(V), R, m), utoi(AV), m);
      e += rel.nbtest;
      if (DEBUGLEVEL)
        err_printf("%lu test.,%lu total, complexity=O(x^%Ps)\n", rel.nbtest,e,
            gdiv(glog(utoi(e), DEFAULTPREC), glog(m, DEFAULTPREC)));
      if (degpol(Flxq_mul(a0, Flxq_pow(b0,Fp_neg(l,m),T0,p),T0,p))!=0)
        pari_err_BUG("Flxq_log_index");
      return gerepileuptoint(av, l);
    }
    else
    {
      long k = R[1];
      avma = av2;
      if (DEBUGLEVEL) timer_start(&ti);
      gel(M, k) = Flxq_log_find_rel(b, r, T, p, &g, &e);
      if (DEBUGLEVEL) timer_printf(&ti,"changing col %ld", k);
      V[k] = e;
    }
  }
}
