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
/*               SUBFIELDS OF A NUMBER FIELD                       */
/*   J. Klueners and M. Pohst, J. Symb. Comp. (1996), vol. 11      */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
extern GEN matrixpow(long n, long m, GEN y, GEN P,GEN l);
extern GEN Fp_factor_irred(GEN P,GEN l, GEN Q);
extern GEN FpX_rand(long d1, long v, GEN p);
extern GEN hensel_lift_fact(GEN pol, GEN Q, GEN T, GEN p, GEN pe, long e);

static GEN print_block_system(long N,GEN Y,long d,GEN vbs,long maxl);

/* Computation of potential block systems of given size d associated to a
 * rational prime p: give a row vector of row vectors containing the
 * potential block systems of imprimitivity; a potential block system is a
 * vector of row vectors (enumeration of the roots).
 */
#define BIL 32 /* for 64bit machines also */
static GEN
calc_block(long N,GEN Z,long d,GEN Y,GEN vbs,ulong maxl)
{
  long r,lK,i,j,t,tp,T,lpn,u,nn,lnon,lY;
  GEN K,n,non,pn,pnon,e,Yp,Zp,Zpp;

  if (DEBUGLEVEL>3)
  {
    long l = vbs? lg(vbs): 0;
    fprintferr("avma = %ld, lg(Z) = %ld, lg(Y) = %ld, lg(vbs) = %ld\n",
               avma,lg(Z),lg(Y),l);
    if (DEBUGLEVEL > 5)
    {
      fprintferr("Z = %Z\n",Z);
      fprintferr("Y = %Z\n",Y);
      if (DEBUGLEVEL > 7) fprintferr("vbs = %Z\n",vbs);
    }
  }
  r=lg(Z); lnon = min(BIL, r);
  e    = new_chunk(BIL);
  n    = new_chunk(r);
  non  = new_chunk(lnon);
  pnon = new_chunk(lnon);
  pn   = new_chunk(lnon);
  Zp   = cgetg(lnon,t_VEC);
  Zpp  = cgetg(lnon,t_VEC);
  for (i=1; i<r; i++) n[i] = lg(Z[i])-1;

  K=divisors(stoi(n[1])); lK=lg(K);
  for (i=1; i<lK; i++)
  {
    long  ngcd = n[1], k = itos((GEN)K[i]), dk = d*k;
    lpn=0;
    for (j=2; j<r; j++)
      if (n[j]%k == 0)
      {
        if (++lpn >= BIL) err(talker,"overflow in calc_block");
        pn[lpn] = n[j]; pnon[lpn] = j;
        ngcd = cgcd(ngcd, n[j]);
      }
    if (dk % ngcd) continue;
    T = 1<<lpn; if (!lpn) lpn = 1;
    for (t=0; t<T; t++)
    {
      for (nn=n[1],tp=t, u=1; u<=lpn; u++,tp>>=1)
      {
        if (tp&1) { nn += pn[u]; e[u]=1; } else e[u]=0;
      }
      if (dk == nn)
      {
	long av=avma;
        int Z_equal_Zp = 1;

        for (j=1; j<lnon; j++) non[j]=0;
        Zp[1]=Z[1];
	for (u=2,j=1; j<=lpn; j++)
	  if (e[j])
          {
            Zp[u]=Z[pnon[j]]; non[pnon[j]]=1;
            if (Zp[u] != Z[u]) Z_equal_Zp = 0;
            u++;
          }
        setlg(Zp, u);
        lY=lg(Y); Yp = cgetg(lY+1,t_VEC);
        for (j=1; j<lY; j++) Yp[j]=Y[j];
	Yp[lY]=(long)Zp;
        if (r == u && Z_equal_Zp)
	  vbs = print_block_system(N,Yp,d,vbs,maxl);
	else
	{
	  for (u=1,j=2; j<r; j++)
	    if (!non[j]) Zpp[u++] = Z[j];
          setlg(Zpp, u);
	  vbs = calc_block(N,Zpp,d,Yp,vbs,maxl);
	}
        if (vbs && (ulong)lg(vbs) > maxl) return vbs;
        avma=av;
      }
    }
  }
  return vbs;
}

static GEN
potential_block_systems(long N, long d, GEN n, ulong maxl)
{
  long r, i, j, k;
  gpmem_t av=avma;
  GEN p1,vbs,Z;

  r=lg(n); Z=cgetg(r,t_VEC);
  for (k=0,i=1; i<r; i++)
  {
    p1=cgetg(n[i]+1,t_VECSMALL); Z[i]=(long)p1;
    for (j=1; j<=n[i]; j++) p1[j]= ++k;
  }
  vbs=calc_block(N,Z,d, cgetg(1,t_VEC), NULL, maxl);
  avma=av; return vbs;
}

/* product of permutations. Put the result in perm1. */
static void
perm_mul_i(GEN perm1,GEN perm2)
{
  long i, N = lg(perm1);
  gpmem_t av = avma;
  GEN perm=new_chunk(N);
  for (i=1; i<N; i++) perm[i]=perm1[perm2[i]];
  for (i=1; i<N; i++) perm1[i]=perm[i];
  avma=av;
}

/* cy is a cycle; compute cy^l as a permutation */
static GEN
cycle_power_to_perm(GEN perm,GEN cy,long l)
{
  long lp,i,j,b, N = lg(perm), lcy = lg(cy)-1;

  lp = l % lcy;
  for (i=1; i<N; i++) perm[i] = i;
  if (lp)
  {
    gpmem_t av = avma;
    GEN p1 = new_chunk(N);
    b = cy[1];
    for (i=1; i<lcy; i++) b = (perm[b] = cy[i+1]);
    perm[b] = cy[1];
    for (i=1; i<N; i++) p1[i] = perm[i];

    for (j=2; j<=lp; j++) perm_mul_i(perm,p1);
    avma = av;
  }
  return perm;
}

/* image du block system D par la permutation perm */
static GEN
im_block_by_perm(GEN D,GEN perm)
{
  long i,j,lb,lcy;
  GEN Dn,cy,p1;

  lb=lg(D); Dn=cgetg(lb,t_VEC);
  for (i=1; i<lb; i++)
  {
    cy=(GEN)D[i]; lcy=lg(cy);
    Dn[i]=lgetg(lcy,t_VECSMALL); p1=(GEN)Dn[i];
    for (j=1; j<lcy; j++) p1[j] = perm[cy[j]];
  }
  return Dn;
}

/* cy is a cycle; recturn cy(a) */
static long
im_by_cy(long a,GEN cy)
{
  long k, l = lg(cy);

  k=1; while (k<l && cy[k] != a) k++;
  if (k == l) return a;
  k++; if (k == l) k = 1;
  return cy[k];
}

/* vbs[0] = current cardinality+1, vbs[1] = max number of elts */
static GEN
append_vbs(GEN vbs, GEN D)
{
  long l,maxl,i,j,n, lD = lg(D);
  GEN Dn, last;

  n = 0; for (i=1; i<lD; i++) n += lg(D[i]);
  Dn = (GEN)gpmalloc((lD + n) * sizeof(long));
  last = Dn + lD; Dn[0] = D[0];
  for (i=1; i<lD; i++)
  {
    GEN cy = (GEN)D[i], cn = last;
    for (j=0; j<lg(cy); j++) cn[j] = cy[j];
    Dn[i] = (long)cn; last = cn + j;
  }

  if (!vbs)
  {
    maxl = 1024;
    vbs = (GEN)gpmalloc((2 + maxl)*sizeof(GEN));
    *vbs = maxl; vbs++; setlg(vbs, 1);
  }
  l = lg(vbs); maxl = vbs[-1];
  if (l == maxl)
  {
    vbs = (GEN)gprealloc((void*)(vbs-1), (2 + (maxl<<1))*sizeof(GEN));
    *vbs = maxl<<1; vbs++; setlg(vbs, 1);
  }
  if (DEBUGLEVEL>5) fprintferr("appending D = %Z\n",D);
  vbs[l] = (long)Dn; setlg(vbs, l+1); return vbs;
}

GEN
myconcat(GEN D, long a)
{
  long i,l = lg(D);
  GEN x = cgetg(l+1,t_VECSMALL);
  for (i=1; i<l; i++) x[i]=D[i];
  x[l] = a; return x;
}

void
myconcat2(GEN D, GEN a)
{
  long i,l = lg(D), m = lg(a);
  GEN x = D + (l-1);
  for (i=1; i<m; i++) x[i]=a[i];
  setlg(D, l+m-1);
}

static GEN
print_block_system(long N,GEN Y,long d,GEN vbs,long maxl)
{
  long a,i,j,l,ll,*k,*n,lp,**e,u,v,*t,ns, r = lg(Y);
  GEN D,De,Z,cyperm,perm,p1,empty;

  if (DEBUGLEVEL>5) fprintferr("Y = %Z\n",Y);
  empty = cgetg(1,t_VEC);
  n = new_chunk(N+1);
  D = cgetg(N+1, t_VEC); setlg(D,1);
  t=new_chunk(r+1); k=new_chunk(r+1); Z=cgetg(r+1,t_VEC);
  for (ns=0,i=1; i<r; i++)
  {
    GEN Yi = (GEN)Y[i], cy;
    long ki = 0, si = lg(Yi)-1;

    for (j=1; j<=si; j++) { n[j]=lg(Yi[j])-1; ki += n[j]; }
    ki /= d;
    De=cgetg(ki+1,t_VEC);
    for (j=1; j<=ki; j++) De[j]=(long)empty;
    for (j=1; j<=si; j++)
    {
      cy = (GEN)Yi[j]; a = cy[1];
      for (l=1,lp=0; l<=n[j]; l++)
      {
        lp++; if (lp>ki) lp = 1;
        a = im_by_cy(a, cy);
        De[lp] = (long)myconcat((GEN)De[lp], a);
      }
    }
    if (si>1 && ki>1)
    {
      ns++; t[ns]=si-1; k[ns]=ki;
      Z[ns]=lgetg(si,t_VEC); p1=(GEN)Z[ns];
      for (j=2; j<=si; j++) p1[j-1]=Yi[j];
    }
    myconcat2(D,De);
  }
  if (DEBUGLEVEL>2) { fprintferr("\nns = %ld\n",ns); flusherr(); }
  if (!ns) return append_vbs(vbs,D);

  setlg(Z, ns+1);
  e=(long**)new_chunk(ns+1);
  for (i=1; i<=ns; i++)
  {
    e[i]=new_chunk(t[i]+1);
    for (j=1; j<=t[i]; j++) e[i][j]=0;
  }
  cyperm = cgetg(N+1,t_VEC);
  perm = cgetg(N+1,t_VEC); i=ns;
  do
  {
    gpmem_t av = avma;
    if (DEBUGLEVEL>5)
    {
      for (l=1; l<=ns; l++)
      {
	for (ll=1; ll<=t[l]; ll++)
	  fprintferr("e[%ld][%ld] = %ld, ",l,ll,e[l][ll]);
	fprintferr("\n");
      }
      fprintferr("\n"); flusherr();
    }
    for (u=1; u<=N; u++) perm[u]=u;
    for (u=1; u<=ns; u++)
      for (v=1; v<=t[u]; v++)
	perm_mul_i(perm, cycle_power_to_perm(cyperm,gmael(Z,u,v),e[u][v]));
    vbs = append_vbs(vbs, im_block_by_perm(D,perm));
    if (lg(vbs) > maxl) return vbs;
    avma = av;

    e[ns][t[ns]]++;
    if (e[ns][t[ns]] >= k[ns])
    {
      j=t[ns]-1;
      while (j>=1 && e[ns][j] == k[ns]-1) j--;
      if (j>=1) { e[ns][j]++; for (l=j+1; l<=t[ns]; l++) e[ns][l]=0; }
      else
      {
	i=ns-1;
	while (i>=1)
	{
	  j=t[i];
	  while (j>=1 && e[i][j] == k[i]-1) j--;
	  if (j<1) i--;
          else
	  {
	    e[i][j]++;
	    for (l=j+1; l<=t[i]; l++) e[i][l]=0;
	    for (ll=i+1; ll<=ns; ll++)
              for (l=1; l<=t[ll]; l++) e[ll][l]=0;
            break;
	  }
	}
      }
    }
  }
  while (i>0);
  return vbs;
}

static GEN
polsimplify(GEN x)
{
  long i,lx = lgef(x);
  for (i=2; i<lx; i++)
    if (typ(x[i]) == t_POL) x[i] = (long)constant_term(x[i]);
  return x;
}

/* return 0 if |g[i]| > M[i] for some i; 1 otherwise */
static long
ok_coeffs(GEN g,GEN M)
{
  long i, lg = lgef(g)-1; /* g is monic, and cst term is ok */
  for (i=3; i<lg; i++)
    if (absi_cmp((GEN)g[i], (GEN)M[i]) > 0) return 0;
  return 1;
}

/* Return a polynomial g defining a potential subfield, or
 * 0: if p | d(g)
 * 1: if coeffs of g are too large
 * 2: same, detected by cheap d-1 test */
static GEN
cand_for_subfields(GEN A,GEN DATA,GEN *ptlistdelta)
{
  long N,m,i,j,d,lf;
  GEN M,T,pe,p,pol,fhk,g;
  GEN d_1_term,delta,listdelta,whichdelta,firstroot;

  pol=(GEN)DATA[1];
  p = (GEN)DATA[2];
  pe= (GEN)DATA[3];
  T = (GEN)DATA[4];
  fhk=(GEN)DATA[5];
  M = (GEN)DATA[8]; N=degpol(pol); m=lg(A)-1; d=N/m; /* m | M */
  firstroot = (GEN)DATA[13];

  delta = cgetg(m+1,t_VEC);
  lf = lg(firstroot);
  listdelta = cgetg(lf, t_VEC);
  whichdelta = cgetg(N+1, t_VECSMALL);
  d_1_term = gzero;
  for (i=1; i<=m; i++)
  {
    GEN Ai = (GEN)A[i], p1 = gun;
    for (j=1; j<=d; j++)
      p1 = FpXQ_mul(p1, (GEN)fhk[Ai[j]], T,pe);
    delta[i] = (long)p1;
    if (DEBUGLEVEL>2) fprintferr("delta[%ld] = %Z\n",i,p1);
    /* g = prod (X - delta[i])
     * if g o h = 0 (pol), we'll have h(Ai[j]) = delta[i] for all j */
    /* fk[k] belongs to block number whichdelta[k] */
    for (j=1; j<=d; j++) whichdelta[Ai[j]] = i;
    if (typ(p1) == t_POL) p1 = constant_term(p1);
    d_1_term = addii(d_1_term, p1);
  }
  d_1_term = centermod(d_1_term, pe); /* Tr(g) */
  if (absi_cmp(d_1_term, (GEN)M[3]) > 0) return gdeux; /* d-1 test */
  g = FqV_roots_to_pol(delta, T, pe, 0);
  g = centermod(polsimplify(g), pe); /* assume g in Z[X] */
  if (DEBUGLEVEL>2) fprintferr("pol. found = %Z\n",g);
  if (!ok_coeffs(g,M)) return gun;
  if (!FpX_is_squarefree(g, p)) return gzero;

  for (i=1; i<lf; i++) listdelta[i] = delta[whichdelta[firstroot[i]]];
  *ptlistdelta = listdelta; return g;
}

/* return U list of polynomials s.t U[i] = 1 mod fk[i] and 0 mod fk[j] for all
 * other j */
static GEN
get_bezout(GEN pol, GEN fk, GEN p)
{
  GEN A,B,d,u,v,bezout_coeff;
  long i, l = lg(fk);

  pol = FpX_red(pol, p);
  bezout_coeff = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    A = (GEN)fk[i];
    B = FpX_div(pol, A, p);
    d = FpX_extgcd(A,B,p, &u, &v);
    if (degpol(d) > 0) err(talker, "relatively prime polynomials expected");
    d = constant_term(d);
    if (!gcmp1(d))
    {
      d = mpinvmod(d, p);
      v = FpX_Fp_mul(v,d, p);
    }
    bezout_coeff[i] = (long)FpX_mul(B,v, p);
  } 
  return bezout_coeff;
}

/* assume x in Fq, return Tr_{Fq/Fp}(x) as a t_INT */
static GEN
trace(GEN x, GEN Trq, GEN p)
{
  long i, l;
  GEN s;
  if (typ(x) == t_INT) return modii(mulii(x, (GEN)Trq[1]), p);
  l = lgef(x)-1; if (l == 1) return gzero;
  x++; s = mulii((GEN)x[1], (GEN)Trq[1]);
  for (i=2; i<l; i++)
    s = addii(s, mulii((GEN)x[i], (GEN)Trq[i]));
  return modii(s, p);
}

/* assume x in Fq[X], return Tr_{Fq[X]/Fp[X]}(x), varn(X) = 0 */
static GEN 
poltrace(GEN x, GEN Trq, GEN p)
{
  long i,l;
  GEN y;
  if (typ(x) == t_INT || varn(x) != 0) return trace(x, Trq, p);
  l = lgef(x); y = cgetg(l,t_POL); y[1]=x[1];
  for (i=2; i<l; i++) y[i] = (long)trace((GEN)x[i],Trq,p);
  return y;
}

/* Find h in Fp[X] such that h(a[i]) = listdelta[i] for all modular factors
 * ff[i], where a[i] is a fixed root of ff[i] in Fq = Z[Y]/(p,T) [namely the
 * first one in Fp_factor_irred output]. Let f = ff[i], A the given root, then
 * h mod f is Tr_Fq/Fp ( h(A) f(X)/(X-A)f'(A) ), most of the expression being
 * precomputed. The complete h is recovered via chinese remaindering */
static GEN
chinese_retrieve_pol(GEN DATA, GEN listdelta)
{
  GEN interp,Trk,bezoutC,T,p, S,p1;
  long i,l;
  p = (GEN)DATA[2];
  T = (GEN)DATA[4];
  interp = (GEN)DATA[10];
  Trk = (GEN)DATA[11];
  bezoutC = (GEN)DATA[12];
  
  S = NULL; l = lg(interp);
  for (i=1; i<l; i++)
  { /* h(firstroot[i]) = listdelta[i] */
    p1 = FpXQX_FpXQ_mul((GEN)interp[i], (GEN)listdelta[i], T,p);
    p1 = poltrace(p1, (GEN)Trk[i], p);
    p1 = gmul(p1, (GEN)bezoutC[i]);
    S = S? gadd(S,p1): p1;
  }
  return FpX_res(FpX_red(S, p), FpX_red((GEN)DATA[1],p), p);
}

/* return P(X + c) using destructive Horner */
static GEN
TR_pol(GEN P, GEN c)
{
  GEN Q = dummycopy(P), *R;
  long i,k,n;
  
  if (!signe(P)) return Q;
  R = (GEN*)(Q+2); n = degpol(P);
  if (gcmp1(c))
  {
    for (i=1; i<=n; i++)
      for (k=n-i; k<n; k++)
        R[k] = gadd(R[k], R[k+1]);
  }
  else if (gcmp_1(c))
  {
    for (i=1; i<=n; i++)
      for (k=n-i; k<n; k++)
        R[k] = gsub(R[k], R[k+1]);
  }
  else
  {
    for (i=1; i<=n; i++)
      for (k=n-i; k<n; k++)
        R[k] = gadd(R[k], gmul(c, R[k+1]));
  }
  return Q;
}

/* g in Z[X] potentially defines a subfield of Q[X]/f. It is a subfield iff A
 * (cf cand_for_subfields) was a block system; then there
 * exists h in Q[X] such that f | g o h. listdelta determines h s.t f | g o h
 * in Fp[X] (cf chinese_retrieve_pol). We try to lift it. */
static GEN
embedding_of_potential_subfields(GEN g,GEN DATA,GEN listdelta)
{
  GEN TR,w0_Q,w0,w1_Q,w1,wpow,h0,gp,T,q2,q,p,ind,maxp,a;
  long rt;
  gpmem_t av;

  T = (GEN)DATA[1]; rt = brent_kung_optpow(degpol(T), 2);
  p = (GEN)DATA[2];
  maxp = (GEN)DATA[7];
  ind = (GEN)DATA[9];
  gp = derivpol(g); av = avma;
  w0 = chinese_retrieve_pol(DATA,listdelta);
  w0_Q = centermod(gmul(w0,ind), p);
  h0 = FpXQ_inv(FpX_FpXQ_compo(gp,w0, T,p), T,p); /* = 1/g'(w0) mod (T,p) */
  wpow = NULL; q = sqri(p);
  for(;;)
  {/* Given g,w0,h0 in Z[x], s.t. h0.g'(w0) = 1 and g(w0) = 0 mod (T,p), find
    * [w1,h1] satisfying the same conditions mod p^2, [w1,h1] = [w0,h0] (mod p)
    * (cf. Dixon: J. Austral. Math. Soc., Series A, vol.49, 1990, p.445) */
    if (DEBUGLEVEL>1) fprintferr("lifting embedding mod p = %Z\n",q);

    /* w1 := w0 - h0 g(w0) mod (T,q) */
    if (wpow)
      a = FpX_FpXQV_compo(g,wpow, T,q);
    else
      a = FpX_FpXQ_compo(g,w0, T,q); /* first time */
    /* now, a = 0 (p) */
    a = gmul(gneg(h0), gdivexact(a, p));
    w1 = gadd(w0, gmul(p, FpX_res(a, T,p)));

    w1_Q = centermod(gmul(w1, resii(ind,q)), q);
    if (gegal(w1_Q, w0_Q) || cmpii(q,maxp) > 0)
    {
      GEN G = gcmp1(ind)? g: rescale_pol(g,ind);
      if (gcmp0(poleval(G, gmodulcp(w1_Q,T)))) break;
    }
    if (cmpii(q, maxp) > 0)
    {
      if (DEBUGLEVEL) fprintferr("coeff too big for embedding\n");
      return NULL;
    }
    {
      GEN *gptr[5]; gptr[0]=&w1; gptr[1]=&h0; gptr[2]=&w1_Q;
      gptr[3]=&q; gptr[4]=&p;
      gerepilemany(av,gptr,5);
    }

    q2 = sqri(q);
    wpow = FpXQ_powers(w1, rt, T, q2);
    /* h0 := h0 * (2 - h0 g'(w1)) mod (T,q)
     *     = h0 + h0 * (1 - h0 g'(w1)) */
    a = gmul(gneg(h0), FpX_FpXQV_compo(gp, FpXV_red(wpow,q),T,q));
    a = ZX_s_add(FpX_res(a, T,q), 1); /* 1 - h0 g'(w1) = 0 (p) */
    a = gmul(h0, gdivexact(a, p));
    h0 = gadd(h0, gmul(p, FpX_res(a, T,p)));
    w0 = w1; w0_Q = w1_Q; p = q; q = q2;
  }
  TR = (GEN)DATA[14];
  if (!gcmp0(TR)) w1_Q = TR_pol(w1_Q, TR);
  return gdiv(w1_Q,ind);
}

static GEN
choose_prime(GEN pol,GEN dpol,long d,GEN *ptff,GEN *ptlistpotbl, long *ptlcm)
{
  gpmem_t av;
  byteptr di=diffptr;
  long j,k,oldllist,llist,r,lcm,oldlcm,pp,minp, N = degpol(pol), m = N/d;
  GEN p,listpotbl,oldlistpotbl,ff,oldff,n,oldn;
 
  minp = N*(m-1)/2;
  if (DEBUGLEVEL) timer2();
  di++; p = stoi(2);
  while (p[2]<=minp) p[2] += *di++;
  oldllist = 100000;
  oldlcm = 0;
  oldlistpotbl = oldff = oldn = NULL; pp = 0; /* gcc -Wall */
  av = avma;
  for(k=1; k<11 || !oldn; k++,p[2]+= *di++,avma = av)
  {
    while (!smodis(dpol,p[2])) p[2] += *di++;
    if (k > 50) err(talker,"sorry, too many block systems in nfsubfields");
    ff=(GEN)factmod0(pol,p)[1]; r=lg(ff)-1;
    if (r == 1 || r == N) continue;

    n = cgetg(r+1, t_VECSMALL);
    lcm = n[1] = degpol(ff[1]);
    for (j=2; j<=r; j++) { n[j] = degpol(ff[j]); lcm = clcm(lcm,n[j]); }
    if (lcm < oldlcm) continue; /* false when oldlcm = 0 */
    if (r >= BIL) { err(warner,"subfields: overflow in calc_block"); continue; }
    if (DEBUGLEVEL) fprintferr("p = %ld,\tlcm = %ld,\torbits: %Z\n",p[2],lcm,n);
    if (oldn && gegal(n,oldn)) continue;

    listpotbl = potential_block_systems(N,d,n, oldllist);
    if (!listpotbl) { oldlistpotbl = NULL; pp = p[2]; break; }
    llist = lg(listpotbl)-1;
    if (llist >= oldllist)
    {
      if (DEBUGLEVEL) msgtimer("#pbs >= %ld [aborted]",oldllist);
      for (j=1; j<llist; j++) free((void*)listpotbl[j]);
      free((void*)(listpotbl-1)); continue;
    }
    oldllist = llist; oldlistpotbl = listpotbl;
    pp = p[2]; oldff = ff; oldlcm = lcm; oldn = n;
    if (DEBUGLEVEL) msgtimer("#pbs = %ld",llist);
    av = avma;
  }
  if (DEBUGLEVEL)
  {
    fprintferr("Chosen prime: p = %ld\n",pp);
    if (DEBUGLEVEL>2)
      fprintferr("Potential block systems of size %ld: %Z\n", d,oldlistpotbl);
    flusherr();
  }
  *ptlistpotbl=oldlistpotbl; *ptff=oldff; *ptlcm=oldlcm; return stoi(pp);
}

static GEN
bound_for_coeff(long m,GEN rr, GEN *maxroot)
{
  long i,r1, lrr=lg(rr);
  GEN p1,b1,b2,B,M, C = matpascal(m-1);

  for (r1=1; r1 < lrr; r1++)
    if (typ(rr[r1]) != t_REAL) break;
  r1--;

  rr = gabs(rr,0); *maxroot = vecmax(rr);
  for (i=1; i<lrr; i++)
    if (gcmp((GEN)rr[i], gun) < 0) rr[i] = un;
  for (b1=gun,i=1; i<=r1; i++) b1 = gmul(b1, (GEN)rr[i]);
  for (b2=gun    ; i<lrr; i++) b2 = gmul(b2, (GEN)rr[i]);
  B = gmul(b1, gsqr(b2)); /* Mahler measure */
  M = cgetg(m+2, t_VEC); M[1]=M[2]=zero; /* unused */
  for (i=1; i<m; i++)
  {
    p1 = gadd(gmul(gcoeff(C, m, i+1), B),/* binom(m-1, i)   */
              gcoeff(C, m, i));          /* binom(m-1, i-1) */
    M[i+2] = (long)ceil_safe(p1);
  }
  return M;
}

static GEN
init_traces(GEN ff, GEN T, GEN p)
{
  long N = degpol(T),i,j,k, r = lg(ff);
  GEN Frob = matrixpow(N,N, FpXQ_pow(polx[varn(T)],p, T,p), T,p);
  GEN y,p1,p2,Trk,pow,pow1;

  k = degpol(ff[r-1]); /* largest degree in modular factorization */
  pow = cgetg(k+1, t_VEC);
  pow[1] = (long)zero; /* dummy */
  pow[2] = (long)Frob;
  pow1= cgetg(k+1, t_VEC); /* 1st line */
  for (i=3; i<=k; i++)
    pow[i] = (long)FpM_mul((GEN)pow[i-1], Frob, p);
  pow1[1] = (long)zero; /* dummy */
  for (i=2; i<=k; i++)
  {
    p1 = cgetg(N+1, t_VEC);
    pow1[i] = (long)p1; p2 = (GEN)pow[i];
    for (j=1; j<=N; j++) p1[j] = coeff(p2,1,j);
  }
  p1 = cgetg(N+1,t_VEC); p1[1] = un;
  for (i=2; i<=N; i++) p1[i] = zero;
  /* Trk[i] = line 1 of x -> x + x^p + ... + x^{p^(i-1)} */
  Trk = pow; /* re-use (destroy) pow */
  Trk[1] = (long)p1;
  for (i=2; i<=k; i++)
    Trk[i] = ladd((GEN)Trk[i-1], (GEN)pow1[i]);
  y = cgetg(r, t_VEC);
  for (i=1; i<r; i++) y[i] = Trk[degpol(ff[i])];
  return y;
}

/* return C in Z[X]/(p,T), C[ D[1] ] = 1, C[ D[i] ] = 0 otherwise. H is the
 * list of degree 1 polynomials X - D[i]  (come directly from factorization) */
static GEN
interpol(GEN H, GEN T, GEN p)
{
  long i, m = lg(H);
  GEN X = polx[0],d,p1,p2,a;

  p1=polun[0]; p2=gun; a = gneg(constant_term(H[1])); /* = D[1] */
  for (i=2; i<m; i++)
  {
    d = constant_term(H[i]); /* -D[i] */
    p1 = FpXQX_mul(p1,gadd(X,d), T,p);
    p2 = FpXQ_mul(p2, gadd(a,d), T,p);
  }
  p2 = FpXQ_inv(p2, T,p);
  return FpXQX_FpXQ_mul(p1,p2, T,p);
}

static GEN
roots_from_deg1(GEN x)
{
  long i,l = lg(x);
  GEN r = cgetg(l,t_VEC);
  for (i=1; i<l; i++) r[i] = lneg(constant_term(x[i]));
  return r;
}

struct poldata
{
  GEN pol;
  GEN dis; /* |disc(pol)| */
  GEN roo; /* roots(pol) */
  GEN den; /* multiple of index(pol) */
};

/* ff = factmod(nf[1], p), d = requested degree for subfield. Return DATA,
 * valid for given nf, p and d 
 * 1: polynomial nf[1],
 * 2: prime p,
 * 3: exponent e (for Hensel lifts) such that p^e > max(M),
 * 4: polynomial defining the field F_(p^nn),
 * 5: Hensel lift to precision p^e  of DATA[6]
 * 6: roots of nf[1] in F_(p^nn),
 * 7: Hadamard bound for coefficients of h(x) such that g o h = 0 mod nf[1].
 * 8: bound M for polynomials defining subfields x DATA[9]
 * 9: multiple of index of nf
 *10: *[i] = interpolation polynomial for ff[i] [= 1 on the first root
      firstroot[i], 0 on the others]
 *11: Trk used to compute traces (cf poltrace)
 *12: Bezout coefficients associated to the ff[i]
 *13: *[i] = index of first root of ff[i] (in DATA[6])
 *14: number of polynomial changes (translations) */
static GEN
compute_data(GEN DATA, struct poldata PD, long d, GEN ff, GEN T,GEN p)
{
  long i,j,l,e,N, lff = lg(ff);
  GEN ffL,den,roo,pe,p1,p2,fk,fhk,MM,maxroot,pol,interp,bezoutC;    

  if (DEBUGLEVEL>1) { fprintferr("Entering compute_data()\n\n"); flusherr(); }
  pol = PD.pol; N = degpol(pol);
  roo = PD.roo;
  den = PD.den;
  if (DATA) /* update (translate) an existing DATA */
  {
    GEN Xm1 = gsub(polx[varn(pol)], gun);
    GEN TR = addis((GEN)DATA[14],1);
    GEN mTR = negi(TR), mun = negi(gun);
    DATA[14] = (long)TR;
    pol = TR_pol(pol, mTR);
    p1 = dummycopy(roo); l = lg(p1);
    for (i=1; i<l; i++) p1[i] = ladd(TR, (GEN)p1[i]);
    roo = p1;

    fk = (GEN)DATA[6]; l=lg(fk);
    for (i=1; i<l; i++) fk[i] = lsub(Xm1, (GEN)fk[i]);

    interp = (GEN)DATA[10];
    bezoutC = (GEN)DATA[12]; l = lg(interp);
    for (i=1; i<l; i++)
    {
      if (degpol(interp[i]) > 0) /* do not turn polun[0] into gun */
      {
        p1 = TR_pol((GEN)interp[i], mun);
        interp[i] = (long)FpXQX_red(p1, NULL,p);
      }
      if (degpol(bezoutC[i]) > 0)
      {
        p1 = TR_pol((GEN)bezoutC[i], mun);
        bezoutC[i] = (long)FpXQX_red(p1, NULL,p);
      }
    }
    p1 = cgetg(lff, t_VEC);
    for (i=1; i<lff; i++)
      p1[i] = (long)FpX_red(TR_pol((GEN)ff[i], mTR), p);
    ff = p1;
  }
  else
  {
    GEN firstroot = cgetg(lff, t_VECSMALL);
    DATA = cgetg(15,t_VEC);
    DATA[2] = (long)p;
    DATA[4] = (long)T;
    interp = cgetg(lff, t_VEC);
    fk = cgetg(N+1,t_VEC);
    for (l=1,j=1; j<lff; j++)
    { /* compute roots and fix ordering (Frobenius cycles) */
      p1 = Fp_factor_irred((GEN)ff[j], p,T);
      interp[j] = (long)interpol(p1,T,p);
      firstroot[j] = l;
      for (i=1; i<lg(p1); i++,l++) fk[l] = p1[i];
    }
    DATA[9] = (long)PD.den;
    DATA[10]= (long)interp;
    DATA[11]= (long)init_traces(ff, T,p);
    DATA[12]= (long)get_bezout(pol,ff,p);
    DATA[13]= (long)firstroot;
    DATA[14]= zero;
  }
  DATA[1] = (long)pol;
  MM = bound_for_coeff(d, roo, &maxroot);
  MM = gmul2n(MM,1);
  DATA[8] = (long)MM;
  e = logint(shifti(vecmax(MM),20), p, &pe); /* overlift 2^20 [for d-1 test] */
  DATA[3] = (long)pe;
  DATA[6] = (long)roots_from_deg1(fk);

#if 0
  fhk = hensel_lift_fact(pol,fk,(GEN)DATA[4],p,pe,e);
#else
  /* first lift in Zp to precision p^e */
  ffL = hensel_lift_fact(pol,ff, NULL,p,pe,e);
  fhk = NULL;
  for (l=i=1; i<lff; i++)
  { /* lift factorization of ff[i] in Qp[X] / T */
    GEN L = (GEN)ffL[i];
    long di = degpol(L);
    p2 = cgetg(di+1, t_VEC);
    for (j=1; j<=di; j++) p2[j] = fk[l++];
    p1 = hensel_lift_fact(L,p2,T,p,pe,e);
    fhk = fhk? concatsp(fhk, p1): p1;
  }
#endif
  DATA[5] = (long)roots_from_deg1(fhk);

  p1 = gmul(stoi(N), gsqrt(gpuigs(stoi(N-1),N-1),DEFAULTPREC));
  p2 = gpuigs(maxroot, N/d + N*(N-1)/2);
  p1 = gdiv(gmul(p1,p2), gsqrt(PD.dis,DEFAULTPREC));
  p1 = shifti(ceil_safe(p1), 1);
  DATA[7] = lmulii(p1, PD.den);

  if (DEBUGLEVEL>1) {
    fprintferr("f = %Z\n",DATA[1]);
    fprintferr("p = %Z, lift to p^%ld\n",DATA[2], e);
    fprintferr("Fq defined by %Z\n",DATA[4]);
    fprintferr("2 * Hadamard bound * ind = %Z\n",DATA[7]);
    fprintferr("2 * M = %Z\n",DATA[8]);
  }
  return DATA;
}

/* g = polynomial, h = embedding. Return [[g,h]] */
static GEN
_subfield(GEN g, GEN h)
{
  GEN x = cgetg(3,t_VEC);
  x[1] = (long)g;
  x[2] = (long)h; return _vec(x);
}

/* subfields of degree d */
static GEN
subfields_of_given_degree(struct poldata PD,long d)
{
  gpmem_t av, av2;
  long llist,i,nn,v;
  GEN listpotbl,ff,A,CSF,ESF,LSB,p,T,DATA,listdelta;
  GEN pol = PD.pol, dpol = PD.dis;

  if (DEBUGLEVEL) fprintferr("\n*** Look for subfields of degree %ld\n\n", d);
  av = avma;
  p = choose_prime(pol,dpol,degpol(pol)/d,&ff,&listpotbl,&nn);
  if (!listpotbl) { avma=av; return cgetg(1,t_VEC); }
  v = fetch_var(); name_var(v,"y");
  T = lift_intern(ffinit(p,nn, v));
  DATA = NULL; LSB = cgetg(1,t_VEC); 
  i = 1; llist = lg(listpotbl);
CHANGE: 
  DATA = compute_data(DATA,PD,d, ff,T,p);
  for (; i<llist; i++)
  {
    av2 = avma; A = (GEN)listpotbl[i];
    if (DEBUGLEVEL > 1) fprintferr("\n* Potential block # %ld: %Z\n",i,A);
    CSF = cand_for_subfields(A,DATA,&listdelta);
    if (typ(CSF)==t_INT)
    {
      avma = av2;
      if (DEBUGLEVEL > 1) switch(itos(CSF))
      {
        case 0: fprintferr("changing f(x): p divides disc(g(x))\n"); break;
        case 1: fprintferr("coeff too big for pol g(x)\n"); break;
        case 2: fprintferr("d-1 test failed\n"); break;
      }
      if (CSF==gzero) goto CHANGE;
    }
    else
    {
      if (DEBUGLEVEL) fprintferr("candidate = %Z\n",CSF);
      ESF = embedding_of_potential_subfields(CSF,DATA,listdelta);
      if (!ESF) { avma = av2; continue; }

      if (DEBUGLEVEL) fprintferr("embedding = %Z\n",ESF);
      LSB = gerepileupto(av2, concat(LSB, _subfield(CSF,ESF)));
    }
  }
  delete_var();
  for (i=1; i<llist; i++) free((void*)listpotbl[i]);
  free((void*)(listpotbl-1));
  if (DEBUGLEVEL) fprintferr("\nSubfields of degree %ld: %Z\n",d, LSB);
  return gerepilecopy(av, LSB);
}

static GEN
fix_var(GEN x, long v)
{
  long i, l = lg(x);
  x = gcopy(x); if (!v) return x;
  for (i=1; i<l; i++) { GEN t = (GEN)x[i]; setvarn(t[1],v); setvarn(t[2],v); }
  return x;
}

extern GEN vandermondeinverseprep(GEN T, GEN L);
extern GEN ZX_disc_all(GEN x, ulong bound);
extern GEN indexpartial(GEN P, GEN DP);
extern GEN initgaloisborne(GEN T, GEN dn, GEN *ptL, GEN *ptprep, GEN *ptdis, long *ptprec);

void
subfields_poldata(GEN T, struct poldata *PD)
{
  GEN  nf,L,dis;

  T = get_nfpol(T, &nf);
  PD->pol = dummycopy(T); /* may change variable number later */
  if (nf)
  {
    PD->den = (GEN)nf[4];
    PD->roo = (GEN)nf[6];
    PD->dis = mulii(absi((GEN)nf[3]), sqri((GEN)nf[4]));
  }
  else
  {
    PD->den = initgaloisborne(T,NULL, &L,NULL,&dis,NULL);
    PD->roo = L;
    PD->dis = absi(dis);
  }
}

GEN
subfields(GEN nf,GEN d)
{
  gpmem_t av = avma;
  long di,N,v0;
  GEN LSB,pol;
  struct poldata PD;

  pol = get_nfpol(nf, &nf); /* in order to treat trivial cases */
  v0=varn(pol); N=degpol(pol); di=itos(d);
  if (di==N) return gerepilecopy(av, _subfield(pol, polx[v0]));
  if (di==1) return gerepilecopy(av, _subfield(polx[v0], pol));
  if (di < 1 || di > N || N % di) return cgetg(1,t_VEC);

  subfields_poldata(nf? nf:pol, &PD);
  pol = PD.pol;
  setvarn(pol, 0);
  LSB = subfields_of_given_degree(PD, di);
  return gerepileupto(av, fix_var(LSB,v0));
}

static GEN
subfieldsall(GEN nf)
{
  gpmem_t av = avma;
  long N,ld,i,v0;
  GEN pol,dg,LSB,NLSB;
  struct poldata PD;

  subfields_poldata(nf, &PD);
  pol = PD.pol;

  v0 = varn(pol); N = degpol(pol);
  dg = divisors(stoi(N)); ld = lg(dg)-1;
  if (DEBUGLEVEL) fprintferr("\n***** Entering subfields\n\npol = %Z\n",pol);

  LSB = _subfield(pol,polx[0]);
  if (ld > 2)
  {
    setvarn(pol, 0);
    for (i=2; i<ld; i++)
    {
      gpmem_t av1 = avma;
      NLSB = subfields_of_given_degree(PD, N / itos((GEN)dg[i]));
      if (lg(NLSB) > 1) LSB = concatsp(LSB,NLSB); else avma = av1;
    }
  }
  LSB = concatsp(LSB, _subfield(polx[0],pol));
  if (DEBUGLEVEL) fprintferr("\n***** Leaving subfields\n\n");
  return gerepileupto(av, fix_var(LSB,v0));
}

GEN
subfields0(GEN nf,GEN d)
{
  return d? subfields(nf,d): subfieldsall(nf);
}

