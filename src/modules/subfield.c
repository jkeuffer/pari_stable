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

#define deg(a) (lgef(a)-3)
static long TR; /* nombre de changements de polynomes (degre fixe) */
static GEN FACTORDL; /* factorisation of |disc(L)| */

static GEN print_block_system(long N,GEN Y,long d, GEN vbs);

/* Computation of potential block systems of given size d associated to a
 * rational prime p: give a row vector of row vectors containing the
 * potential block systems of imprimitivity; a potential block system is a
 * vector of row vectors (enumeration of the roots).
 */
#define BIL 32 /* for 64bit machines also */
static GEN
calc_block(long N,GEN Z,long d,GEN Y,GEN vbs,ulong maxl)
{
  long r,lK,i,j,k,t,tp,T,lpn,u,nn,lnon,lY;
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
    lpn=0; k = itos((GEN)K[i]);
    for (j=2; j<r; j++)
      if (n[j]%k == 0)
      {
        if (++lpn >= BIL) err(talker,"overflow in calc_block");
        pn[lpn]=n[j]; pnon[lpn]=j;
      }
    if (!lpn)
    {
      if (d*k != n[1]) continue;
      T=1; lpn=1;
    }
    else
      T = 1<<lpn;
    for (t=0; t<T; t++)
    {
      for (nn=n[1],tp=t, u=1; u<=lpn; u++,tp>>=1)
      {
        if (tp&1) { nn += pn[u]; e[u]=1; } else e[u]=0;
      }
      if (d*k == nn)
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
	  vbs = print_block_system(N,Yp,d,vbs);
	else
	{
	  for (u=1,j=2; j<r; j++)
	    if (!non[j]) Zpp[u++] = Z[j];
          setlg(Zpp, u);
	  vbs = calc_block(N,Zpp,d,Yp,vbs,maxl);
          if (lg(vbs) > maxl) return vbs;
	}
        avma=av;
      }
    }
  }
  return vbs;
}

static GEN
potential_block_systems(long N, long d, GEN n, ulong maxl)
{
  long av=avma,r,i,j,k;
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
perm_mul(GEN perm1,GEN perm2)
{
  long av = avma,i, N = lg(perm1);
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
    long av = avma;
    GEN p1 = new_chunk(N);
    b = cy[1];
    for (i=1; i<lcy; i++) b = (perm[b] = cy[i+1]);
    perm[b] = cy[1];
    for (i=1; i<N; i++) p1[i] = perm[i];

    for (j=2; j<=lp; j++) perm_mul(perm,p1);
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

/* renvoie 0 si l'un des coefficients de g[i] est de module > M[i]; 1 sinon */
static long
ok_coeffs(GEN g,GEN M)
{
  long i, lg = lgef(g)-1; /* g is monic, and cst term is ok */
  for (i=3; i<lg; i++)
    if (absi_cmp((GEN)g[i], (GEN)M[i]) > 0) return 0;
  return 1;
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
    vbs = (GEN)gprealloc((void*)(vbs-1), (2 + (maxl<<1))*sizeof(GEN),
                                         (2 + maxl)*sizeof(GEN));
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
print_block_system(long N,GEN Y,long d, GEN vbs)
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
      cy = (GEN)Yi[j]; a = (GEN)cy[1];
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
    long av = avma;
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
	perm_mul(perm, cycle_power_to_perm(cyperm,gmael(Z,u,v),e[u][v]));
    vbs = append_vbs(vbs, im_block_by_perm(D,perm));
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

/* Return common factors to A and B + s the prime to A part of B */
static GEN
commonfactor(GEN A, GEN B)
{
  GEN f,p1,p2,s, y = cgetg(3,t_MAT);
  long lf,i;

  s = absi(B); f=(GEN)A[1]; lf=lg(f);
  p1=cgetg(lf+1,t_COL); y[1]=(long)p1;
  p2=cgetg(lf+1,t_COL); y[2]=(long)p2;
  for (i=1; i<lf; i++)
  {
    p1[i] = f[i];
    p2[i] = lstoi(pvaluation(s,(GEN)f[i], &s));
  }
  p1[i] = (long)s;
  p2[i] = un; return y;
}

static GEN
polsimplify(GEN x)
{
  long i,lx = lgef(x);
  for (i=2; i<lx; i++)
    if (typ(x[i]) == t_POL) x[i] = signe(x[i])? mael(x,i,2): zero;
  return x;
}

/* Return a polynomial g defining a potential subfield, or
 * 0: if p | d(g)
 * 1: if coeffs of g are too large
 * 4: prime to d(L) part of d(g) not a square
 * 5: !4 but a prime divisor of (d(g), d(L)) has odd exponent in d(g), and
 *    exponent lower than d in d(L) */
static GEN
cand_for_subfields(GEN A,GEN DATA,GEN *ptlistdelta)
{
  long N,m,i,j,d,lf;
  GEN T,pe,p,pol,fk,fhk,g,dg,factcommon,ff1,ff2,p1;
  GEN delta,listdelta,whichdelta,firstroot;

  pol=(GEN)DATA[1];
  p = (GEN)DATA[2];
  pe= (GEN)DATA[3];
  T = (GEN)DATA[4];
  fhk=(GEN)DATA[5];
  fk= (GEN)DATA[6]; N=deg(pol); m=lg(A)-1; d=N/m;
  firstroot = (GEN)DATA[13];
  if (N % m) err(talker,"incompatible block system in cand_for_subfields");

  delta = cgetg(m+1,t_VEC);
  lf = lg(firstroot);
  listdelta = cgetg(lf, t_VEC);
  whichdelta = cgetg(N+1, t_VECSMALL);
  for (i=1; i<=m; i++)
  {
    GEN Ai=(GEN)A[i], col = cgetg(d+1,t_VEC);

    p1 = gun;
    for (j=1; j<=d; j++)
    {
      col[j] = fk[Ai[j]];
      p1 = FpXQ_mul(p1, (GEN)fhk[Ai[j]], T,pe);
    }
    /* g = prod (X - delta[i])
     * if g o h = 0 (pol), we'll have h(Ai[j]) = delta[i] for all j */
    if (DEBUGLEVEL>2) fprintferr("delta[%ld] = %Z\n",i,p1);
    /* fk[k] belongs to whichdelta[k] */
    for (j=1; j<=d; j++) whichdelta[Ai[j]] = i;
    delta[i] = (long)p1;
  }
  for (i=1; i<lf; i++) listdelta[i] = delta[whichdelta[firstroot[i]]];
  g = FqV_roots_to_pol(delta, T, pe, 0);
  g = centermod(polsimplify(g), pe); /* assume g in Z[X] */
  if (DEBUGLEVEL>2) fprintferr("pol. found = %Z\n",g);
  if (!FpX_is_squarefree(g, p)) return gzero;
  if (!ok_coeffs(g,(GEN)DATA[8])) return gun;

  dg = ZX_disc(g);
  factcommon = commonfactor(FACTORDL,dg);
  ff1=(GEN)factcommon[1]; lf=lg(ff1)-1;
  if (!carreparfait((GEN)ff1[lf])) return stoi(4);
  ff2=(GEN)factcommon[2];
  for (i=1; i<lf; i++)
    if (mod2((GEN)ff2[i]) && itos(gmael(FACTORDL,2,i)) < d) return stoi(5);

  *ptlistdelta = listdelta; return g;
}

/* Given h in Z[X], return a rational polynomial = h mod p^k with denominator
 * dividing ind. */
static GEN
retrieve_ratpol(GEN ind, GEN h, GEN pk)
{
  return gdiv(centermod(gmul(h,ind), pk), ind);
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
    if (deg(d) > 0) err(talker, "relatively prime polynomials expected");
    d = (GEN)d[2];
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

/* g in Z[X] potentially defines a subfield of Q[X]/f. It is a subfield iff A
 * (cf cand_for_subfields) was a block system; then there
 * exists h in Q[X] such that f | g o h. listdelta determines h s.t f | g o h
 * in Fp[X] (cf chinese_retrieve_pol). We try to lift it. */
static GEN
embedding_of_potential_subfields(GEN g,GEN DATA,GEN listdelta)
{
  GEN w0_Q,w0,w1,h0,gp,w1_Q,T,p,ind,maxp,p1;
  ulong av;

  T = (GEN)DATA[1];
  p = (GEN)DATA[2];
  maxp = (GEN)DATA[7];
  ind = (GEN)DATA[9];
  gp = derivpol(g); av = avma;
  w0 = chinese_retrieve_pol(DATA,listdelta);
  w0_Q = retrieve_ratpol(ind,w0,p);
  h0 = FpXQ_inv(FpX_FpXQ_compo(gp,w0, T,p), T,p); /* = 1/g'(w0) mod (T,p) */
  for(;;)
  {/* Given g,w0,h0 in Z[x], s.t. h0.g'(w0) = 1 and g(w0) = 0 mod (T,p), find
    * [w1,h1] satisfying the same conditions mod p^2, [w1,h1] = [w0,h0] (mod p)
    * (cf. Dixon: J. Austral. Math. Soc., Series A, vol.49, 1990, p.445) */
    if (DEBUGLEVEL>2) fprintferr("w = %Z\nh = %Z\n",w0,h0);
    p = sqri(p);
    /* w1 = w0 - h0 g(w0) mod (T,p) */
    p1 = gmul(gneg(h0), FpX_FpXQ_compo(g,w0, T,p));
    w1 = gadd(w0, FpX_res(p1, T,p));
    w1_Q = retrieve_ratpol(ind,w1,p);
    if ((gegal(w1_Q, w0_Q) || cmpii(p,maxp) > 0) &&
      gcmp0(poleval(g, gmodulcp(w1_Q,T)))) break;
    if (DEBUGLEVEL>2)
    {
      fprintferr("Old Q-polynomial: %Z\n",w0_Q);
      fprintferr("New Q-polynomial: %Z\n",w1_Q);
    }
    if (cmpii(p, maxp) > 0)
    {
      if (DEBUGLEVEL) fprintferr("coeff too big for embedding\n");
      return NULL;
    }

    p1 = gmul(gneg(h0), FpX_FpXQ_compo(gp,w1, T,p));
    p1 = gadd(gdeux, FpX_res(p1, T,p));
    h0 = FpX_res(gmul(h0, p1), T,p);
    w0 = w1; w0_Q = w1_Q;
    {
      GEN *gptr[4]; gptr[0]=&w0; gptr[1]=&h0; gptr[2]=&w0_Q; gptr[3]=&p;
      gerepilemany(av,gptr,4);
    }
  }
  return poleval(w1_Q, gadd(polx[0],stoi(TR)));
}

static GEN
choose_prime(GEN pol,GEN dpol,long d,GEN *ptff,GEN *ptlistpotbl, long *ptnn)
{
  long j,k,oldllist,llist,r,nn,oldnn,*n,N,pp;
  GEN p,listpotbl,oldlistpotbl,ff,oldff;
  byteptr di=diffptr;

  if (DEBUGLEVEL) timer2();
  di++; p = stoi(2); N = deg(pol);
  while (p[2]<=N) p[2] += *di++;
  oldllist = oldnn = BIGINT;
  oldlistpotbl = oldff = NULL; pp = 0; /* gcc -Wall */
  for(k=1; k<11 || oldnn == BIGINT; k++,p[2]+= *di++)
  {
    ulong av = avma, maxl;
    while (!smodis(dpol,p[2])) p[2] += *di++;
    ff=(GEN)factmod(pol,p)[1]; r=lg(ff)-1;
    if (r == 1 || r == N) { avma = av; continue; }

    n = cgetg(r+1, t_VECSMALL);
    nn = n[1] = deg(ff[1]);
    for (j=2; j<=r; j++) { n[j] = deg(ff[j]); nn = clcm(nn,n[j]); }
    maxl = (oldnn == BIGINT)? 1000000: oldnn * oldllist;
    listpotbl = potential_block_systems(N,d,n, maxl);
    if (!listpotbl) { oldlistpotbl = NULL; pp = p[2]; break; }
    llist = lg(listpotbl)-1;
    if (DEBUGLEVEL)
    {
      if (llist >= maxl)
        fprintferr("p = %ld,\tr = %ld,\tnn = %ld,\t#pbs > %ld [aborted]\n",
                   p[2],r,nn,maxl);
      else
        fprintferr("Time: %ldms,\tp = %ld,\tr = %ld,\tnn = %ld,\t#pbs = %ld\n",
                   timer2(),p[2],r,nn,llist);
      flusherr();
    }
    if (llist < maxl && nn * llist < maxl)
    {
      oldllist = llist; oldlistpotbl = listpotbl;
      pp = p[2]; oldff = ff; oldnn = nn; continue;
    }
    for (j=1; j<llist; j++) free((void*)listpotbl[j]);
    free((void*)(listpotbl-1));
    avma = av;
  }
  if (DEBUGLEVEL)
  {
    fprintferr("Chosen prime: p = %ld\n",pp);
    if (DEBUGLEVEL>2)
      fprintferr("Potential block systems of size %ld: %Z\n", d,oldlistpotbl);
    flusherr();
  }
  if (oldff) oldff = lift_intern(oldff);
  *ptlistpotbl=oldlistpotbl; *ptff=oldff; *ptnn=oldnn; return stoi(pp);
}

static GEN
bound_for_coeff(long m,GEN rr,long r1, GEN *maxroot)
{
  long i, lrr=lg(rr);
  GEN p1,b1,b2,B,M, C = matpascal(m-1);

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
    M[i+2] = lceil(p1);
  }
  return M;
}

/* upper bound for floor(x) [avoid "precision loss in truncation"] */
static GEN
floor_bound(GEN x)
{
  long e;
  GEN y = grndtoi(x, &e);
  if (e>=0) y = addii(y, shifti(gun, e));
  return y;
}

static GEN
init_traces(GEN ff, GEN T, GEN p)
{
  long N = deg(T),i,j,k, r = lg(ff);
  GEN Frob = matrixpow(N,N, FpXQ_pow(polx[varn(T)],p, T,p), T,p);
  GEN y,p1,p2,Trk,pow,pow1;

  k = deg(ff[r-1]); /* largest degree in modular factorization */
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
  for (i=1; i<r; i++) y[i] = Trk[deg(ff[i])];
  return y;
}

/* return H in Z[X]/(p,T), H[ D[1] ] = 1, H[ D[i] ] = 0 otherwise. H is the
 * list of degree 1 polynomials X - D[i]  (come directly from factorization) */
static GEN
interpol(GEN H, GEN T, GEN p)
{
  long i, m = lg(H);
  GEN X = polx[0],d,p1,p2,a;

  p1=polun[0]; p2=gun; a = gneg(gmael(H,1,2)); /* = D[1] */
  for (i=2; i<m; i++)
  {
    d = gmael(H,i,2); /* -D[i] */
    p1 = FpXQX_mul(p1,gadd(X,d), T,p);
    p2 = FpXQ_mul(p2, gadd(a,d), T,p);
  }
  p2 = FpXQ_inv(p2, T,p);
  return FpXQX_FpXQ_mul(p1,p2, T,p);
}

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
 * 9: index of nf
 *10: *[i] = interpolation polynomial for ff[i] [= 1 on the first root
      firstroot[i], 0 on the others]
 *11: Trk used to compute traces (cf poltrace)
 *12: Bezout coefficients associated to the ff[i]
 *13: *[i] = index of first root of ff[i] (in DATA[6]) */
static GEN
compute_data(GEN DATA, long d, GEN nf, GEN ff, GEN T, GEN p)
{
  long i,j,l,e,N,pp;
  GEN pe,p1,p2,fk,fhk,MM,dpol,maxroot,maxMM,pol,ind,interp,bezoutC;

  if (DEBUGLEVEL>1) { fprintferr("Entering compute_data()\n\n"); flusherr(); }
  pol = (GEN)nf[1]; N = deg(pol);
  if (DATA) /* update (translate) an existing DATA */
  {
    GEN Xm1 = gsub(polx[varn(pol)], gun);
    TR++; pol = poleval(pol, Xm1);
    nf = dummycopy(nf); nf[1]=(long)pol;
    nf[6] = (long)dummycopy((GEN)nf[6]);
    p1 = (GEN)nf[6]; l = lg(p1);
    for (i=1; i<l; i++) p1[i] = ladd(gun,(GEN)p1[i]);
    /* don't update ff (useless), only fk, interp, and bezoutC */
    fk = (GEN)DATA[6]; l=lg(fk);
    interp = (GEN)DATA[10];
    bezoutC = (GEN)DATA[12];
    for (i=1; i<l; i++)
      fk[i] = lsub(Xm1, (GEN)fk[i]);
    l = lg(interp);
    for (i=1; i<l; i++)
    {
      if (deg(interp[i]) > 0) /* do not turn polun[0] into gun */
      {
        p1 = poleval((GEN)interp[i], Xm1);
        interp[i] = (long)FpXQX_red(p1, NULL,p);
      }
      if (deg(bezoutC[i]) > 0)
      {
        p1 = poleval((GEN)bezoutC[i], Xm1);
        bezoutC[i] = (long)FpXQX_red(p1, NULL,p);
      }
    }
  }
  else
  {
    GEN firstroot;    
    long r = lg(ff);
    DATA = cgetg(14,t_VEC);
    DATA[2] = (long)p;
    DATA[4] = (long)T;
    interp = cgetg(r, t_VEC);
    firstroot = cgetg(r, t_VECSMALL);
    fk = cgetg(N+1,t_VEC);
    for (l=1,j=1; j<r; j++)
    { /* compute roots and fix ordering (Frobenius cycles) */
      p1 = Fp_factor_irred((GEN)ff[j], p, (GEN)DATA[4]);
      interp[j] = (long)interpol(p1,T,p);
      firstroot[j] = l;
      for (i=1; i<lg(p1); i++,l++) fk[l] = p1[i];
    }
    DATA[10]= (long)interp;
    DATA[11]= (long)init_traces(ff, T,p);
    DATA[12]= (long)get_bezout(pol,ff,p);
    DATA[13]= (long)firstroot;
  }
  DATA[1] = (long)pol;
  MM = bound_for_coeff(d, (GEN)nf[6], nf_get_r1(nf), &maxroot);
  MM = gmul2n(MM,1);
  DATA[8] = (long)MM;
  pp = itos(p); maxMM = vecmax(MM);
  for (e=1,pe=p; cmpii(pe, maxMM) < 0; ) { pe = mulis(pe,pp); e++; }
  DATA[3] = (long)pe;
  p1 = cgetg(N+1,t_VEC);
  for (l=1; l<=N; l++) p1[l] = lneg(gmael(fk,l,2));
  DATA[6] = (long)p1;

  fhk = hensel_lift_fact(pol,fk,(GEN)DATA[4],p,pe,e);
  p1 = cgetg(N+1,t_VEC);
  for (l=1; l<=N; l++) p1[l] = lneg(gmael(fhk,l,2));
  DATA[5] = (long)p1;

  p1 = gmul(stoi(N), gsqrt(gpuigs(stoi(N-1),N-1),DEFAULTPREC));
  p2 = gpuigs(maxroot, N/d + N*(N-1)/2);
  ind = (GEN)nf[4];
  dpol = mulii(sqri(ind),(GEN)nf[3]);
  p1 = gdiv(gmul(p1,p2), gsqrt(absi(dpol),DEFAULTPREC));
  p1 = shifti(floor_bound(p1), 1);
  DATA[7] = lmulii(p1,ind);
  DATA[9] = (long)ind;

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

/* subfields of degree d. dpol = poldisc(nf[1]) */
static GEN
subfields_of_given_degree(GEN nf,GEN dpol,long d)
{
  ulong av,av2;
  long llist,i,nn;
  GEN listpotbl,ff,A,CSF,ESF,LSB,p,T,DATA,listdelta, pol = (GEN)nf[1];

  if (DEBUGLEVEL) fprintferr("\n*** Look for subfields of degree %ld\n\n", d);
  TR = 0; av = avma;
  p = choose_prime(pol,dpol,deg(pol)/d,&ff,&listpotbl,&nn);
  if (!listpotbl) { avma=av; return cgetg(1,t_VEC); }
  T = lift_intern(ffinit(p,nn, fetch_var()));
  DATA = NULL; LSB = cgetg(1,t_VEC); 
  i = 1; llist = lg(listpotbl);
CHANGE: 
  DATA = compute_data(DATA,d,nf,ff,T,p);
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
        case 4: fprintferr("prime to d(L) part of d(g) not a square\n"); break;
        case 5: fprintferr("exponent too small in factor( d(L) )\n"); break;
      }
      if (gcmp0(CSF)) goto CHANGE;
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
  return gerepileupto(av, gcopy(LSB));
}

static GEN
init_var(GEN nf, long v)
{
  if (!v) return nf;
  nf = dummycopy(nf);
  nf[1] = (long)dummycopy((GEN)nf[1]);
  setvarn(nf[1], 0); return nf;
}

static GEN
fix_var(GEN x, long v)
{
  long i, l = lg(x);
  x = gcopy(x); if (!v) return x;
  for (i=1; i<l; i++) { GEN t = (GEN)x[i]; setvarn(t[1],v); setvarn(t[2],v); }
  return x;
}

GEN
subfields(GEN nf,GEN d)
{
  ulong av = avma;
  long di,N,v0;
  GEN dpol,LSB,pol;

  nf = checknf(nf); pol = (GEN)nf[1];
  v0=varn(pol); N=deg(pol); di=itos(d);
  if (di==N) return _subfield(gcopy(pol), polx[v0]);
  if (di==1) return _subfield(polx[v0], gcopy(pol));
  if (di < 1 || di > N || N % di) return cgetg(1,t_VEC);

  nf = init_var(nf,v0);
  FACTORDL = factor(absi((GEN)nf[3]));
  dpol = mulii((GEN)nf[3],sqri((GEN)nf[4]));
  LSB = subfields_of_given_degree(nf,dpol,di);
  return gerepileupto(av, fix_var(LSB,v0));
}

static GEN
subfieldsall(GEN nf)
{
  ulong av = avma,
  long N,ld,i,v0;
  GEN pol,dpol,dg,LSB,NLSB;

  nf = checknf(nf); pol = (GEN)nf[1];
  v0 = varn(pol); N = deg(pol);
  dg = divisors(stoi(N)); ld = lg(dg)-1;
  if (DEBUGLEVEL) fprintferr("\n***** Entering subfields\n\npol = %Z\n",pol);

  LSB = _subfield(pol,polx[0]);
  if (ld > 2)
  {
    nf = init_var(nf,v0);
    FACTORDL = factor(absi((GEN)nf[3]));
    dpol = mulii(sqri((GEN)nf[4]),(GEN)nf[3]);
    for (i=2; i<ld; i++)
    {
      ulong av1 = avma;
      NLSB = subfields_of_given_degree(nf,dpol, N / itos((GEN)dg[i]));
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

/* irreducible (unitary) polynomial of degree n over Fp[v] */
GEN
ffinit(GEN p,long n,long v)
{
  long av = avma;
  GEN pol;

  if (n<=0) err(talker,"non positive degree in ffinit");
  if (typ(p) != t_INT) err(typeer,"ffinit");
  if (v<0) v = 0;
  for(;; avma = av)
  {
    pol = gadd(gpowgs(polx[v],n), FpX_rand(n-1,v, p));
    if (is_irred_mod_p(pol, p)) break;
  }
  return gerepileupto(av, FpX(pol,p));
}

/*******************************************************************/
/*                                                                 */
/*            AUTOMORPHISMS OF AN ABELIAN NUMBER FIELD             */
/*               V. Acciaro and J. Klueners (1996)                 */
/*                                                                 */
/*******************************************************************/

/* calcul du frobenius en p pour le corps abelien defini par le polynome pol,
 * par relevement de hensel du frobenius frobp de l'extension des corps
 * residuels (frobp est un polynome mod pol a coefficients dans F_p)
 */
static GEN
frobenius(GEN pol,GEN frobp,GEN p,GEN B,GEN d)
{
  long av=avma,v0,D,i,depas;
  GEN b0,b1,pold,polp,poldp,w0,w1,g0,g1,unmodp,polpp,v,pp,unmodpp,poldpp,bl0,bl1;

  v0=varn(pol); unmodp=gmodulsg(1,p); pold=deriv(pol,v0);
  b0=frobp; polp=gmul(unmodp,pol);
  poldp=gsubst(deriv(polp,v0),v0,frobp);
  w0=ginv(poldp);
  bl0=lift(b0); D=deg(bl0);
  v=cgetg(D+2,t_VEC);
  for (i=1; i<=D+1; i++)
    v[i]=ldiv(centerlift(gmul(d,compo(bl0,D+2-i))),d);
  g0=gtopoly(v,v0);
  if (DEBUGLEVEL>2)
  {
    fprintferr("val. initiales:\n");
    fprintferr("b0 = "); outerr(b0);
    fprintferr("w0 = "); outerr(w0);
    fprintferr("g0 = "); outerr(g0);
  }
  depas=1; pp=gsqr(p);
  for(;;)
  {
    if (gcmp(pp,B)>0) depas=0;
    unmodpp=gmodulsg(1,pp);
    polpp=gmul(unmodpp,pol); poldpp=gmul(unmodpp,pold);
    b0=gmodulcp(gmul(unmodpp,lift_intern(lift_intern(b0))),polpp);
    w0=gmodulcp(gmul(unmodpp,lift_intern(lift_intern(w0))),polpp);
    b1=gsub(b0,gmul(w0,gsubst(polpp,v0,b0)));
    w1=gmul(w0,gsub(gdeux,gmul(w0,gsubst(poldpp,v0,b1))));
    bl1=lift(b1); D=deg(bl1);
    v=cgetg(D+2,t_VEC);
    for (i=1; i<=D+1; i++)
      v[i]=ldiv(centerlift(gmul(d,compo(bl1,D+2-i))),d);
    g1=gtopoly(v,v0);
    if (DEBUGLEVEL>2)
    {
      fprintferr("pp = "); outerr(pp);
      fprintferr("b1 = "); outerr(b1);
      fprintferr("w1 = "); outerr(w1);
      fprintferr("g1 = "); outerr(g1);
    }
    if (gegal(g0,g1)) return gerepileupto(av,g1);
    pp=gsqr(pp); b0=b1; w0=w1; g0=g1;
    if (!depas) err(talker,"the number field is not an Abelian number field");
  }
}

static GEN
compute_denom(GEN dpol)
{
  long av=avma,lf,i,a;
  GEN d,f1,f2, f = decomp(dpol);

  f1=(GEN)f[1];
  f2=(GEN)f[2]; lf=lg(f1);
  for (d=gun,i=1; i<lf; i++)
  {
    a = itos((GEN)f2[i]) >> 1;
    d = mulii(d, gpuigs((GEN)f1[i],a));
  }
  return gerepileupto(av,d);
}

static GEN
compute_bound_for_lift(GEN pol,GEN dpol,GEN d)
{
  long av=avma,n,i;
  GEN p1,p2,p3;

  n=deg(pol);
  p1=gdiv(gmul(stoi(n),gpui(stoi(n-1),gdivgs(stoi(n-1),2),DEFAULTPREC)),
          gsqrt(dpol,DEFAULTPREC));
  p2=gzero;
  for (i=2; i<=n+2; i++) p2=gadd(p2,gsqr((GEN)pol[i]));
  p2=gpuigs(gsqrt(p2,DEFAULTPREC),n-1);
  p1=gmul(p1,p2); p2=gzero;
  for (i=2; i<=n+2; i++)
  {
    p3 = gabs((GEN)pol[i],DEFAULTPREC);
    if (gcmp(p3,p2)>0) p2 = p3;
  }
  p2=gmul(d,gadd(gun,p2));
  return gerepileupto(av, gmul2n(gsqr(gmul(p1,p2)),1));

/* Borne heuristique de P. S. Wang, Math. Comp. 30, 1976, p. 332
  p2=gzero; for (i=2; i<=n+2; i++) p2=gadd(p2,gsqr((GEN)pol[i]));
  p1=gzero;
  for (i=2; i<=n+2; i++){ if (gcmp(gabs((GEN)pol[i],4),p1)>0) p1=gabs((GEN)pol[i],4); }
  if (gcmp(p2,p1)>0) p1=p2;
  p2=gmul(gdiv(mpfactr(n,4),gsqr(mpfactr(n/2,4))),d);
  B=gmul(p1,p2);
  tetpil=avma; return gerepile(av,tetpil,gcopy(B));
*/
}

static long
isinlist(GEN T,long longT,GEN x)
{
  long i;
  for (i=1; i<=longT; i++)
    if (gegal(x,(GEN)T[i])) return i;
  return 0;
}

/* renvoie 0 si frobp n'est pas dans la liste T; sinon le no de frobp dans T */
static long
isinlistmodp(GEN T,long longT,GEN frobp,GEN p)
{
  long av=avma,i;
  GEN p1,p2,unmodp;

  p1=lift_intern(lift_intern(frobp)); unmodp=gmodulsg(1,p);
  for (i=1; i<=longT; i++)
  {
    p2=lift_intern(gmul(unmodp,(GEN)T[i]));
    if (gegal(p2,p1)) { avma=av; return i; }
  }
  avma=av; return 0;
}

/* renvoie le plus petit f tel que frobp^f est dans la liste T */
static long
minimalexponent(GEN T,long longT,GEN frobp,GEN p,long N)
{
  long av=avma,i;
  GEN p1 = frobp;
  for (i=1; i<=N; i++)
  {
    if (isinlistmodp(T,longT,p1,p)) {avma=av; return i;}
    p1 = gpui(p1,p,DEFAULTPREC);
  }
  err(talker,"missing frobenius (field not abelian ?)");
  return 0; /* not reached */
}


/* Computation of all the automorphisms of the abelian number field
   defined by the monic irreducible polynomial pol with integral coefficients */
GEN
conjugates(GEN pol)
{
  long av,tetpil,N,i,j,pp,bound_primes,nbprimes,longT,v0,flL,f,longTnew,*tab,nop;
  GEN T,S,p1,p2,p,dpol,modunp,polp,xbar,frobp,frob,d,B,nf;
  byteptr di;

  if (DEBUGLEVEL>2){ fprintferr("** Entree dans conjugates\n"); flusherr(); }
  if (typ(pol)==t_POL) nf = NULL; else { nf = checknf(pol); pol=(GEN)nf[1]; }
  av=avma; N=deg(pol); v0=varn(pol);
  if (N==1) return _vec(polx[v0]);
  if (N==2)
  {
    S=cgetg(3,t_VEC);
    S[1] = (long)polx[v0];
    S[2] = lsub(gneg(polx[v0]),(GEN)pol[3]);
    tetpil=avma; return gerepile(av,tetpil,gcopy(S));
  }
  dpol=absi(discsr(pol));
  if (DEBUGLEVEL>2)
    { fprintferr("discriminant du polynome: "); outerr(dpol); }
  d = nf? (GEN)nf[4]: compute_denom(dpol);
  if (DEBUGLEVEL>2)
    { fprintferr("facteur carre du discriminant: "); outerr(d); }
  B=compute_bound_for_lift(pol,dpol,d);
  if (DEBUGLEVEL>2) { fprintferr("borne pour les lifts: "); outerr(B); }
  /* sous GRH il faut en fait 3.47*log(dpol) */
  p1=gfloor(glog(dpol,DEFAULTPREC));
  bound_primes=itos(p1);
  if (DEBUGLEVEL>2)
  { fprintferr("borne pour les premiers: %ld\n",bound_primes); flusherr(); }
  nbprimes=itos(gfloor(gmul(dbltor(1.25506),
                            gdiv(p1,glog(p1,DEFAULTPREC)))));
  if (DEBUGLEVEL>2)
  { fprintferr("borne pour le nombre de premiers: %ld\n",nbprimes); flusherr(); }
  S=cgetg(nbprimes+1,t_VEC);
  di=diffptr; pp=*di; i=0;
  while (pp<=bound_primes)
  {
    if (smodis(dpol,pp)) { i++; S[i]=lstoi(pp); }
    pp = pp + (*(++di));
  }
  for (j=i+1; j<=nbprimes; j++) S[j]=zero;
  nbprimes=i; tab=new_chunk(nbprimes+1);
  for (i=1; i<=nbprimes; i++) tab[i]=0;
  if (DEBUGLEVEL>2)
  {
    fprintferr("nombre de premiers: %ld\n",nbprimes);
    fprintferr("table des premiers: "); outerr(S);
  }
  T=cgetg(N+1,t_VEC); T[1]=(long)polx[v0];
  for (i=2; i<=N; i++) T[i]=zero; longT=1;
  if (DEBUGLEVEL>2) { fprintferr("table initiale: "); outerr(T); }
  for(;;)
  {
    do
    {
      do
      {
        nop = 1+itos(shifti(mulss(mymyrand(),nbprimes),-(BITS_IN_RANDOM-1)));
      }
      while (tab[nop]);
      tab[nop]=1; p=(GEN)S[nop];
      if (DEBUGLEVEL>2) { fprintferr("\nnombre premier: "); outerr(p); }
      modunp=gmodulsg(1,p);
      polp=gmul(modunp,pol);
      xbar=gmodulcp(gmul(polx[v0],modunp),polp);
      frobp=gpui(xbar,p,4);
      if (DEBUGLEVEL>2) { fprintferr("frobenius mod p: "); outerr(frobp); }
      flL=isinlistmodp(T,longT,frobp,p);
      if (DEBUGLEVEL>2){ fprintferr("flL: %ld\n",flL); flusherr(); }
    }
    while (flL);
    f=minimalexponent(T,longT,frobp,p,N);
    if (DEBUGLEVEL>2){ fprintferr("exposant minimum: %ld\n",f); flusherr(); }
    frob=frobenius(pol,frobp,p,B,d);
    if (DEBUGLEVEL>2) { fprintferr("frobenius: "); outerr(frob); }
/* Ce passage n'est vrai que si le corps est abelien !! */
    longTnew=longT;
    p2=gmodulcp(frob,pol);
    for (i=1; i<=longTnew; i++)
      for (j=1; j<f; j++)
      {
	p1=lift(gsubst((GEN)T[i],v0,gpuigs(p2,j)));
	if (DEBUGLEVEL>2)
	{
	  fprintferr("test de la puissance (%ld,%ld): ",i,j); outerr(p1);
	}
	if (!isinlist(T,longTnew,p1))
	{
	  longT++; T[longT]=(long)p1;
	  if (longT==N)
          {
            if (DEBUGLEVEL>2)
              { fprintferr("** Sortie de conjugates\n"); flusherr(); }
            tetpil=avma; return gerepile(av,tetpil,gcopy(T));
          }
	}
      }
    if (DEBUGLEVEL>2) { fprintferr("nouvelle table: "); outerr(T); }
  }
}

