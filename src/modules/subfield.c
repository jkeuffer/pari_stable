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
#ifdef __WIN32
#  include <io.h> /* for open, read, close */
#endif
extern GEN roots_to_pol(GEN a, long v);

static long TR; /* nombre de changements de polynomes (degre fixe) */
static GEN FACTORDL; /* factorisation of |disc(L)| */

static GEN print_block_system(long N,GEN Y,long d, GEN vbs);
static GEN compute_data(GEN nf,GEN ff,GEN p,long m,long nn);

/* Computation of potential block systems of given size d associated to a
 * rational prime p: give a row vector of row vectors containing the
 * potential block systems of imprimitivity; a potential block system is a
 * vector of row vectors (enumeration of the roots).
 */
#define BIL 32 /* for 64bit machines also */
static GEN
calc_block(long N,GEN Z,long d,GEN Y,GEN vbs)
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
	  vbs = calc_block(N,Zpp,d,Yp,vbs);
	}
        avma=av;
      }
    }
  }
  return vbs;
}

static GEN
potential_block_systems(long N, long d,GEN ff,long *n)
{
  long av=avma,r,i,j,k;
  GEN p1,vbs,Z;

  r=lg(ff); Z=cgetg(r,t_VEC);
  for (k=0,i=1; i<r; i++)
  {
    p1=cgetg(n[i]+1,t_VECSMALL); Z[i]=(long)p1;
    for (j=1; j<=n[i]; j++) p1[j]= ++k;
  }
  vbs=calc_block(N,Z,d, cgetg(1,t_VEC), NULL);
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
      a = mael(Yi,j,1); cy = (GEN)Yi[j];
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

/* rend le numero du cycle (a1,...,an) dans le support duquel se trouve a */
/* met dans *pt l'indice i tq ai = a */
static long
in_what_cycle(long a,GEN cys,long *pt)
{
  long i,k,nk, lcys=lg(cys);

  for (k=1; k<lcys; k++)
  {
    GEN c = (GEN)cys[k]; nk = lg(c);
    for (i=1; i<nk; i++)
      if (a == c[i]) { *pt = i; return k; }
  }
  err(talker,"impossible to find %d in in_what_cycle",a);
  return 0; /* not reached */
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

static void
polsimplify(GEN x)
{
  long i,lx = lgef(x);
  for (i=2; i<lx; i++)
    if (typ(x[i]) == t_POL) x[i] = signe(x[i])? mael(x,i,2): zero;
}

/* Renvoie un polynome g definissant un sous-corps potentiel, ou
 * 0: si le polynome trouve n'est pas separable,
 * 1: si les coefficients du polynome trouve sont plus grands que la borne M,
 * 2: si p divise le discriminant de g,
 * 3: si le discriminant de g est nul,
 * 4: si la partie s de d(g) premiere avec d(L) n'est pas un carre,
 * 5: si s est un carre et si un des facteurs premiers communs a d(g) et d(L)
 *    a un exposant impair dans d(g) et un exposant plus petit que d dans d(L),
 * 6: si le discriminant du corps defini par g a la puissance d ne divise pas
 *        le discriminant du corps nf (soit L).
 */
static GEN
cand_for_subfields(GEN A,GEN DATA,GEN *ptdelta,GEN *ptrootsA)
{
  long av=avma,N,m,i,j,d,lf;
  GEN P,pe,p,pol,cys,tabroots,delta,g,dg,unmodpe,tabrA;
  GEN factcommon,ff1,ff2,p1;
  GEN *gptr[3];

  pol=(GEN)DATA[1]; N=lgef(pol)-3; m=lg(A)-1; d=N/m;
  if (N%m) err(talker,"incompatible block system in cand_for_subfields");
  p = (GEN)DATA[2];
  cys=(GEN)DATA[5];
  tabroots=(GEN)DATA[10];
  pe = gclone((GEN)DATA[9]);
  unmodpe = cgetg(3,t_INTMOD); unmodpe[1]=(long)pe; unmodpe[2]=un;

  delta = cgetg(m+1,t_VEC);
  tabrA = cgetg(m+1,t_VEC);
  for (i=1; i<=m; i++)
  {
    GEN Ai=(GEN)A[i], col = cgetg(d+1,t_VEC);
    long l,k;

    tabrA[i]=(long)col; p1 = unmodpe;
    for (j=1; j<=d; j++)
    {
      l=in_what_cycle(Ai[j],cys,&k);
      col[j] = mael(tabroots, l, k);
      p1 = gmul(p1, (GEN)col[j]);
    }
    p1 = lift_intern((GEN)p1[2]);
    for (j=1; j<i; j++)
      if (gegal(p1,(GEN)delta[j])) { avma=av; return gzero; }
    if (DEBUGLEVEL>2) fprintferr("delta[%ld] = %Z\n",i,p1);
    delta[i] = (long)p1;
  }
  P = gmael3(tabroots,1,1,1);
  for (i=1; i<=m; i++)
  {
    p1 = cgetg(3,t_POLMOD); p1[1]=(long)P; p1[2]=delta[i];
    delta[i] = (long)p1;
  }
  g = roots_to_pol(gmul(unmodpe,delta),0); 
  g=centerlift(lift_intern(g)); polsimplify(g);
  if (DEBUGLEVEL>2) fprintferr("pol. found = %Z\n",g);
  if (!ok_coeffs(g,(GEN)DATA[8])) return gun;
  dg=discsr(g);
  if (!signe(dg)) return stoi(3);
  if (!signe(resii(dg,p))) return gdeux;
  factcommon=commonfactor(FACTORDL,dg);
  ff1=(GEN)factcommon[1]; lf=lg(ff1)-1;
  if (!carreparfait((GEN)ff1[lf])) return stoi(4);
  ff2=(GEN)factcommon[2];
  for (i=1; i<lf; i++)
    if (mod2((GEN)ff2[i]) && itos(gmael(FACTORDL,2,i)) < d) return stoi(5);
  gunclone(pe);

  *ptdelta=delta; *ptrootsA=tabrA;
  gptr[0]=&g; gptr[1]=ptdelta; gptr[2]=ptrootsA;
  gerepilemany(av,gptr,3); return g;
}

/* a partir d'un polynome h(x) dont les coefficients sont definis mod p^k,
 * on construit un polynome a coefficients dans Q dont les coefficients ont
 * pour approximation p-adique les coefficients de h */
static GEN
retrieve_p_adique_polynomial_in_Q(GEN ind,GEN h)
{
  return gdiv(centerlift(gmul(h,ind)), ind);
}

/* interpolation polynomial P(x) s.t P(T[j][i]) = delta[i] mod p */
static GEN
interpolation_polynomial(GEN T, GEN delta)
{
  long i,j,i1,j1, m = lg(T), d = lg(T[1]);
  GEN P = NULL, x0 = gneg(polx[0]);

  for (j=1; j<m; j++)
  {
    GEN p3 = NULL;
    for (i=1; i<d; i++)
    {
      GEN p1=gun, p2=gun, a = gneg(gmael(T,j,i));
      for (j1=1; j1<m; j1++)
        for (i1=1; i1<d; i1++)
          if (i1 != i || j1 != j)
          {
            p1 = gmul(p1,gadd(gmael(T,j1,i1), x0));
            p2 = gmul(p2,gadd(gmael(T,j1,i1), a));
          }
      p1 = gdiv(p1,p2);
      p3 = p3? gadd(p3, p1): p1;
    }
    p3 = gmul((GEN)delta[j],p3);
    P = P? gadd(P,p3): p3;
  }
  return P;
}

/* nf est le corps de nombres, g un polynome de Z[x] candidat
 * pour definir un sous-corps, p le nombre premier ayant servi a definir le
 * potential block system rootsA donne par les racines avec une approximation
 * convenable, e est la precision p-adique des elements de rootsA et delta la
 * liste des racines de g dans une extension convenable en precision p^e.
 * Renvoie un polynome h de Q[x] tel que f divise g o h et donc tel que le
 * couple (g,h) definisse un sous-corps, ou bien gzero si rootsA n'est pas un
 * block system
 */
static GEN
embedding_of_potential_subfields(GEN nf,GEN g,GEN DATA,GEN rootsA,GEN delta)
{
  GEN w0_inQ,w0,w1,h0,gp,p2,f,unmodp,p,ind, maxp;
  long av = avma, av1;

  f=(GEN)nf[1]; ind=(GEN)nf[4]; p=(GEN)DATA[2];
  maxp=mulii((GEN)DATA[11],ind);
  gp=deriv(g,varn(g)); unmodp=gmodulsg(1,p);
  av1 = avma;
  w0 = interpolation_polynomial(gmul(rootsA,unmodp), delta);
  w0 = lift_intern(w0); /* in Fp[x] */
  polsimplify(w0);
  w0_inQ = retrieve_p_adique_polynomial_in_Q(ind,w0);
  (void)gbezout(poleval(gp,w0), gmul(unmodp,f), &h0, &p2);
  w0 = lift_intern(w0); /* in Z[x] */
  h0 = lift_intern(lift_intern(h0));
  for(;;)
  {
    GEN p1;
   /* Given g in Z[x], gp its derivative, p a prime, [w0,h0] in Z[x] s.t.
    * h0(x).gp(w0(x)) = 1 and g(w0(x))  = 0 (mod f,mod p), return
    * [w1,h1]  satisfying the same condition mod p^2. Moreover,
    * [w1,h1] = [w0,h0] (mod p)
    * (cf. Dixon: J. Austral. Math. Soc., Series A, vol.49, 1990, p.445) */
    if (DEBUGLEVEL>2)
    {
      fprintferr("w = "); outerr(w0);
      fprintferr("h = "); outerr(h0);
    }
    p = sqri(p); unmodp[1] = (long)p;
    p1 = gneg(gmul(h0, poleval(g,w0)));
    w1 = gres(gmul(unmodp,gadd(w0,p1)), f);
    p2 = retrieve_p_adique_polynomial_in_Q(ind,w1);
    if ((gegal(p2, w0_inQ) || cmpii(p,maxp)) && gdivise(poleval(g,p2), f))
      return gerepileupto(av, poleval(p2, gadd(polx[0],stoi(TR))));
    if (DEBUGLEVEL>2)
    {
      fprintferr("Old Q-polynomial: "); outerr(w0_inQ);
      fprintferr("New Q-polynomial: "); outerr(p2);
    }
    if (cmpii(p, maxp) > 0)
    {
      if (DEBUGLEVEL) fprintferr("coeff too big for embedding\n");
      avma=av; return gzero;
    }

    w1 = lift_intern(w1);
    p1 = gneg(gmul(h0, poleval(gp,w1)));
    p1 = gmul(h0, gadd(gdeux,p1));
    h0 = lift_intern(gres(gmul(unmodp,p1), f));
    w0 = w1; w0_inQ = p2;
    {
      GEN *gptr[4]; gptr[0]=&w0; gptr[1]=&h0; gptr[2]=&w0_inQ; gptr[3]=&p;
      gerepilemany(av1,gptr,4);
    }
  }
}

static long
choose_prime(GEN pol,GEN dpol,long d,GEN *ptff,GEN *ptlistpotbl, long *ptnn)
{
  long j,k,oldllist,llist,r,nn,oldnn,*n,N,pp;
  GEN p,listpotbl,oldlistpotbl,ff,oldff,p3;
  byteptr di=diffptr;

  if (DEBUGLEVEL) timer2();
  di++; p = stoi(2); N = lgef(pol)-3;
  while (p[2]<=N) p[2] += *di++;
  oldllist = oldnn = BIGINT;
  oldlistpotbl = oldff = NULL; pp = 0; /* gcc -Wall */
  n = new_chunk(N+1);
  for(k=1; k<11 || oldnn == BIGINT; k++,p[2]+= *di++)
  {
    long av=avma;
    while (!smodis(dpol,p[2])) p[2] += *di++;
    ff=(GEN)factmod(pol,p)[1]; r=lg(ff)-1;
    if (r>1 && r<N)
    {
      for (j=1; j<=r; j++) n[j]=lgef(ff[j])-3;
      p3 = stoi(n[1]);
      for (j=2; j<=r; j++) p3 = glcm(p3,stoi(n[j]));
      nn=itos(p3);
      if (nn > oldnn)
      {
        if (DEBUGLEVEL)
        {
          fprintferr("p = %ld,\tr = %ld,\tnn = %ld,\t#pbs = skipped\n",
                      p[2],r,nn);
        }
        continue;
      }
      listpotbl=potential_block_systems(N,d,ff,n);
      if (!listpotbl) { oldlistpotbl = NULL; pp = p[2]; break; }
      llist=lg(listpotbl)-1;
      if (DEBUGLEVEL)
      {
	fprintferr("Time: %ldms,\tp = %ld,\tr = %ld,\tnn = %ld,\t#pbs = %ld\n",
                    timer2(),p[2],r,nn,llist);
	flusherr();
      }
      if (nn<oldnn || llist<oldllist)
      {
	oldllist=llist; oldlistpotbl=listpotbl;
	pp=p[2]; oldff=ff; oldnn=nn; continue;
      }
      for (j=1; j<llist; j++) free((void*)listpotbl[j]);
      free((void*)(listpotbl-1));
    }
    avma = av;
  }
  if (DEBUGLEVEL)
  {
    fprintferr("Chosen prime: p = %ld\n",pp);
    if (DEBUGLEVEL>2)
      fprintferr("List of potential block systems of size %ld: %Z\n",
                  d,oldlistpotbl);
    flusherr();
  }
  *ptlistpotbl=oldlistpotbl; *ptff=oldff; *ptnn=oldnn; return pp;
}

static GEN
change_pol(GEN nf, GEN ff)
{
  long i,l;
  GEN pol = (GEN)nf[1], p1 = gsub(polx[0],gun);

  TR++; pol=poleval(pol, p1);
  nf = dummycopy(nf);
  nf[6] = (long)dummycopy((GEN)nf[6]);
  l=lg(ff);
  for (i=1; i<l; i++) ff[i]=(long)poleval((GEN)ff[i], p1);
  l=lg(nf[6]); p1=(GEN)nf[6];
  for (i=1; i<l; i++) p1[i]=ladd(gun,(GEN)p1[i]);
  nf[1]=(long)pol; return nf;
}

static GEN
bound_for_coeff(long m,GEN rr,long r1, GEN *maxroot)
{
  long i, lrr=lg(rr);
  GEN p1,b1,b2,B,M, C = matpascal(m-1);

  rr = gabs(rr,DEFAULTPREC); *maxroot = vecmax(rr);
  for (i=1; i<lrr; i++)
    if (gcmp((GEN)rr[i], gun) < 0) rr[i] = un;
  for (b1=gun,i=1; i<=r1; i++) b1 = gmul(b1, (GEN)rr[i]);
  for (b2=gun    ; i<lrr; i++) b2 = gmul(b2, (GEN)rr[i]);
  B = gmul(b1, gsqr(b2));
  M = cgetg(m+2, t_VEC); M[1]=M[2]=zero; /* unused */
  for (i=1; i<m; i++)
  {
    p1 = gadd(gmul(gcoeff(C, m, i), B),
              gcoeff(C, m, i+1));
    M[i+2] = lceil(p1);
  }
  return M;
}

/* liste des sous corps de degre d du corps de nombres nf */
static GEN
subfields_of_given_degree(GEN nf,GEN dpol,long d)
{
  long av,av1,av2,tetpil,pp,llist,i,nn,N;
  GEN listpotbl,ff,A,delta,rootsA,CSF,ESF,p1,p2,LSB;
  GEN DATA, pol = (GEN)nf[1];

  av=avma;
  N = lgef(pol)-3;
  pp=choose_prime(pol,dpol,N/d,&ff,&listpotbl,&nn);
  if (!listpotbl) { avma=av; return cgetg(1,t_VEC); }
  llist=lg(listpotbl);
LAB0:
  av1=avma; LSB=cgetg(1,t_VEC);
  DATA=compute_data(nf,ff,stoi(pp),d,nn);
  for (i=1; i<llist; i++)
  {
    av2=avma; A=(GEN)listpotbl[i];
    if (DEBUGLEVEL > 1) 
      fprintferr("\n* Potential block # %ld: %Z\n",i,A);
    CSF=cand_for_subfields(A,DATA,&delta,&rootsA);
    if (typ(CSF)==t_INT)
    {
      if (DEBUGLEVEL > 1) switch(itos(CSF))
      {
        case 0: fprintferr("changing f(x): non separable g(x)\n"); break;
        case 1: fprintferr("coeff too big for pol g(x)\n"); break;
        case 2: fprintferr("changing f(x): p divides disc(g(x))\n"); break;
        case 3: fprintferr("non irreducible polynomial g(x)\n"); break;
        case 4: fprintferr("prime to d(L) part of d(g) not a square\n"); break;
        case 5: fprintferr("too small exponent of a prime factor in d(L)\n"); break;
        case 6: fprintferr("the d-th power of d(K) does not divide d(L)\n");
      }
      switch(itos(CSF))
      {
        case 0: case 2:
          avma=av1; nf = change_pol(nf,ff); pol = (GEN)nf[1];
          if (DEBUGLEVEL) fprintferr("new f = %Z\n",pol);
          goto LAB0;
      }
      avma=av2;
    }
    else
    {
      if (DEBUGLEVEL) fprintferr("candidate = %Z\n",CSF);
      ESF=embedding_of_potential_subfields(nf,CSF,DATA,rootsA,delta);
      if (ESF == gzero) avma=av2;
      else
      {
        if (DEBUGLEVEL) fprintferr("embedding = %Z\n",ESF);
	p1=cgetg(3,t_VEC); p2=cgetg(2,t_VEC); p2[1]=(long)p1;
        p1[1]=(long)CSF;
        p1[2]=(long)ESF; tetpil=avma;
        LSB=gerepile(av2,tetpil, concat(LSB,p2));
      }
    }
  }
  for (i=1; i<llist; i++) free((void*)listpotbl[i]);
  free((void*)(listpotbl-1)); tetpil=avma;
  return gerepile(av,tetpil,gcopy(LSB));
}

GEN
subfields(GEN nf,GEN d)
{
  long av=avma,di,N,v0,lp1,i;
  GEN dpol,p1,LSB,p2,pol;

  nf=checknf(nf); pol = (GEN)nf[1];
  v0=varn(pol); N=lgef(pol)-3; di=itos(d);
  if (di==N)
  {
    LSB=cgetg(2,t_VEC); p1=cgetg(3,t_VEC); LSB[1]=(long)p1;
    p1[1]=lcopy(pol); p1[2]=lpolx[v0]; return LSB;
  }
  if (di==1)
  {
    LSB=cgetg(2,t_VEC); p1=cgetg(3,t_VEC); LSB[1]=(long)p1;
    p1[1]=lpolx[v0]; p1[2]=lcopy(pol); return LSB;
  }
  if (di<=0 || di>N || N%di) return cgetg(1,t_VEC);

  TR=0; dpol=mulii((GEN)nf[3],sqri((GEN)nf[4]));
  if (v0) nf=gsubst(nf,v0,polx[0]);
  FACTORDL=factor(absi((GEN)nf[3]));
  p1=subfields_of_given_degree(nf,dpol,di); lp1=lg(p1)-1;
  if (v0)
    for (i=1; i<=lp1; i++)
      { p2=(GEN)p1[i]; setvarn(p2[1],v0); setvarn(p2[2],v0); }
  return gerepileupto(av,p1);
}

static GEN
subfieldsall(GEN nf)
{
  long av=avma,av1,N,ld,d,i,j,lNLSB,v0,lp1;
  GEN pol,dpol,dg,LSB,NLSB,p1,p2;

  nf=checknf(nf); pol = (GEN)nf[1];
  v0=varn(pol); N=lgef(pol)-3;
  if (isprime(stoi(N)))
  {
    avma=av; LSB=cgetg(3,t_VEC);
    LSB[1]=lgetg(3,t_VEC); LSB[2]=lgetg(3,t_VEC);
    p1=(GEN)LSB[1]; p1[1]=lcopy(pol); p1[2]=lpolx[v0];
    p2=(GEN)LSB[2]; p2[1]=p1[2]; p2[2]=p1[1];
    return LSB;
  }
  FACTORDL=factor(absi((GEN)nf[3])); dg=divisors(stoi(N));
  dpol=mulii(sqri((GEN)nf[4]),(GEN)nf[3]);
  if (DEBUGLEVEL>0)
  {
    fprintferr("\n***** Entering subfields\n\n");
    fprintferr("pol = "); outerr(pol);
    fprintferr("dpol = "); outerr(dpol);
    fprintferr("divisors = "); outerr(dg);
  }
  ld=lg(dg)-1; LSB=cgetg(2,t_VEC); LSB[1]=lgetg(3,t_VEC);
  p1=(GEN)LSB[1]; p1[1]=(long)pol; p1[2]=(long)polx[0];
  if (v0) nf=gsubst(nf,v0,polx[0]);
  for (i=2; i<ld; i++)
  {
    TR=0; av1=avma; d=itos((GEN)dg[i]);
    if (DEBUGLEVEL>0)
    {
      fprintferr("\n*** Looking for subfields of degree %ld\n\n",N/d);
      flusherr();
    }
    NLSB=subfields_of_given_degree(nf,dpol,N/d);
    if (DEBUGLEVEL)
    {
      fprintferr("\nSubfields of degree %ld:\n",N/d);
      lNLSB=lg(NLSB)-1; for (j=1; j<=lNLSB; j++) outerr((GEN)NLSB[j]);
    }
    if (lg(NLSB)>1) LSB = concatsp(LSB,NLSB); else avma=av1;
  }
  p1=cgetg(2,t_VEC); p1[1]=lgetg(3,t_VEC);p2=(GEN)p1[1];
  p2[1]=(long)polx[0]; p2[2]=(long)pol;
  LSB=concatsp(LSB,p1); lp1=lg(LSB)-1;
  LSB = gerepileupto(av, gcopy(LSB));
  if (v0)
    for (i=1; i<=lp1; i++)
      { p2=(GEN)LSB[i]; setvarn(p2[1],v0); setvarn(p2[2],v0); }
  if (DEBUGLEVEL>0) fprintferr("\n***** Leaving subfields\n\n");
  return LSB;
}

GEN
subfields0(GEN nf,GEN d)
{
  return d? subfields(nf,d): subfieldsall(nf);
}

extern GEN FpX_rand(long d1, long v, GEN p);

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

static GEN
lift_coeff(GEN x, GEN fq)
{
  GEN r;
  if (typ(x) == t_POLMOD) { r = x; x = (GEN)x[2]; }
  else r = cgetg(3,t_POLMOD);
  r[1]=(long)fq; r[2]=(long)lift_intern(x); return r;
}

/* a is a polynomial whose coeffs are in Fq (= (Z/p)[y] / (fqbar), where
 * fqbar is the reduction of fq mod p).
 * Lift _in place_ the coeffs so that they belong to Z[y] / (fq)
 */
static GEN
special_lift(GEN a,GEN fq)
{
  long la,i;
  GEN c;

  if (typ(a)==t_POL)
  {
    la=lgef(a); c=cgetg(la,t_POL); c[1]=a[1];
    for (i=2; i<la; i++) c[i]=(long)lift_coeff((GEN)a[i],fq);
    return c;
  }
  return lift_coeff(a,fq);
}

/* Hensel lift: fk = vector of factors of pol (unramified) in finite field
 * Fp / fkk. Lift it to the precision p^e. This is equivalent to working
 * in precision pi^e in the unramified extension of Qp given by fkk.
 */
GEN
hensel_lift(GEN pol,GEN fk,GEN fkk,GEN p,long e)
{
  long av = avma, i, r = lg(fk)-1;
  GEN p1,A,B,C,R,U,V,fklift,fklift2,fk2;
  GEN unmodp = gmodulsg(1,p), fq = lift(fkk);

  fk2=cgetg(r+1,t_VEC);
  fklift=cgetg(r+1,t_VEC);
  fklift2=cgetg(r+1,t_VEC);
  fk2[r] = fklift2[r] = un;
  for (i=r; i>1; i--)
  {
    fk2[i-1] = lmul((GEN)fk2[i],(GEN)fk[i]);
    fklift[i] = (long)special_lift(gcopy((GEN)fk[i]),fq);
    fklift2[i-1] = lmul((GEN)fklift2[i],(GEN)fklift[i]);
  }
  fklift[1] = (long)special_lift(gcopy((GEN)fk[1]),fq);
  R=cgetg(r+1,t_VEC); C=pol;
  for (i=1; i<r; i++)
  { /* treat factors two by two: fk[i] and fk2[i] = product fk[i+1..] */
    long av1 = avma,tetpil1, ex = 1;
    GEN pp;

    (void)gbezout((GEN)fk[i],(GEN)fk2[i],&U,&V);
    A = (GEN)fklift[i];  U = special_lift(U,fq);
    B = (GEN)fklift2[i]; V = special_lift(V,fq);
    for (pp=p;; pp=sqri(pp))
    { /* Algorithm 3.5.[5,6] H. Cohen page 137 (1995) */
      GEN f,t,A0,B0,U0,V0;

      unmodp[1] = (long)pp;
      p1 = gneg_i(gmul(A,B));
      p1=gdiv(gadd(C,p1),pp);
      f=gmul(p1,unmodp);
      t=poldivres(gmul(V,f),A, &A0);
      A0=special_lift(A0,fq);
      B0=special_lift(gadd(gmul(U,f),gmul(B,t)),fq);
      A0 = gmul(A0,pp);
      B0 = gmul(B0,pp); tetpil1 = avma;
      A = gadd(A, A0);
      B = gadd(B, B0); ex <<= 1;
      if (ex>=e)
      {
        GEN *gptr[2]; gptr[0]=&A; gptr[1]=&B;
        gerepilemanysp(av1,tetpil1,gptr,2);
        C = B; R[i] = (long)A; break;
      }
      p1 = gneg_i(gadd(gmul(U,A),gmul(V,B)));
      p1=gdiv(gadd(gun,p1),pp);
      f=gmul(p1,unmodp);
      t=poldivres(gmul(V,f),A, &V0);
      U0=special_lift(gadd(gmul(U,f),gmul(B,t)),fq);
      V0=special_lift(V0,fq);
      U = gadd(U, gmul(U0,pp));
      V = gadd(V, gmul(V0,pp));
    }
  }
  if (r==1) C = gcopy(C);
  R[r] = (long)C; return gerepileupto(av,R);
}

/* etant donne nf et p et la factorisation de nf[1] mod p, et le degre m des
 * sous corps cherches, cree un vecteur ligne a 13 composantes:
 * 1 : le polynome nf[1],
 * 2 : le premier p,
 * 3 : la factorisation ff,
 * 4 : la longeur des cycles associes (n_1,...,n_r),
 * 5 : les cycles associes,
 * 6 : le corps F_(p^q),
 * 7 : les racines de f dans F_(p^q) par facteur de ff,
 * 8 : la borne M pour les sous-corps,
 * 9 : l'exposant e telle que la precision des lifts soit p^e>2.M,
 * 10: le lift de Hensel a la precision p^e de la factorisation en facteurs
 *     lineaires de nf[1] dans F_(p^q),
 * 11: la borne de Hadamard pour les coefficients de h(x) tel que g o h = 0
 *     mod nf[1].
 * ces donnees sont valides pour nf, p et m (d) donnes...
 */
static GEN
compute_data(GEN nf, GEN ff, GEN p, long m, long nn)
{
  long i,j,l,r,*n,e,N,pp,d,r1;
  GEN DATA,p1,p2,cys,fhk,tabroots,MM,fk,dpol,maxroot,maxMM,pol;

  if (DEBUGLEVEL>1) { fprintferr("Entering compute_data()\n\n"); flusherr(); }
  pol = (GEN)nf[1]; N = lgef(pol)-3;
  DATA=cgetg(14,t_VEC);
  DATA[1]=(long)pol;
  DATA[2]=(long)p; r=lg(ff)-1;
  DATA[3]=(long)ff;
  n = cgetg(r+1, t_VECSMALL);
  DATA[4]= (long)n;
  for (j=1; j<=r; j++) n[j]=lgef(ff[j])-3;
  cys=cgetg(r+1,t_VEC); l=0;
  for (i=1; i<=r; i++)
  {
    p1 = cgetg(n[i]+1, t_VECSMALL);
    cys[i] = (long)p1; for (j=1; j<=n[i]; j++) p1[j]=++l;
  }
  DATA[5]=(long)cys;
  DATA[6]=(long)ffinit(p,nn,MAXVARN);
  tabroots=cgetg(r+1,t_VEC);
  for (j=1; j<=r; j++)
  {
    p1=(GEN)factmod9((GEN)ff[j],p,(GEN)DATA[6])[1];
    p2=cgetg(n[j]+1,t_VEC); tabroots[j]=(long)p2;
    p2[1]=lneg(gmael(p1,1,2));
    for (i=2; i<=n[j]; i++) p2[i]=(long)powgi((GEN)p2[i-1],p);
  }
  DATA[7]=(long)tabroots;
  r1=itos(gmael(nf,2,1));
  MM = bound_for_coeff(m, (GEN)nf[6], r1, &maxroot);
  MM = gmul2n(MM,1);
  DATA[8]=(long)MM;
  pp=itos(p); maxMM = vecmax(MM);
  for (e=1,p1=p; cmpii(p1, maxMM) < 0; ) { p1 = mulis(p1,pp); e++; }
  DATA[9]=lpuigs(p,e); fk=cgetg(N+1,t_VEC);
  for (l=1,j=1; j<=r; j++)
    for (i=1; i<=n[j]; i++)
      fk[l++] = lsub(polx[0],gmael(tabroots,j,i));
  fhk = hensel_lift(pol,fk,(GEN)DATA[6],p,e);
  tabroots=cgetg(r+1,t_VEC);
  for (l=1,j=1; j<=r; j++)
  {
    p1 = cgetg(n[j]+1,t_VEC); tabroots[j]=(long)p1;
    for (i=1; i<=n[j]; i++,l++) p1[i] = lneg(gmael(fhk,l,2));
  }
  DATA[10]=(long)tabroots;

  d=N/m; p1=gmul(stoi(N), gsqrt(gpuigs(stoi(N-1),N-1),DEFAULTPREC));
  p2 = gpuigs(maxroot, d + N*(N-1)/2);
  dpol=mulii(sqri((GEN)nf[4]),(GEN)nf[3]);
  p1 = gdiv(gmul(p1,p2), gsqrt(absi(dpol),DEFAULTPREC));
  p1 = grndtoi(p1, &e);
  if (e>=0) p1 = addii(p1, shifti(gun, e));
  p1 = shifti(p1, 1);
  DATA[11]=(long)p1;

  if (DEBUGLEVEL>1)
  {
    fprintferr("DATA =\n");
    fprintferr("f = "); outerr((GEN)DATA[1]);
    fprintferr("p = "); outerr((GEN)DATA[2]);
    fprintferr("ff = "); outerr((GEN)DATA[3]);
    fprintferr("lcy = "); outerr((GEN)DATA[4]);
    fprintferr("cys = "); outerr((GEN)DATA[5]);
    fprintferr("bigfq = "); outerr((GEN)DATA[6]);
    fprintferr("roots = "); outerr((GEN)DATA[7]);
    fprintferr("2 * M = "); outerr((GEN)DATA[8]);
    fprintferr("p^e = "); outerr((GEN)DATA[9]);
    fprintferr("lifted roots = "); outerr((GEN)DATA[10]);
    fprintferr("2 * Hadamard bound = "); outerr((GEN)DATA[11]);
  }
  return DATA;
}

/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*                                                                 */
/*               AUTOMORPHISMS OF AN ABELIAN NUMBER FIELD          */
/*                                                                 */
/*               V. Acciaro and J. Klueners (1996)                 */
/*                                                                 */
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*/

/* calcul du frobenius en p pour le corps abelien defini par le polynome pol,
 * par relevement de hensel du frobenius frobp de l'extension des corps
 * residuels (frobp est un polynome mod pol a coefficients dans F_p)
 */
static GEN
frobenius(GEN pol,GEN frobp,GEN p,GEN B,GEN d)
{
  long av=avma,v0,deg,i,depas;
  GEN b0,b1,pold,polp,poldp,w0,w1,g0,g1,unmodp,polpp,v,pp,unmodpp,poldpp,bl0,bl1;

  v0=varn(pol); unmodp=gmodulsg(1,p); pold=deriv(pol,v0);
  b0=frobp; polp=gmul(unmodp,pol);
  poldp=gsubst(deriv(polp,v0),v0,frobp);
  w0=ginv(poldp);
  bl0=lift(b0); deg=lgef(bl0)-3;
  v=cgetg(deg+2,t_VEC);
  for (i=1; i<=deg+1; i++)
    v[i]=ldiv(centerlift(gmul(d,compo(bl0,deg+2-i))),d);
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
    bl1=lift(b1); deg=lgef(bl1)-3;
    v=cgetg(deg+2,t_VEC);
    for (i=1; i<=deg+1; i++)
      v[i]=ldiv(centerlift(gmul(d,compo(bl1,deg+2-i))),d);
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

  n=lgef(pol)-3;
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
  av=avma; N=lgef(pol)-3; v0=varn(pol);
  if (N==1) { S=cgetg(2,t_VEC); S[1]=(long)polx[v0]; return S; }
  if (N==2)
  {
    S=cgetg(3,t_VEC); S[1]=(long)polx[v0];
    S[2]=lsub(gneg(polx[v0]),(GEN)pol[3]);
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

