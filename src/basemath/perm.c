/* $Id$

Copyright (C) 2000-2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"

/*************************************************************************/
/**                                                                     **/
/**                   Routine for handling VECSMALL                     **/
/**                                                                     **/
/*************************************************************************/

GEN vecsmall_const(long n, long c)
{
  long i;
  GEN V=cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) V[i]=c;
  return V;
}

GEN vecsmall_shorten(GEN v, long n)
{
  long i;
  GEN V=cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) V[i]=v[i];
  return V;
 
}

/*in place sort.*/
void vecsmall_sort(GEN V)
{
  long i,j,k,l,m;
  for(l=1;l<lg(V);l<<=1)
    for(j=1;(j>>1)<lg(V);j+=l<<1)
      for(k=j+l,i=j; i<k && k<j+(l<<1) && k<lg(V);)
	if (V[i]>V[k])
	{
	  long z=V[k];
	  for (m=k;m>i;m--)
	    V[m]=V[m-1];
	  V[i]=z;
	  k++;
	}
	else
	  i++;
}

GEN vecsmall_uniq(GEN V)
{
  pari_sp ltop=avma;
  GEN W;
  long i,j;
  if ( lg(V) == 1 ) return gcopy(V);
  W=cgetg(lg(V),t_VECSMALL);
  W[1]=V[1];
  for(i=2,j=1;i<lg(V);i++)
    if (V[i]!=W[j])
      W[++j]=V[i];
  setlg(W,j+1);
  return gerepileupto(ltop,W);
}

int
vecsmall_lexcmp(GEN x, GEN y)
{
  long lx,ly,l,i;
  lx = lg(x);
  ly = lg(y); l = min(lx,ly);
  for (i=1; i<l; i++)
    if (x[i]!=y[i])
      return x[i]<y[i]?-1:1;
  if (lx == ly) return 0;
  return (lx < ly)? -1 : 1;
}

int
vecsmall_prefixcmp(GEN x, GEN y)
{
  long lx,ly,l,i;
  lx = lg(x);
  ly = lg(y); l = min(lx,ly);
  for (i=1; i<l; i++)
    if (x[i]!=y[i])
      return x[i]<y[i]?-1:1;
  return 0;
}

/*Can be used on vector but with no copy*/
GEN vecsmall_prepend(GEN V, long s)
{
  GEN res;
  long l2 = lg(V);
  long i;
  res = cgetg(l2+1, typ(V));
  res[1]=s;
  for (i = 2; i <= l2; ++i)
    res[i] = V[i - 1];
  return res;
}

/*Can be used on vector but with no copy*/
GEN vecsmall_append(GEN V, long s)
{
  GEN res;
  long l2 = lg(V);
  long i;
  res = cgetg(l2+1, typ(V));
  for (i = 1; i < l2; ++i)
    res[i] = V[i];
  res[l2]=s;
  return res;
}

GEN vecsmall_concat(GEN u, GEN v)
{
  GEN res;
  long l1 = lg(u)-1;
  long l2 = lg(v)-1;
  long i;
  res = cgetg(l1+l2+1, t_VECSMALL);
  for (i = 1; i <= l1; ++i)
    res[i] = u[i];
  for (i = 1; i <= l2; ++i)
    res[i+l1] = v[i];
  return res;
}
/* return the number of indices where u and v are equal.
 */

long
vecsmall_coincidence(GEN u, GEN v)
{
  long l=min(lg(u),lg(v));
  long i,s=0;
  for(i=1;i<l;i++)
    if(u[i]==v[i])
      s++;
  return s;
}

/*************************************************************************/
/**                                                                     **/
/**               Routine for handling bit vector                       **/
/**                                                                     **/
/*************************************************************************/

GEN
bitvec_alloc(long n)
{
  long l=1+(n>>TWOPOTBITS_IN_LONG);
  return vecsmall_const(l,0);
}


GEN
bitvec_shorten(GEN bitvec, long n)
{
  long l=1+(n>>TWOPOTBITS_IN_LONG);
  return vecsmall_shorten(bitvec,l);
}

long
bitvec_test(GEN bitvec, long b)
{
  long q=b>>TWOPOTBITS_IN_LONG;
  long r=b&(BITS_IN_LONG-1);
  return (bitvec[1+q]>>r)&1L;
}

void
bitvec_set(GEN bitvec, long b)
{
  long q=b>>TWOPOTBITS_IN_LONG;
  long r=b&(BITS_IN_LONG-1);
  bitvec[1+q]|=1L<<r;
}

void
bitvec_clear(GEN bitvec, long b)
{
  long q=b>>TWOPOTBITS_IN_LONG;
  long r=b&(BITS_IN_LONG-1);
  bitvec[1+q]&=~(1L<<r);
}

/*************************************************************************/
/**                                                                     **/
/**               Routine for handling vector of VECSMALL               **/
/**                                                                     **/
/*************************************************************************/

GEN
vecvecsmall_sort(GEN x)
{
  return gen_sort(x, 0, vecsmall_lexcmp);
}

GEN
vecvecsmall_indexsort(GEN x)
{
  GEN p=gen_sort(x, cmp_IND | cmp_C, vecsmall_lexcmp);
  return p;
}

long
vecvecsmall_search(GEN x, GEN y, long flag)
{
  return gen_search(x,y,flag,vecsmall_prefixcmp);
}

/*************************************************************************/
/**                                                                     **/
/**                   Routine for handling permutations                 **/
/**                                                                     **/
/*************************************************************************/

/* Permutations may be given by
 * perm (VECSMALL): a bijection from 1...n to 1...n i-->perm[i]
 * cyc (VEC of VECSMALL): a product of disjoint cycles.
 */

/* indentity permutation */
/* Not a good name since l is not a perm...*/
GEN
perm_identity(long l)
{
  GEN     perm;
  int     i;
  perm = cgetg(l + 1, t_VECSMALL);
  for (i = 1; i <= l; i++)
    perm[i] = i;
  return perm;
} 

GEN
cyclicperm(long l, long d)
{
  GEN     perm;
  int     i;
  perm = cgetg(l + 1, t_VECSMALL);
  for (i = 1; i <= l-d; i++)
    perm[i] = i+d;
  for (i = l-d+1; i <= l; i++)
    perm[i] = i-l+d;
  return perm;
}

/*
 * Multiply (compose) two permutations.
 * Can be used if s is a vector but with no copy
 */
GEN
perm_mul(GEN s, GEN t)
{
  GEN     u;
  int     i;
  if (lg(s) < lg(t))
    err(talker, "First permutation shorter than second in perm_mul");
  u = cgetg(lg(s), typ(s));
  for (i = 1; i < lg(s); i++)
    u[i] = s[t[i]];
  return u;
}
/* Compute the inverse (reciprocal) of a permutation.
 */
GEN
perm_inv(GEN x)
{
      long i,lx = lg(x);
      GEN y = cgetg(lx,t_VECSMALL);
      for (i=1; i<lx; i++) y[x[i]] = i;
      return y;
}

/* Orbits of the subgroup generated by v on {1,..,n}
 */
GEN
vecperm_orbits(GEN v, long n)
{
  pari_sp ltop = avma;
  int     j, k, l, m, o, p, flag;
  GEN     bit, cycle, cy;
  long    mj=1;
  cycle = cgetg(n+1, t_VEC);
  bit = bitvec_alloc(n);
  for (k = 1, l = 1; k <= n;)
  {
    for (  ; bitvec_test(bit,mj); mj++);
    cy = cgetg(n+1, t_VECSMALL);
    m = 1;
    cy[m++] = mj;
    bitvec_set(bit,mj++);
    k++;
    do
    {
      flag = 0;
      for (o = 1; o < lg(v); o++)
      {
	for (p = 1; p < m; p++)	/* m varie! */
	{
	  j = mael(v,o,cy[p]);
	  if (!bitvec_test(bit,j))
	  {
	    flag = 1;
	    bitvec_set(bit,j);
	    k++;
	    cy[m++] = j;
	  }
	}
      }
    }
    while (flag);
    setlg(cy, m);
    cycle[l++] = (long) cy;
  }
  setlg(cycle, l);
  return gerepilecopy(ltop, cycle);
}

/* Compute the cyclic decomposition of a permutation
 */

GEN
perm_cycles(GEN v)
{
  pari_sp ltop = avma;
  GEN  u = cgetg(2, t_VEC);
  u[1] = (long) v;
  return gerepileupto(ltop, vecperm_orbits(u, lg(v)-1));
}
/* Compute the power of a permutation given by product of cycles
 * Ouput a perm, not a cyc.
 * */
GEN
cyc_powtoperm(GEN cyc, long exp)
{
  int     j, k, n;
  GEN     p;
  for (n = 0, j = 1; j < lg(cyc); j++)
    n += lg(cyc[j]) - 1;
  p = cgetg(n + 1, t_VECSMALL);
  for (j = 1; j < lg(cyc); j++)
  {
    n = lg(cyc[j]) - 1;
    for (k = 1; k <= n; k++)
      p[mael(cyc,j,k)] = mael(cyc,j,1 + (k + exp - 1) % n);
  }
  return p;
}

/*Output the order of p*/

long
perm_order(GEN p)
{
  long l=lg(p)-1;
  GEN id=perm_identity(l);
  GEN q=p;
  long o=1,inc,linc=-1;
  long k=1;
  linc=vecsmall_coincidence(p,id);
  while(linc<l)
  {
    q=perm_mul(p,q);  
    k++; 
    inc=vecsmall_coincidence(q,id);
    if(inc>linc)
    {
      p=q;
      o*=k;
      k=1;
      linc=inc;
    }
  }
  return o;
}

/*
 * Compute the power of a permutation.
 * TODO: make it more clever with small exp.
 */
GEN
perm_pow(GEN perm, long exp)
{
  return cyc_powtoperm(perm_cycles(perm),exp);
}

GEN 
perm_to_GAP(GEN p)	  /* genstr */
{
  pari_sp ltop=avma;
  GEN gap;	  /* genstr */
  GEN x;	  /* vec */
  long i;
  long nb=0,c=0;
  char *s;
  if (typ(p) != t_VECSMALL)  err(typeer, "perm_to_GAP");
  x = perm_cycles(p);
  /*Dry run*/
  for (i = 1; i < lg(x); ++i)
  {
    long j;
    GEN z = (GEN) x[i];
    for (j = 1; j < lg(z); ++j)
    {
      long n;
      if (j > 1)
        nb+=2;
      for(n=z[j]; n ; n /= 10) 
        nb++;
    }
    nb+=3;
  }
  /*Real run*/
  nb = (nb+2*BYTES_IN_LONG-1) >> TWOPOTBYTES_IN_LONG;
  gap = cgetg(nb,t_STR);
  s = (char*)(gap+1);
  for (i = 1; i < lg(x); ++i)
  {
    long j;
    GEN z = (GEN) x[i];
    s[c++] = '(';
    for (j = 1; j < lg(z); ++j)
    {
      long n;
      if (j > 1)
      {
        s[c++] = ','; s[c++] = ' ';
      }
      for(n = z[j]; n ; n /= 10) 
        s[c++] = n%10 + '0';
    }
    s[c++] = ')';
  }
  s[c++]=0;
  return gerepileupto(ltop,gap);
}
/*************************************************************************/
/**                                                                     **/
/**                   Routine for handling groups                       **/
/**                                                                     **/
/*************************************************************************/

/* Groups are vector [gen,orders]
 * gen (vecvecsmall): list of generators given by permutations 
 * orders (vecsmall): relatives orders of generators.
 */

GEN trivialsubgroups(void)
{
  GEN p2,p3;	  /* vec */
  p2 = cgetg(2, t_VEC);
  p3 = cgetg(3, t_VEC);
  p3[1] = (long) cgetg(1,t_VEC);
  p3[2] = (long) cgetg(1,t_VECSMALL);
  p2[1] = (long) p3;
  return p2;
}



/* Compute the orders of p modulo the group S given by a set.
 */
long
perm_relorder(GEN p, GEN S)
{
  pari_sp ltop=avma;
  long n = 1;
  GEN  q = p;
  while (!vecvecsmall_search(S, q, 0))
  {
    q = perm_mul(q, p);
    ++n;
  }
  ltop=avma;
  return n;
}

GEN perm_generate(GEN S, GEN H, long o)
{
  long i,k;
  long n = lg(H)-1;
  GEN L = cgetg(1+n*o, t_VEC);
  for(i=1; i<=n; i++)
    L[i]=lcopy((GEN)H[i]);
  for(k=n+1; k <= n*o; ++k)
    L[k] = (long) perm_mul((GEN) L[k-n], S);
  return L;
}

/*Return the order (cardinal) of a group */

long group_order(GEN G)
{
  GEN ord=(GEN) G[2];
  long i;
  long card=1;
  for (i = 1; i < lg(ord); i++) 
    card *= ord[i];
  return card;
}

/* G being a subgroup of S_n, output n
 */
long group_domain(GEN G)
{
  if ( lg(G[1]) < 2 )
    err(talker,"empty group in group_domain");
  return lg(mael(G,1,1))-1;
}

/*Compute the left coset of g mod G: gG*/

GEN group_leftcoset(GEN G, GEN g)
{
  GEN res;
  long i,j,k;
  GEN gen=(GEN) G[1];
  GEN ord=(GEN) G[2];
  long card=group_order(G);
  res = cgetg(card + 1, t_VEC);
  res[1] = lcopy(g);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    int     c = k * (ord[i] - 1);
    for (j = 1; j <= c; j++)	/* I like it */
      res[++k] = (long) perm_mul((GEN) res[j], (GEN) gen[i]);
  }
  return res;
}

/*Compute the right coset of g mod G: Gg*/

GEN group_rightcoset(GEN G, GEN g)
{
  GEN res;
  long i,j,k;
  GEN gen=(GEN) G[1];
  GEN ord=(GEN) G[2];
  long card=group_order(G);
  res = cgetg(card + 1, t_VEC);
  res[1] = lcopy(g);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    int     c = k * (ord[i] - 1);
    for (j = 1; j <= c; j++)	/* I like it */
      res[++k] = (long) perm_mul((GEN) gen[i], (GEN) res[j]);
  }
  return res;
}

/*Compute the elements of a group from the generators*/
/*Not stack clean!*/

GEN group_elts(GEN G, long n)
{
  return group_leftcoset(G,perm_identity(n));
}

/*Return the cyclic group generated by g of order s*/

GEN cyclicgroup(GEN g, long s)
{
  GEN p2,p3,p4;
  p2 = cgetg(3, t_VEC);
  p3 = cgetg(2, t_VEC);
  p3[1] = lcopy(g);
  p4 = cgetg(2,t_VECSMALL);
  p4[1] = s;
  p2[1] = (long) p3;
  p2[2] = (long) p4;
  return p2;
}

/*Return the group generated by g1,g2 of rel orders s1,s2*/

GEN dicyclicgroup(GEN g1, GEN g2, long s1, long s2)
{
  GEN H = cgetg(3, t_VEC);
  GEN p3,p4;
  p3 = cgetg(3, t_VEC);
  p3[1] = lcopy((GEN)g1);
  p3[2] = lcopy((GEN)g2);
  p4 = cgetg(3,t_VECSMALL);
  p4[1] = s1;
  p4[2] = s2;
  H[1] = (long) p3;
  H[2] = (long) p4;
  return H;
}

/* return the quotient map G --> G/H */
/*The ouput is [gen,hash]*/
/* gen (vecvecsmall): coset generators
 * hash (vecvecsmall): sorted vecsmall of concat(perm,coset number)
 */
GEN group_quotient(GEN G, GEN H)
{
  pari_sp ltop=avma;
  GEN p1,p2,p3;
  long i,j,k;
  long a=1;
  long n=group_domain(G);
  long o=group_order(H);
  GEN elt = vecvecsmall_sort(group_elts(G,n));
  GEN used = bitvec_alloc(lg(elt));
  long l = (lg(elt)-1)/o;
  p2 = cgetg(l+1, t_VEC);
  p3 = cgetg(lg(elt), t_VEC);
  for (i = 1, k = 1; i <= l; ++i)
  {
    GEN V;
    while(bitvec_test(used,a)) a++;
    V = group_leftcoset(H,(GEN)elt[a]);
    p2[i] = V[1];
    for(j=1;j<lg(V);j++) 
    {
      long b=vecvecsmall_search(elt,(GEN)V[j],0);
      bitvec_set(used,b);
    }
    for (j = 1; j <= o; j++)
      p3[k++] = (long) vecsmall_append((GEN) V[j],i);
  }
  setlg(p3,k);
  p1 = cgetg(3,t_VEC);
  p1[1] = lcopy(p2);
  p1[2]= (long) vecvecsmall_sort(p3);
  return gerepileupto(ltop,p1);
}

/*Find in which coset a perm lie.*/

long
cosets_perm_search(GEN C, GEN p)
{
  long n=gen_search((GEN) C[2],p,0,vecsmall_prefixcmp);
  if (!n)
    err(talker, "coset not found in cosets_perm_search");
  return mael3(C,2,n,lg(p));
}

/*Compute the image of a permutation by a quotient map.*/

GEN quotient_perm(GEN C, GEN p)
{
  GEN p3;
  long j;
  long l2 = lg(C[1]);
  p3 = cgetg(l2, t_VECSMALL);
  for (j = 1; j < l2; ++j)
    p3[j] = cosets_perm_search(C, perm_mul(p, gmael(C,1,j)));
  return p3;
}

/* H is a subgroup of G, C is the quotient map G --> G/H
 *
 * Lift a subgroup S of G/H to a subgroup of G containing H
 */

GEN quotient_subgroup_lift(GEN C, GEN H, GEN S)
{
  GEN p1,L;
  long l1=lg(H[1])-1;
  long l2=lg(S[1])-1;
  long j;
  p1 = cgetg(3, t_VEC);
  L = cgetg(l1+l2+1, t_VEC);
  for (j = 1; j <= l1; ++j)
    L[j] = mael(H,1,j);
  for (j = 1; j <= l2; ++j)
    L[l1+j] = (long) gmael(C,1,mael3(S,1,j,1));
  p1[1] = (long) L;
  p1[2] = (long) vecsmall_concat((GEN)H[2],(GEN)S[2]);
  return p1;
}

/* Let G a group and H a quotient map G --> G/H
 * Assume H is normal, return the group G/H.
 */

GEN quotient_group(GEN C, GEN G)
{
  pari_sp ltop=avma;
  GEN Qgen,Qord,Qelt;
  GEN Q;
  long i,j;
  long n=lg(C[1])-1;
  long l=lg(G[1]);
  Qord = cgetg(l, t_VECSMALL);
  Qgen = cgetg(l, t_VEC);
  Qelt = cgetg(2, t_VEC);
  Qelt[1] = (long) perm_identity(n);
  for (i = 1, j = 1; i < l; ++i)
  {
    Qgen[j] = (long) quotient_perm(C, gmael(G,1,i));
    Qord[j] = (long) perm_relorder((GEN) Qgen[j], vecvecsmall_sort(Qelt));
    if (Qord[j]!=1)
    {
      Qelt=perm_generate((GEN) Qgen[j], Qelt, Qord[j]);
      j++;
    }
  }
  setlg(Qgen,j); setlg(Qord,j);
  Q=cgetg(3,t_VEC);
  Q[1]=(long)Qgen;
  Q[2]=(long)Qord;
  return gerepilecopy(ltop,Q);
}

/* Test if g normalize N*/
long group_perm_normalize(GEN N, GEN g)
{
  pari_sp ltop=avma;
  long l1 = gegal(vecvecsmall_sort(group_leftcoset(N, g)),
                  vecvecsmall_sort(group_rightcoset(N, g)));
  avma=ltop;
  return l1;
}

/* L is a list of subgroups, C is a coset and r a rel. order.*/
static
GEN liftlistsubgroups(GEN L, GEN C, long r)
{
  pari_sp ltop=avma;
  GEN p4;
  long i, k;
  long c=lg(C)-1;
  long l=lg(L)-1;
  long n=lg(C[1])-1;
  if ( !l )
    return cgetg(1,t_VEC);
  p4 = cgetg(l*c+1, t_VEC);
  for (i = 1, k = 1; i <= l; ++i)
  {
    long j;
    GEN S = (GEN) L[i];
    GEN Selt = vecvecsmall_sort(group_elts(S,n));
    for (j = 1; j <= c; ++j)
      if ((perm_relorder((GEN) C[j], Selt) == r) && group_perm_normalize(S, (GEN) C[j]))
      {
        GEN p7 = cgetg(3, t_VEC);
        p7[1] = (long) vecsmall_append((GEN) S[1], C[j]);
        p7[2] = (long) vecsmall_append((GEN) S[2], r);
        p4[k++] = (long) p7;
      }
  }
  setlg(p4,k);
  return gerepilecopy(ltop,p4);
}

/* H is a normal subgroup, C is the quotient map G -->G/H,
 * S is a subgroup of G/H, and G is embedded in Sym(l)
 * Return all the subgroups K of G such that
 * S= K mod H and K inter H={1}.
 */
static GEN liftsubgroup(GEN C, GEN H, GEN S)
{
  pari_sp ltop=avma;
  GEN V = trivialsubgroups();
  long n = lg(S[1]);
  long i;
  /*Loop over generators of S*/
  for (i = 1; i < n; ++i)
  {
    GEN W = group_leftcoset(H, gmael(C, 1, mael3(S, 1, i, 1)));
    V = liftlistsubgroups(V, W, mael(S, 2, i));
  }
  return gerepilecopy(ltop,V);
}
/* 1:A4 2:S4 0: other */
long
group_isA4S4(GEN G)
{
  GEN ord=(GEN)G[2];
  long n = lg(ord);
  if (n!=4 && n!=5) return 0;
  if (ord[1]!=2 || ord[2]!=2 || ord[3]!=3)
    return 0;
  if (n==4) return 1;
  if (ord[4]==2) return 2;
  return 0;
}
/* compute all the subgroups of a group G
 */
GEN group_subgroups(GEN G) 
{
  pari_sp ltop=avma;
  GEN p1;
  GEN C,Q,M;
  long lM;
  GEN sg1,sg2,sg3;
  long i, j;
  GEN gen=(GEN)G[1], ord=(GEN)G[2];
  GEN H;
  long l, n = lg(gen);
  if (n == 1)
    return trivialsubgroups();
  l = lg(gen[1]);/*now lg(gen)>1*/
  if (group_isA4S4(G))
  {
    GEN u=perm_mul((GEN) gen[1],(GEN) gen[2]);
    H = dicyclicgroup((GEN) gen[1],(GEN) gen[2],2,2);
  /* sg3 is the list of subgroups intersecting only partially with H*/
    sg3 = cgetg((n==4)?4:10, t_VEC);
    sg3[1] = (long) cyclicgroup((GEN) gen[1], 2);
    sg3[2] = (long) cyclicgroup((GEN) gen[2], 2);
    sg3[3] = (long) cyclicgroup(u, 2);
    if (n==5)
    {
      GEN s=(GEN) gen[1];
      GEN t=(GEN) gen[2];
      GEN u=(GEN) gen[3],u2=perm_mul(u,u);
      GEN v=(GEN) gen[4];
      GEN st=perm_mul(s,t);
      GEN w=perm_mul(perm_mul(u2,perm_mul(s,v)),u2);
      sg3[4] = (long) dicyclicgroup(s,v,2,2);
      sg3[5] = (long) dicyclicgroup(t,perm_mul(u,perm_mul(v,u2)),2,2);
      sg3[6] = (long) dicyclicgroup(st,perm_mul(u2,perm_mul(v,u)),2,2);
      sg3[7] = (long) dicyclicgroup(s,w,2,2);
      sg3[8] = (long) dicyclicgroup(t,perm_mul(u,perm_mul(w,u2)),2,2);
      sg3[9] = (long) dicyclicgroup(st,perm_mul(u2,perm_mul(w,u)),2,2);
    }
  }
  else
  {
    long osig = itos((GEN) coeff(decomp(stoi(ord[1])), 1, 1));
    GEN sig = perm_pow((GEN) gen[1], ord[1]/osig);
    H = cyclicgroup(sig,osig);
    sg3=NULL;
  }
  C = group_quotient(G,H);
  Q = quotient_group(C,G);
  M = group_subgroups(Q);
  lM = lg(M);
  /* sg1 is the list of subgroups containing H*/
  sg1 = cgetg(lM, t_VEC);
  for (i = 1; i < lM; ++i)
    sg1[i] = (long) quotient_subgroup_lift(C,H,(GEN)M[i]);
  /*sg2 is a list of lists of subgroups not intersecting with H*/
  sg2 = cgetg(lM, t_VEC);
  /* Loop over all subgroups of G/H */
  for (j = 1; j < lM; ++j)
    sg2[j] = (long) liftsubgroup(C, H, (GEN) M[j]);
  p1 = concat(sg1, concat(sg2, NULL));
  if (sg3)
    p1 = concat(p1, sg3);
  return gerepileupto(ltop,p1);
}

/*return 1 if G is abelian, else 0*/
long 
group_isabelian(GEN G)
{
  pari_sp ltop=avma;
  long i,j;
  for(i=2;i<lg(G[1]);i++)
    for(j=1;j<i;j++)
    {
      long test=gegal(perm_mul(gmael(G,1,i),gmael(G,1,j)),
	  perm_mul(gmael(G,1,j),gmael(G,1,i)));
      avma=ltop;
      if (!test) return 0;
    }
  return 1;  
}

/*If G is abelian, return its HNF matrix*/

GEN group_abelianHNF(GEN G, GEN S)
{
  long i, j;
  long n=lg(G[1]);
  GEN M;
  if (!group_isabelian(G)) return NULL;
  if (!S)
    S=group_elts(G,group_domain(G));
  M=cgetg(n,t_MAT);
  for(i=1;i<n;i++)
  {
    pari_sp btop;
    GEN P;
    long k;
    M[i]=lgetg(n,t_COL);
    btop=avma;
    P=perm_pow(gmael(G,1,i),mael(G,2,i));
    for(j=1;j<lg(S);j++)
      if (gegal(P,(GEN) S[j]))
	  break;
    avma=btop;
    if (j==lg(S)) err(talker,"wrong argument in galoisisabelian");
    j--;
    for(k=1;k<i;k++)
    {
      mael(M,i,k)=lstoi(j%mael(G,2,k));
      j/=mael(G,2,k);
    }  
    mael(M,i,k++)=lstoi(mael(G,2,i));
    for(  ;k<n;k++)
      mael(M,i,k)=zero;
  }
  return M;
}

/*If G is abelian, return its abstract SNF matrix*/

GEN group_abelianSNF(GEN G, GEN L)
{
  pari_sp ltop=avma;
  GEN S,H=group_abelianHNF(G,L);
  if (!H) return NULL;
  S=smithclean(smith(H));
  return gerepileupto(ltop,S);
}

GEN
abelian_group(GEN v)
{
  GEN G=cgetg(3,t_VEC);
  long card;
  long i;
  long d=1;
  G[1]=lgetg(lg(v),t_VEC);
  G[2]=lcopy(v);
  card=group_order(G);
  for(i=1;i<lg(v);i++)
  {
    GEN p=cgetg(1+card,t_VECSMALL);
    long o=v[i],u=d*(o-1);
    long j,k,l;
    mael(G,1,i) = (long) p;
    /*The following loop is a bit over-optimised. Oh well.
     *Remember that I wrote the loop in testpermutation. 
     *Something have survived... BA*/
    for(j=1;j<=card;)
    {
      for(k=1;k<o;k++)
        for(l=1;l<=d;l++,j++)
          p[j]=j+d;
      for(l=1;l<=d;l++,j++)
        p[j]=j-u;
    }
    d+=u;
  }
  return G;
}


 
GEN 
group_export_GAP(GEN G)
{
  pari_sp ltop=avma;
  GEN s;
  long i;
  long l = lg(G[1]);
  if (l == 1)
    return STRtoGENstr("Group(())");
  s = STRtoGENstr("Group(");
  for (i = 1; i < l; ++i)
  {
    if (i > 1)
      s = concat(s, STRtoGENstr(", "));
    s = concat(s, perm_to_GAP(gmael(G,1,i)));
  }
  s = concat(s, STRtoGENstr(")"));
  return gerepileupto(ltop,s);
}  

GEN 
group_export_MAGMA(GEN G)
{
  pari_sp ltop=avma;
  GEN s;
  long i;
  long l = lg(G[1]);
  if (l == 1)
    return STRtoGENstr("PermutationGroup<1|>");
  s = STRtoGENstr("PermutationGroup<");
  s = concat(s,stoi(group_domain(G)));
  s = concat(s,STRtoGENstr("|"));
  for (i = 1; i < l; ++i)
  {
    if (i > 1)
      s = concat(s, STRtoGENstr(", "));
    s = concat(s, small_to_vec(gmael(G,1,i)));
  }
  s = concat(s, STRtoGENstr(">"));
  return gerepileupto(ltop,s);
}  

GEN 
group_export(GEN G, long format)
{
  switch(format)
  {
  case 0:
    return group_export_GAP(G);
  case 1:
    return group_export_MAGMA(G);
  }
  err(flagerr,"galoisexport");
  return NULL; /*-Wall*/
}

