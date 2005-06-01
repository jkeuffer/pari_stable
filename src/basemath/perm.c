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
#include "paripriv.h"
/*************************************************************************/
/**                                                                     **/
/**                   Routines for handling VECSMALL                    **/
/**                                                                     **/
/*************************************************************************/

GEN
vec_to_vecsmall(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = itos((GEN)z[i]);
  return x;
}

GEN
vecsmall_to_vec(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_VEC);
  for (i=1; i<l; i++) x[i] = lstoi(z[i]);
  return x;
}

GEN
vecsmall_to_col(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_COL);
  for (i=1; i<l; i++) x[i] = lstoi(z[i]);
  return x;
}

GEN
vecsmall_copy(GEN x)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  if (typ(x)!=t_VECSMALL) err(typeer,"vecsmall_copy");
  for (i=1; i<l; i++) z[i] = x[i];
  return z;
}

GEN
vecsmall_const(long n, long c)
{
  long i;
  GEN V = cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) V[i] = c;
  return V;
}

GEN
vecsmall_shorten(GEN v, long n)
{
  long i;
  GEN V = cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) V[i] = v[i];
  return V;
 
}

/*in place sort.*/
void
vecsmall_sort(GEN V)
{
  long i,j,k,l,m;
  for(l=1; l<lg(V); l<<=1)
    for(j=1; (j>>1)<lg(V); j += l<<1)
      for(k=j+l, i=j; i<k && k<j+(l<<1) && k<lg(V); )
	if (V[i] > V[k])
	{
	  long z=V[k];
	  for (m=k;m>i;m--) V[m] = V[m-1];
	  V[i] = z; k++;
	}
	else
	  i++;
}

/* assume V sorted */
GEN
vecsmall_uniq(GEN V)
{
  GEN W;
  long i,j, l = lg(V);
  if (l == 1) return vecsmall_copy(V);
  W = cgetg(l,t_VECSMALL);
  W[1] = V[1];
  for(i=j=2; i<l; i++)
    if (V[i] != W[j-1]) W[j++] = V[i];
  setlg(W, j);
  stackdummy(W + j, l - j);
  return W;
}

int
vecsmall_lexcmp(GEN x, GEN y)
{
  long lx,ly,l,i;
  lx = lg(x);
  ly = lg(y); l = min(lx,ly);
  for (i=1; i<l; i++)
    if (x[i] != y[i]) return x[i]<y[i]? -1: 1;
  if (lx == ly) return 0;
  return (lx < ly)? -1 : 1;
}

int
vecsmall_prefixcmp(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y), l = min(lx,ly);
  for (i=1; i<l; i++)
    if (x[i] != y[i]) return x[i]<y[i]? -1: 1;
  return 0;
}

/*Can be used on t_VEC, but coeffs not gcopy-ed*/
GEN
vecsmall_prepend(GEN V, long s)
{
  long i, l2 = lg(V);
  GEN res = cgetg(l2+1, typ(V));
  res[1] = s;
  for (i = 2; i <= l2; ++i) res[i] = V[i - 1];
  return res;
}

/*Can be used on t_VEC, but coeffs not gcopy-ed*/
GEN
vecsmall_append(GEN V, long s)
{
  long i, l2 = lg(V);
  GEN res = cgetg(l2+1, typ(V));
  for (i = 1; i < l2; ++i) res[i] = V[i];
  res[l2] = s; return res;
}

GEN
vecsmall_concat(GEN u, GEN v)
{
  long i, l1 = lg(u)-1, l2 = lg(v)-1;
  GEN res = cgetg(l1+l2+1, t_VECSMALL);
  for (i = 1; i <= l1; ++i) res[i]    = u[i];
  for (i = 1; i <= l2; ++i) res[i+l1] = v[i];
  return res;
}

/* return the number of indices where u and v are equal */
long
vecsmall_coincidence(GEN u, GEN v)
{
  long i, s = 0, l = min(lg(u),lg(v));
  for(i=1; i<l; i++)
    if(u[i] == v[i]) s++;
  return s;
}

/* returns the first index i<=n such that x=v[i] if it exits, 0 otherwise */
long
vecsmall_isin(GEN v, long x)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
    if (v[i] == x) return i;
  return 0;
}


long
vecsmall_pack(GEN V, long base, long mod)
{
  long i, s = 0;
  for(i=1; i<lg(V); i++) s = (base*s + V[i]) % mod;
  return s;
}

/*************************************************************************/
/**                                                                     **/
/**               Routines for handling bit vector                      **/
/**                                                                     **/
/*************************************************************************/

GEN
bitvec_alloc(long n)
{
  long l = 1 + (n>>TWOPOTBITS_IN_LONG);
  return vecsmall_const(l,0);
}


GEN
bitvec_shorten(GEN bitvec, long n)
{
  long l = 1 + (n>>TWOPOTBITS_IN_LONG);
  return vecsmall_shorten(bitvec,l);
}

long
bitvec_test(GEN bitvec, long b)
{
  long q = b>>TWOPOTBITS_IN_LONG;
  long r = b&(BITS_IN_LONG-1);
  return (bitvec[1+q]>>r) & 1L;
}

void
bitvec_set(GEN bitvec, long b)
{
  long q = b>>TWOPOTBITS_IN_LONG;
  long r = b&(BITS_IN_LONG-1);
  bitvec[1+q] |= 1L<<r;
}

void
bitvec_clear(GEN bitvec, long b)
{
  long q = b>>TWOPOTBITS_IN_LONG;
  long r = b&(BITS_IN_LONG-1);
  bitvec[1+q] &= ~(1L<<r);
}

/*************************************************************************/
/**                                                                     **/
/**             Routines for handling vectors of VECSMALL               **/
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
  return gen_sort(x, cmp_IND | cmp_C, vecsmall_lexcmp);
}

long
vecvecsmall_search(GEN x, GEN y, long flag)
{
  return gen_search(x,y,flag,vecsmall_prefixcmp);
}

/*************************************************************************/
/**                                                                     **/
/**                  Routines for handling permutations                 **/
/**                                                                     **/
/*************************************************************************/

/* Permutations may be given by
 * perm (VECSMALL): a bijection from 1...n to 1...n i-->perm[i]
 * cyc (VEC of VECSMALL): a product of disjoint cycles. */

/* Identity permutation. Not a good name : l is not a perm */
GEN
perm_identity(long l)
{
  GEN perm = cgetg(l + 1, t_VECSMALL);
  int i;
  for (i = 1; i <= l; i++) perm[i] = i;
  return perm;
} 

GEN
cyclicperm(long l, long d)
{
  GEN perm = cgetg(l + 1, t_VECSMALL);
  int i;
  for (i = 1;     i <= l-d; i++) perm[i] = i+d;
  for (i = l-d+1; i <= l; i++)   perm[i] = i-l+d;
  return perm;
}

/* Multiply (compose) two permutations.
 * Can be used if s is a t_VEC but no copy */
GEN
perm_mul(GEN s, GEN t)
{
  GEN u;
  int i, l = lg(s);
  if (l < lg(t))
    err(talker, "First permutation shorter than second in perm_mul");
  u = cgetg(l, typ(s));
  for (i = 1; i < l; i++) u[i] = s[ t[i] ];
  return u;
}

/* Multiply (compose) two permutations, putting the result in the second one. */
static GEN
perm_mul_inplace(GEN s, GEN t)
{
  int i;
  for (i = 1; i < lg(s); i++) t[i] = s[t[i]];
  return t;
}
/* Compute the inverse (reciprocal) of a permutation. */
GEN
perm_inv(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_VECSMALL);
  for (i=1; i<lx; i++) y[ x[i] ] = i;
  return y;
}

/* Return s*t*s^-1 */
GEN 
perm_conj(GEN s, GEN t)
{
  long i, l = lg(s);
  GEN v = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) v[ s[i] ] = s[ t[i] ];
  return v;
}

/* Orbits of the subgroup generated by v on {1,..,n} */
static GEN
vecperm_orbits_i(GEN v, long n)
{
  int j, k, l, m, o, p, flag;
  GEN bit, cycle, cy;
  long mj = 1;
  cycle = cgetg(n+1, t_VEC);
  bit = bitvec_alloc(n);
  for (k = 1, l = 1; k <= n;)
  {
    for (  ; bitvec_test(bit,mj); mj++) /*empty*/;
    cy = cgetg(n+1, t_VECSMALL);
    m = 1;
    k++;
    cy[m++] = mj;
    bitvec_set(bit, mj++);
    do
    {
      flag = 0;
      for (o = 1; o < lg(v); o++)
	for (p = 1; p < m; p++)	/* m increases! */
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
    while (flag);
    setlg(cy, m);
    cycle[l++] = (long)cy;
  }
  setlg(cycle, l); return cycle;
}
/* memory clean version */
GEN
vecperm_orbits(GEN v, long n)
{
  pari_sp av = avma;
  return gerepilecopy(av, vecperm_orbits_i(v, n));
}

/* Compute the cyclic decomposition of a permutation */
GEN
perm_cycles(GEN v)
{
  pari_sp av = avma;
  return gerepilecopy(av, vecperm_orbits_i(mkvec(v), lg(v)-1));
}

/* Output the order of p */
long
perm_order(GEN v)
{
  pari_sp ltop = avma;
  GEN c;
  long i, d;
  c = vecperm_orbits_i(mkvec(v), lg(v)-1);
  for(i=1, d=1; i<lg(c); i++) d = clcm(d, lg(c[i])-1);
  avma = ltop; return d;
}

GEN
cyc_pow(GEN cyc, long exp)
{
  long i, j, k, l, r;
  GEN c;
  for (r = j = 1; j < lg(cyc); j++)
  {
    int n = lg(cyc[j]) - 1;
    r += cgcd(n, exp);
  }
  c = cgetg(r, t_VEC);
  for (r = j = 1; j < lg(cyc); j++)
  {
    GEN v = (GEN)cyc[j];
    long n = lg(v) - 1, e = smodss(exp,n), g = cgcd(n, e), m = n / g;
    for (i = 0; i < g; i++)
    {
      GEN p = cgetg(m+1, t_VECSMALL);
      c[r++]  = (long)p;
      for (k = 1, l = i; k <= m; k++)
      {
        p[k] = v[l+1];
        l += e; if (l >= n) l -= n;
      }
    }
  }
  return c;
}

/* Compute the power of a permutation given by product of cycles
 * Ouput a perm, not a cyc */
GEN
cyc_pow_perm(GEN cyc, long exp)
{
  long e, j, k, l, n;
  GEN p;
  for (n = 0, j = 1; j < lg(cyc); j++) n += lg(cyc[j])-1;
  p = cgetg(n + 1, t_VECSMALL);
  for (j = 1; j < lg(cyc); j++)
  {
    GEN v = (GEN)cyc[j];
    n = lg(v) - 1; e = smodss(exp, n);
    for (k = 1, l = e; k <= n; k++)
    {
      p[v[k]] = v[l+1];
      if (++l == n) l = 0;
    }
  }
  return p;
}

/* Compute the power of a permutation.
 * TODO: make it more clever for small exp */
GEN
perm_pow(GEN perm, long exp)
{
  return cyc_pow_perm(perm_cycles(perm), exp);
}

GEN 
perm_to_GAP(GEN p)
{
  pari_sp ltop=avma;
  GEN gap;
  GEN x;
  long i;
  long nb, c=0;
  char *s;
  long sz;
  long lp=lg(p)-1;
  if (typ(p) != t_VECSMALL)  err(typeer, "perm_to_GAP");
  x = perm_cycles(p);
  sz = (long) ((bfffo(lp)+1) * L2SL10 + 1);
  /*Dry run*/
  for (i = 1, nb = 1; i < lg(x); ++i)
  {
    GEN z = (GEN)x[i];
    long lz = lg(z)-1;
    nb += 1+lz*(sz+2);
  }
  nb++;
  /*Real run*/
  gap = cgetg(nchar2nlong(nb) + 1, t_STR);
  s = GSTR(gap);
  for (i = 1; i < lg(x); ++i)
  {
    long j;
    GEN z = (GEN)x[i];
    if (lg(z) > 2)
    {
      s[c++] = '(';
      for (j = 1; j < lg(z); ++j)
      {
        if (j > 1)
        {
          s[c++] = ','; s[c++] = ' ';
        }
        sprintf(s+c,"%ld",z[j]);
        while(s[c++]) /* empty */;
        c--;
      }
      s[c++] = ')';
    }
  }
  if (!c) { s[c++]='('; s[c++]=')'; }
  s[c++] = 0;
  return gerepileupto(ltop,gap);
}

int
perm_commute(GEN p, GEN q)
{
  pari_sp ltop = avma;
  int r = gequal(perm_mul(p,q), perm_mul(q,p));
  avma = ltop; return r;
}

/*************************************************************************/
/**                                                                     **/
/**                  Routines for handling groups                       **/
/**                                                                     **/
/*************************************************************************/

/* Groups are vectors [gen,orders]
 * gen (vecvecsmall): list of generators given by permutations 
 * orders (vecsmall): relatives orders of generators. */

static GEN
trivialsubgroups(void)
{
  GEN p2 = cgetg(2, t_VEC);
  p2[1] = (long)mkvec2(cgetg(1,t_VEC), cgetg(1,t_VECSMALL));
  return p2;
}

/* Compute the orders of p modulo the group S given by a set */
long
perm_relorder(GEN p, GEN S)
{
  pari_sp ltop = avma;
  long n = 1;
  GEN  q = p;
  while (!vecvecsmall_search(S, q, 0)) { q = perm_mul(q, p); n++; }
  avma = ltop; return n;
}

GEN
perm_generate(GEN S, GEN H, long o)
{
  long i, k, n = lg(H)-1;
  GEN L = cgetg(1+n*o, t_VEC);
  for(i=1; i<=n; i++)
    L[i] = (long)vecsmall_copy((GEN)H[i]);
  for(k=n+1; k <= n*o; ++k)
    L[k] = (long)perm_mul((GEN)L[k-n], S);
  return L;
}

/*Return the order (cardinal) of a group */
long
group_order(GEN G)
{
  GEN ord = (GEN)G[2];
  long i, card = 1;
  for (i = 1; i < lg(ord); i++) card *= ord[i];
  return card;
}

/* G being a subgroup of S_n, output n */
long
group_domain(GEN G)
{
  if (lg(G[1]) < 2) err(talker,"empty group in group_domain");
  return lg(mael(G,1,1)) - 1;
}

/*Compute the left coset of g mod G: gG*/
GEN
group_leftcoset(GEN G, GEN g)
{
  GEN res;
  long i, j, k;
  GEN gen = (GEN)G[1];
  GEN ord = (GEN)G[2];
  res = cgetg(group_order(G)+1, t_VEC);
  res[1] = (long)vecsmall_copy(g);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    int c = k * (ord[i] - 1);
    for (j = 1; j <= c; j++)
      res[++k] = (long)perm_mul((GEN)res[j], (GEN)gen[i]);
  }
  return res;
}

/*Compute the right coset of g mod G: Gg*/
GEN
group_rightcoset(GEN G, GEN g)
{
  GEN res;
  long i, j, k;
  GEN gen = (GEN) G[1];
  GEN ord = (GEN) G[2];
  res = cgetg(group_order(G)+1, t_VEC);
  res[1] = (long) vecsmall_copy(g);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    int c = k * (ord[i] - 1);
    for (j = 1; j <= c; j++)
      res[++k] = (long)perm_mul((GEN)gen[i], (GEN)res[j]);
  }
  return res;
}

/*Compute the elements of a group from the generators*/
/*Not stack clean!*/
GEN
group_elts(GEN G, long n)
{
  return group_leftcoset(G, perm_identity(n));
}

/*Cyclic group generated by g of order s*/
GEN
cyclicgroup(GEN g, long s)
{
  GEN p2 = cgetg(3, t_VEC);
  p2[1] = (long)mkvec( vecsmall_copy(g) );
  p2[2] = (long)mkvecsmall(s); return p2;
}

/*Return the group generated by g1,g2 of rel orders s1,s2*/

GEN
dicyclicgroup(GEN g1, GEN g2, long s1, long s2)
{
  GEN H = cgetg(3, t_VEC);
  GEN p3,p4;
  p3 = cgetg(3, t_VEC);
  p3[1] = (long) vecsmall_copy((GEN)g1);
  p3[2] = (long) vecsmall_copy((GEN)g2);
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
 * hash (vecvecsmall): sorted vecsmall of concat(perm,coset number) */
GEN
group_quotient(GEN G, GEN H)
{
  pari_sp ltop = avma;
  GEN p1, p2, p3;
  long i, j, k, a = 1;
  long n = group_domain(G), o = group_order(H);
  GEN elt = vecvecsmall_sort(group_elts(G,n));
  long le = lg(elt)-1;
  GEN used = bitvec_alloc(le+1);
  long l = le/o;
  p2 = cgetg(l+1, t_VEC);
  p3 = cgetg(le+1, t_VEC);
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
  p1 = cgetg(3,t_VEC);
  p1[1] = lcopy(p2);
  p1[2] = (long) vecvecsmall_sort(p3);
  return gerepileupto(ltop,p1);
}

/*Find in which coset a perm lie.*/
long
cosets_perm_search(GEN C, GEN p)
{
  long n = gen_search((GEN) C[2],p,0,vecsmall_prefixcmp);
  if (!n) err(talker, "coset not found in cosets_perm_search");
  return mael3(C,2,n,lg(p));
}

/*Compute the image of a permutation by a quotient map.*/
GEN
quotient_perm(GEN C, GEN p)
{
  long j, l2 = lg(C[1]);
  GEN p3 = cgetg(l2, t_VECSMALL);
  for (j = 1; j < l2; ++j)
    p3[j] = cosets_perm_search(C, perm_mul(p, gmael(C,1,j)));
  return p3;
}

/* H is a subgroup of G, C is the quotient map G --> G/H
 *
 * Lift a subgroup S of G/H to a subgroup of G containing H */
GEN
quotient_subgroup_lift(GEN C, GEN H, GEN S)
{
  long l1 = lg(H[1])-1;
  long l2 = lg(S[1])-1, j;
  GEN p1 = cgetg(3, t_VEC), L = cgetg(l1+l2+1, t_VEC);
  for (j = 1; j <= l1; ++j) L[j] = mael(H,1,j);
  for (j = 1; j <= l2; ++j) L[l1+j] = mael(C,1,mael3(S,1,j,1));
  p1[1] = (long)L;
  p1[2] = (long)vecsmall_concat((GEN)H[2],(GEN)S[2]);
  return p1;
}

/* Let G a group and H a quotient map G --> G/H
 * Assume H is normal, return the group G/H */
GEN
quotient_group(GEN C, GEN G)
{
  pari_sp ltop = avma;
  GEN Qgen, Qord, Qelt, Q;
  long i,j, n = lg(C[1])-1, l = lg(G[1]);
  Qord = cgetg(l, t_VECSMALL);
  Qgen = cgetg(l, t_VEC);
  Qelt = mkvec(perm_identity(n));
  for (i = 1, j = 1; i < l; ++i)
  {
    Qgen[j] = (long)quotient_perm(C, gmael(G,1,i));
    Qord[j] = (long)perm_relorder((GEN)Qgen[j], vecvecsmall_sort(Qelt));
    if (Qord[j] != 1)
    {
      Qelt = perm_generate((GEN)Qgen[j], Qelt, Qord[j]);
      j++;
    }
  }
  setlg(Qgen,j);
  setlg(Qord,j); Q = mkvec2(Qgen, Qord);
  if (group_order(Q) != n) err(talker,"galoissubgroup: not a WSS group");
  return gerepilecopy(ltop,Q);
}

/* Test if g normalize N*/
long
group_perm_normalize(GEN N, GEN g)
{
  pari_sp ltop = avma;
  long r = gequal(vecvecsmall_sort(group_leftcoset(N, g)),
                vecvecsmall_sort(group_rightcoset(N, g)));
  avma = ltop; return r;
}

/* L is a list of subgroups, C is a coset and r a rel. order.*/
static GEN
liftlistsubgroups(GEN L, GEN C, long r)
{
  pari_sp ltop = avma;
  GEN R;
  long c = lg(C)-1;
  long l = lg(L)-1, n = lg(C[1])-1, i, k;
  if ( !l )
    return cgetg(1,t_VEC);
  R = cgetg(l*c+1, t_VEC);
  for (i = 1, k = 1; i <= l; ++i)
  {
    GEN S = (GEN) L[i], Selt = vecvecsmall_sort(group_elts(S,n));
    long j;
    for (j = 1; j <= c; ++j)
      if ((perm_relorder((GEN) C[j], Selt) == r)
        && group_perm_normalize(S, (GEN) C[j]))
      {
        GEN g = cgetg(3, t_VEC);
        g[1] = (long)vecsmall_append((GEN) S[1], C[j]);
        g[2] = (long)vecsmall_append((GEN) S[2], r);
        R[k++] = (long)g;
      }
  }
  setlg(R, k);
  return gerepilecopy(ltop, R);
}

/* H is a normal subgroup, C is the quotient map G -->G/H,
 * S is a subgroup of G/H, and G is embedded in Sym(l)
 * Return all the subgroups K of G such that
 * S= K mod H and K inter H={1} */
static GEN
liftsubgroup(GEN C, GEN H, GEN S)
{
  pari_sp ltop = avma;
  GEN V = trivialsubgroups();
  long n = lg(S[1]), i;
  for (i = 1; i < n; ++i)
  { /*loop over generators of S*/
    GEN W = group_leftcoset(H, gmael(C, 1, mael3(S, 1, i, 1)));
    V = liftlistsubgroups(V, W, mael(S, 2, i));
  }
  return gerepilecopy(ltop,V);
}

/* 1:A4 2:S4 0: other */
long
group_isA4S4(GEN G)
{
  GEN elt = (GEN)G[1];
  GEN ord = (GEN)G[2];
  long n = lg(ord);
  if (n != 4 && n != 5) return 0;
  if (ord[1]!=2 || ord[2]!=2 || ord[3]!=3) return 0;
  if (perm_commute((GEN)elt[1],(GEN)elt[3])) return 0;
  if (n==4) return 1;
  if (ord[4]!=2) return 0;
  if (perm_commute((GEN)elt[3],(GEN)elt[4])) return 0;
  return 2;
}
/* compute all the subgroups of a group G */
GEN
group_subgroups(GEN G) 
{
  pari_sp ltop = avma;
  GEN p1, H, C, Q, M, sg1, sg2, sg3, gen = (GEN)G[1], ord = (GEN)G[2];
  long lM, i, j, n = lg(gen);
  if (n == 1) return trivialsubgroups();
  if (group_isA4S4(G))
  {
    GEN u = perm_mul((GEN) gen[1],(GEN) gen[2]);
    H = dicyclicgroup((GEN) gen[1],(GEN) gen[2],2,2);
    /* sg3 is the list of subgroups intersecting only partially with H*/
    sg3 = cgetg((n==4)?4: 10, t_VEC);
    sg3[1] = (long)cyclicgroup((GEN)gen[1], 2);
    sg3[2] = (long)cyclicgroup((GEN)gen[2], 2);
    sg3[3] = (long)cyclicgroup(u, 2);
    if (n==5)
    {
      GEN s = (GEN)gen[1]; /*s=(1,2)(3,4)*/
      GEN t = (GEN)gen[2]; /*t=(1,3)(2,4)*/
      GEN u = (GEN)gen[3];
      GEN v = (GEN)gen[4], st = perm_mul(s,t), w, u2;
      if (gequal(perm_conj(u,s), t)) /*u=(2,3,4)*/
        u2 = perm_mul(u,u); 
      else 
      { 
        u2 = u; 
        u = perm_mul(u,u); 
      }
      if (perm_order(v)==2)
      {
        if (!perm_commute(s,v)) /*v=(1,2)*/
        { 
          v = perm_conj(u,v);
          if (!perm_commute(s,v)) v = perm_conj(u,v);
        }
        w = perm_mul(v,t); /*w=(1,4,2,3)*/
      }
      else
      {
        w = v;
        if (!gequal(perm_mul(w,w), s)) /*w=(1,4,2,3)*/
        {
          w = perm_conj(u,w);
          if (!gequal(perm_mul(w,w), s)) w = perm_conj(u,w);
        }
        v = perm_mul(w,t); /*v=(1,2)*/
      }
      sg3[4] = (long)dicyclicgroup(s,v,2,2);
      sg3[5] = (long)dicyclicgroup(t,perm_conj(u,v),2,2);
      sg3[6] = (long)dicyclicgroup(st,perm_conj(u2,v),2,2);
      sg3[7] = (long)dicyclicgroup(s,w,2,2);
      sg3[8] = (long)dicyclicgroup(t,perm_conj(u,w),2,2);
      sg3[9] = (long)dicyclicgroup(st,perm_conj(u2,w),2,2);
    }
  }
  else
  {
    long osig = mael(factoru(ord[1]), 1, 1);
    GEN sig = perm_pow((GEN)gen[1], ord[1]/osig);
    H = cyclicgroup(sig,osig);
    sg3 = NULL;
  }
  C = group_quotient(G,H);
  Q = quotient_group(C,G);
  M = group_subgroups(Q);
  lM = lg(M);
  /* sg1 is the list of subgroups containing H*/
  sg1 = cgetg(lM, t_VEC);
  for (i = 1; i < lM; ++i)
    sg1[i] = (long)quotient_subgroup_lift(C,H,(GEN)M[i]);
  /*sg2 is a list of lists of subgroups not intersecting with H*/
  sg2 = cgetg(lM, t_VEC);
  /* Loop over all subgroups of G/H */
  for (j = 1; j < lM; ++j)
    sg2[j] = (long)liftsubgroup(C, H, (GEN) M[j]);
  p1 = concat(sg1, concat(sg2,NULL));
  if (sg3)
  {
    p1 = concat(p1, sg3);
    /*Fixup to avoid the D4 subgroups of S4 to be in non supersolvable format*/
    if (n==5)
      for(j = 3; j <= 5; j++)
      {
        GEN c = gmael(p1,j,1);
        if (!perm_commute((GEN)c[1],(GEN)c[3]))
        {
          if (perm_commute((GEN)c[2],(GEN)c[3])) { lswap(c[1], c[2]); }
          else
            perm_mul_inplace((GEN)c[2], (GEN)c[1]);
        }
      }
  }
  return gerepileupto(ltop,p1);
}

/*return 1 if G is abelian, else 0*/
long 
group_isabelian(GEN G)
{
  long i, j;
  GEN g = (GEN)G[1];
  for(i=2; i<lg(g); i++)
    for(j=1; j<i; j++)
      if (!perm_commute((GEN)g[i], (GEN)g[j])) return 0;
  return 1;  
}

/*If G is abelian, return its HNF matrix*/
GEN
group_abelianHNF(GEN G, GEN S)
{
  GEN M, g = (GEN)G[1], o = (GEN)G[2];
  long i, j, k, n = lg(g);
  if (!group_isabelian(G)) return NULL;
  if (n==1) return cgetg(1,t_MAT);
  if (!S) S = group_elts(G, group_domain(G));
  M = cgetg(n,t_MAT);
  for(i=1; i<n; i++)
  {
    GEN P, C = cgetg(n,t_COL);
    pari_sp av = avma;
    M[i] = (long)C;
    P = perm_pow((GEN)g[i], o[i]);
    for(j=1; j<lg(S); j++)
      if (gequal(P, (GEN)S[j])) break;
    avma = av;
    if (j==lg(S)) err(talker,"wrong argument in galoisisabelian");
    j--;
    for(k=1; k<i; k++)
    {
      long q = j / o[k];
      C[k] = lstoi(j - q*o[k]);
      j = q;
    }  
    C[k] = lstoi(o[i]);
    for (k++; k<n; k++) C[k] = (long)gen_0;
  }
  return M;
}

/*If G is abelian, return its abstract SNF matrix*/
GEN
group_abelianSNF(GEN G, GEN L)
{
  pari_sp ltop = avma;
  GEN H = group_abelianHNF(G,L);
  if (!H) return NULL;
  return gerepileupto(ltop, smithclean( smith(H) ));
}

GEN
abelian_group(GEN v)
{
  GEN G = cgetg(3,t_VEC);
  long card, i, d = 1;
  G[1] = lgetg(lg(v),t_VEC);
  G[2] = (long)vecsmall_copy(v);
  card = group_order(G);
  for(i=1; i<lg(v); i++)
  {
    GEN p = cgetg(card+1, t_VECSMALL);
    long o = v[i], u = d*(o-1), j, k, l;
    mael(G,1,i) = (long)p;
    /* The following loop is over-optimized. Remember that I wrote it for
     * testpermutation. Something has survived... BA */
    for(j=1;j<=card;)
    {
      for(k=1;k<o;k++)
        for(l=1;l<=d; l++,j++) p[j] = j+d;
      for (l=1; l<=d; l++,j++) p[j] = j-u;
    }
    d += u;
  }
  return G;
}

GEN
groupelts_center(GEN S)
{
  pari_sp ltop = avma;
  long i, j, n = lg(S)-1, l = n;
  GEN V, elts = bitvec_alloc(n+1);
  for(i=1; i<=n; i++)
  {
    if (bitvec_test(elts,i)) { l--;  continue; }
    for(j=1; j<=n; j++)
      if (!perm_commute((GEN)S[i],(GEN)S[j]))
      {
        bitvec_set(elts,i);
        bitvec_set(elts,j); l--; break;
      }
  }
  V = cgetg(l+1,t_VEC);
  for (i=1, j=1; i<=n ;i++)
    if (!bitvec_test(elts,i)) V[j++] = (long)vecsmall_copy((GEN)S[i]);
  return gerepileupto(ltop,V);
}

GEN
groupelts_abelian_group(GEN S)
{
  pari_sp ltop = avma;
  GEN Qgen, Qord, Qelt;
  long i, j, n = lg(S[1])-1, l = lg(S);
  Qord = cgetg(l, t_VECSMALL);
  Qgen = cgetg(l, t_VEC);
  Qelt = mkvec(perm_identity(n));
  for (i = 1, j = 1; i < l; ++i)
  {
    Qgen[j] = (long)S[i];
    Qord[j] = (long)perm_relorder((GEN)Qgen[j], vecvecsmall_sort(Qelt));
    if (Qord[j] != 1)
    {
      Qelt = perm_generate((GEN)Qgen[j], Qelt, Qord[j]);
      j++;
    }
  }
  setlg(Qgen,j);
  setlg(Qord,j); 
  return gerepilecopy(ltop, mkvec2(Qgen, Qord));
}
 
GEN 
group_export_GAP(GEN G)
{
  pari_sp ltop = avma;
  GEN s, g = (GEN)G[1];
  long i, l = lg(g);
  if (l == 1) return strtoGENstr("Group(())");
  s = strtoGENstr("Group(");
  for (i = 1; i < l; ++i)
  {
    if (i > 1) s = dummyconcat(s, strtoGENstr(", "));
    s = dummyconcat(s, perm_to_GAP((GEN)g[i]));
  }
  s = concat(s, strtoGENstr(")"));
  return gerepileupto(ltop,s);
}  

GEN 
group_export_MAGMA(GEN G)
{
  pari_sp ltop=avma;
  GEN s, g = (GEN)G[1];
  long i, l = lg(g);
  if (l == 1) return strtoGENstr("PermutationGroup<1|>");
  s = strtoGENstr("PermutationGroup<");
  s = dummyconcat(s, stoi(group_domain(G)));
  s = dummyconcat(s, strtoGENstr("|"));
  for (i = 1; i < l; ++i)
  {
    if (i > 1) s = dummyconcat(s, strtoGENstr(", "));
    s = dummyconcat(s, vecsmall_to_vec((GEN)g[i]));
  }
  s = concat(s, strtoGENstr(">"));
  return gerepileupto(ltop,s);
}  

GEN 
group_export(GEN G, long format)
{
  switch(format)
  {
  case 0: return group_export_GAP(G);
  case 1: return group_export_MAGMA(G);
  }
  err(flagerr,"galoisexport");
  return NULL; /*-Wall*/
}
