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

#include "pari.h"
#include "paripriv.h"
/**************************************************************/
/**                                                          **/
/**                HERMITE NORMAL FORM REDUCTION             **/
/**                                                          **/
/**************************************************************/
GEN
mathnf0(GEN x, long flag)
{
  if (typ(x)!=t_MAT) pari_err(typeer,"mathnf0");
  RgM_check_ZM(x, "mathnf0");
  switch(flag)
  {
    case 0: return ZM_hnf(x);
    case 1: return hnfall(x);
    case 3: return hnfperm(x);
    case 4: return hnflll(x);
    default: pari_err(flagerr,"mathnf");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                SPECIAL HNF (FOR INTERNAL USE !!!)               */
/*                                                                 */
/*******************************************************************/
static int
count(GEN mat, long row, long len, long *firstnonzero)
{
  long j, n = 0;

  for (j=1; j<=len; j++)
  {
    long p = mael(mat,j,row);
    if (p)
    {
      if (labs(p)!=1) return -1;
      n++; *firstnonzero=j;
    }
  }
  return n;
}

static int
count2(GEN mat, long row, long len)
{
  long j;
  for (j=len; j; j--)
    if (labs(mael(mat,j,row)) == 1) return j;
  return 0;
}

static GEN
hnffinal(GEN matgen,GEN perm,GEN* ptdep,GEN* ptB,GEN* ptC)
{
  GEN p1,p2,U,H,Hnew,Bnew,Cnew,diagH1;
  GEN B = *ptB, C = *ptC, dep = *ptdep, depnew;
  pari_sp av, lim;
  long i,j,k,s,i1,j1,zc;
  long co = lg(C);
  long col = lg(matgen)-1;
  long lnz, nlze, lig;

  if (col == 0) return matgen;
  lnz = lg(matgen[1])-1; /* was called lnz-1 - nr in hnfspec */
  nlze = lg(dep[1])-1;
  lig = nlze + lnz;
  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnffinal:\n");
    if (DEBUGLEVEL>6)
    {
      if (nlze) fprintferr("dep = %Ps\n",dep);
      fprintferr("mit = %Ps\n",matgen);
      fprintferr("B = %Ps\n",B);
    }
  }
  /* H: lnz x lnz [disregarding initial 0 cols], U: col x col */
  H = ZM_hnflll(matgen, &U, 0);
  H += (lg(H)-1 - lnz); H[0] = evaltyp(t_MAT) | evallg(lnz+1);
  /* Only keep the part above the H (above the 0s is 0 since the dep rows
   * are dependent from the ones in matgen) */
  zc = col - lnz; /* # of 0 columns, correspond to units */
  if (nlze) { dep = ZM_mul(dep,U); dep += zc; }

  diagH1 = new_chunk(lnz+1); /* diagH1[i] = 0 iff H[i,i] != 1 (set later) */

  av = avma; lim = stack_lim(av,1);
  Cnew = cgetg(co, typ(C));
  setlg(C, col+1); p1 = gmul(C,U);
  for (j=1; j<=col; j++) Cnew[j] = p1[j];
  for (   ; j<co ; j++)  Cnew[j] = C[j];
  if (DEBUGLEVEL>5) fprintferr("    hnflll done\n");

  /* Clean up B using new H */
  for (s=0,i=lnz; i; i--)
  {
    GEN Di = gel(dep,i), Hi = gel(H,i);
    GEN h = gel(Hi,i); /* H[i,i] */
    if ( (diagH1[i] = is_pm1(h)) ) { h = NULL; s++; }
    for (j=col+1; j<co; j++)
    {
      GEN z = gel(B,j-col);
      p1 = gel(z,i+nlze);
      if (h) p1 = truedivii(p1,h);
      if (!signe(p1)) continue;
      for (k=1; k<=nlze; k++) gel(z,k) = subii(gel(z,k), mulii(p1, gel(Di,k)));
      for (   ; k<=lig;  k++) gel(z,k) = subii(gel(z,k), mulii(p1, gel(Hi,k-nlze)));
      gel(Cnew,j) = gsub(gel(Cnew,j), gmul(p1, gel(Cnew,i+zc)));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"hnffinal, i = %ld",i);
      gerepileall(av, 2, &Cnew, &B);
    }
  }
  p1 = cgetg(lnz+1,t_VEC); p2 = perm + nlze;
  for (i1=0, j1=lnz-s, i=1; i<=lnz; i++) /* push the 1 rows down */
    if (diagH1[i])
      p1[++j1] = p2[i];
    else
      p2[++i1] = p2[i];
  for (i=i1+1; i<=lnz; i++) p2[i] = p1[i];
  if (DEBUGLEVEL>5) fprintferr("    first pass in hnffinal done\n");

  /* s = # extra redundant generators taken from H
   *          zc  col-s  co   zc = col - lnz
   *       [ 0 |dep |     ]    i = lnze + lnz - s = lig - s
   *  nlze [--------|  B' ]
   *       [ 0 | H' |     ]    H' = H minus the s rows with a 1 on diagonal
   *     i [--------|-----] lig-s           (= "1-rows")
   *       [   0    | Id  ]
   *       [        |     ] li */
  lig -= s; col -= s; lnz -= s;
  Hnew = cgetg(lnz+1,t_MAT);
  depnew = cgetg(lnz+1,t_MAT); /* only used if nlze > 0 */
  Bnew = cgetg(co-col,t_MAT);
  C = shallowcopy(Cnew);
  for (j=1,i1=j1=0; j<=lnz+s; j++)
  {
    GEN z = gel(H,j);
    if (diagH1[j])
    { /* hit exactly s times */
      i1++; C[i1+col] = Cnew[j+zc];
      p1 = cgetg(lig+1,t_COL); gel(Bnew,i1) = p1;
      for (i=1; i<=nlze; i++) gel(p1,i) = gcoeff(dep,i,j);
      p1 += nlze;
    }
    else
    {
      j1++; C[j1+zc] = Cnew[j+zc];
      p1 = cgetg(lnz+1,t_COL); gel(Hnew,j1) = p1;
      depnew[j1] = dep[j];
    }
    for (i=k=1; k<=lnz; i++)
      if (!diagH1[i]) p1[k++] = z[i];
  }
  for (j=s+1; j<co-col; j++)
  {
    GEN z = gel(B,j-s);
    p1 = cgetg(lig+1,t_COL); gel(Bnew,j) = p1;
    for (i=1; i<=nlze; i++) p1[i] = z[i];
    z += nlze; p1 += nlze;
    for (i=k=1; k<=lnz; i++)
      if (!diagH1[i]) p1[k++] = z[i];
  }
  if (DEBUGLEVEL>5)
  {
    fprintferr("Leaving hnffinal\n");
    if (DEBUGLEVEL>6)
    {
      if (nlze) fprintferr("dep = %Ps\n",depnew);
      fprintferr("mit = %Ps\nB = %Ps\nC = %Ps\n", Hnew, Bnew, C);
    }
  }
  *ptdep = depnew;
  *ptC = C;
  *ptB = Bnew; return Hnew;
}

/* for debugging */
static void
p_mat(GEN mat, GEN perm, long k)
{
  pari_sp av = avma;
  perm = vecslice(perm, k+1, lg(perm)-1);
  fprintferr("Permutation: %Ps\n",perm);
  if (DEBUGLEVEL > 6)
    fprintferr("matgen = %Ps\n", zm_to_ZM( rowpermute(mat, perm) ));
  avma = av;
}

static GEN
col_dup(long l, GEN col)
{
  GEN c = new_chunk(l);
  memcpy(c,col,l * sizeof(long)); return c;
}

/* HNF reduce a relation matrix (column operations + row permutation)
** Input:
**   mat = (li-1) x (co-1) matrix of long
**   C   = r x (co-1) matrix of GEN
**   perm= permutation vector (length li-1), indexing the rows of mat: easier
**     to maintain perm than to copy rows. For columns we can do it directly
**     using e.g. swap(mat[i], mat[j])
**   k0 = integer. The k0 first lines of mat are dense, the others are sparse.
** Output: cf ASCII art in the function body
**
** row permutations applied to perm
** column operations applied to C. IN PLACE
**/
GEN
hnfspec_i(GEN mat0, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, long k0)
{
  pari_sp av, lim;
  long co, n, s, nlze, lnz, nr, i, j, k, lk0, col, lig, *p;
  GEN mat;
  GEN p1, p2, matb, matbnew, vmax, matt, T, extramat, B, C, H, dep, permpro;
  const long li = lg(perm); /* = lg(mat0[1]) */
  const long CO = lg(mat0);

  n = 0; /* -Wall */

  C = *ptC; co = CO;
  if (co > 300 && co > 1.5 * li)
  { /* treat the rest at the end */
    co = (long)(1.2 * li);
    setlg(C, co);
  }

  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnfspec\n");
    p_mat(mat0,perm,0);
  }
  matt = cgetg(co, t_MAT); /* dense part of mat (top) */
  mat = cgetg(co, t_MAT);
  for (j = 1; j < co; j++)
  {
    GEN matj = col_dup(li, gel(mat0,j));
    p1 = cgetg(k0+1,t_COL); gel(matt,j) = p1; gel(mat,j) = matj;
    for (i=1; i<=k0; i++) gel(p1,i) = stoi(matj[perm[i]]);
  }
  av = avma; lim = stack_lim(av,1);

  i = lig = li-1; col = co-1; lk0 = k0;
  T = (k0 || (lg(C) > 1 && lg(C[1]) > 1))? matid(col): NULL;
  /* Look for lines with a single non-0 entry, equal to 1 in absolute value */
  while (i > lk0 && col)
    switch( count(mat,perm[i],col,&n) )
    {
      case 0: /* move zero lines between k0+1 and lk0 */
        lk0++; lswap(perm[i], perm[lk0]);
        i = lig; continue;

      case 1: /* move trivial generator between lig+1 and li */
        lswap(perm[i], perm[lig]);
        if (T) swap(gel(T,n), gel(T,col));
        swap(gel(mat,n), gel(mat,col)); p = gel(mat,col);
        if (p[perm[lig]] < 0) /* = -1 */
        { /* convert relation -g = 0 to g = 0 */
          for (i=lk0+1; i<lig; i++) p[perm[i]] = -p[perm[i]];
          if (T)
          {
            p1 = gel(T,col);
            for (i=1; ; i++) /* T is a permuted identity: single non-0 entry */
              if (signe(gel(p1,i))) { togglesign_safe(&gel(p1,i)); break; }
          }
        }
        lig--; col--; i = lig; continue;

      default: i--;
    }
  if (DEBUGLEVEL>5) { fprintferr("    after phase1:\n"); p_mat(mat,perm,0); }

#define absmax(s,z) {long _z; _z = labs(z); if (_z > s) s = _z;}
  /* Get rid of all lines containing only 0 and +/- 1, keeping track of column
   * operations in T. Leave the rows 1..lk0 alone [up to k0, coefficient
   * explosion, between k0+1 and lk0, row is 0] */
  s = 0;
  while (lig > lk0 && col && s < (long)(HIGHBIT>>1))
  {
    for (i=lig; i>lk0; i--)
      if (count(mat,perm[i],col,&n) > 0) break;
    if (i == lk0) break;

    /* only 0, +/- 1 entries, at least 2 of them non-zero */
    lswap(perm[i], perm[lig]);
    swap(gel(mat,n), gel(mat,col)); p = gel(mat,col);
    if (T) swap(gel(T,n), gel(T,col));
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      if (T) ZV_togglesign(gel(T,col));
    }
    for (j=1; j<col; j++)
    {
      GEN matj = gel(mat,j);
      long t;
      if (! (t = matj[perm[lig]]) ) continue;
      if (t == 1) {
        for (i=lk0+1; i<=lig; i++) absmax(s, matj[perm[i]] -= p[perm[i]]);
      }
      else { /* t = -1 */
        for (i=lk0+1; i<=lig; i++) absmax(s, matj[perm[i]] += p[perm[i]]);
      }
      if (T) ZC_lincomb1_inplace(gel(T,j), gel(T,col), stoi(-t));
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"hnfspec[1]");
      if (T) T = gerepilecopy(av, T); else avma = av;
    }
  }
  /* As above with lines containing a +/- 1 (no other assumption).
   * Stop when single precision becomes dangerous */
  vmax = cgetg(co,t_VECSMALL);
  for (j=1; j<=col; j++)
  {
    GEN matj = gel(mat,j);
    for (s=0, i=lk0+1; i<=lig; i++) absmax(s, matj[i]);
    vmax[j] = s;
  }
  while (lig > lk0 && col)
  {
    for (i=lig; i>lk0; i--)
      if ( (n = count2(mat,perm[i],col)) ) break;
    if (i == lk0) break;

    lswap(vmax[n], vmax[col]);
    lswap(perm[i], perm[lig]);
    swap(gel(mat,n), gel(mat,col)); p = gel(mat,col);
    if (T) swap(gel(T,n), gel(T,col));
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      if (T) ZV_togglesign(gel(T,col));
    }
    for (j=1; j<col; j++)
    {
      GEN matj = gel(mat,j);
      long t;
      if (! (t = matj[perm[lig]]) ) continue;
      if (vmax[col] && (ulong)labs(t) >= (HIGHBIT-vmax[j]) / vmax[col])
        goto END2;

      for (s=0, i=lk0+1; i<=lig; i++) absmax(s, matj[perm[i]] -= t*p[perm[i]]);
      vmax[j] = s;
      if (T) ZC_lincomb1_inplace(gel(T,j), gel(T,col), stoi(-t));
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"hnfspec[2]");
      gerepileall(av, T? 2: 1, &vmax, &T);
    }
  }

END2: /* clean up mat: remove everything to the right of the 1s on diagonal */
  /* go multiprecision first */
  matb = cgetg(co,t_MAT); /* bottom part (complement of matt) */
  for (j=1; j<co; j++)
  {
    GEN matj = gel(mat,j);
    p1 = cgetg(li-k0,t_COL); gel(matb,j) = p1;
    p1 -= k0;
    for (i=k0+1; i<li; i++) gel(p1,i) = stoi(matj[perm[i]]);
  }
  if (DEBUGLEVEL>5)
  {
    fprintferr("    after phase2:\n");
    p_mat(mat,perm,lk0);
  }
  for (i=li-2; i>lig; i--)
  {
    long h, i0 = i - k0, k = i + co-li;
    GEN Bk = gel(matb,k);
    for (j=k+1; j<co; j++)
    {
      GEN Bj = gel(matb,j), v = gel(Bj,i0);
      s = signe(v); if (!s) continue;

      gel(Bj,i0) = gen_0;
      if (is_pm1(v))
      {
        if (s > 0) /* v = 1 */
        { for (h=1; h<i0; h++) gel(Bj,h) = subii(gel(Bj,h), gel(Bk,h)); }
        else /* v = -1 */
        { for (h=1; h<i0; h++) gel(Bj,h) = addii(gel(Bj,h), gel(Bk,h)); }
      }
      else {
        for (h=1; h<i0; h++) gel(Bj,h) = subii(gel(Bj,h), mulii(v,gel(Bk,h)));
      }
      if (T) ZC_lincomb1_inplace(gel(T,j), gel(T,k), negi(v));
      if (low_stack(lim, stack_lim(av,1)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"hnfspec[3], (i,j) = %ld,%ld", i,j);
        for (h=1; h<co; h++) setlg(matb[h], i0+1); /* bottom can be forgotten */
        gerepileall(av, T? 2: 1, &matb, &T);
        Bk = gel(matb,k);
      }
    }
  }
  for (j=1; j<co; j++) setlg(matb[j], lig-k0+1); /* bottom can be forgotten */
  gerepileall(av, T? 2: 1, &matb, &T);
  if (DEBUGLEVEL>5) fprintferr("    matb cleaned up (using Id block)\n");

  nlze = lk0 - k0;  /* # of 0 rows */
  lnz = lig-nlze+1; /* 1 + # of non-0 rows (!= 0...0 1 0 ... 0) */
  if (T) matt = ZM_mul(matt,T); /* update top rows */
  extramat = cgetg(col+1,t_MAT); /* = new C minus the 0 rows */
  for (j=1; j<=col; j++)
  {
    GEN z = gel(matt,j);
    GEN t = (gel(matb,j)) + nlze - k0;
    p2=cgetg(lnz,t_COL); gel(extramat,j) = p2;
    for (i=1; i<=k0; i++) p2[i] = z[i]; /* top k0 rows */
    for (   ; i<lnz; i++) p2[i] = t[i]; /* other non-0 rows */
  }
  if (!col) {
    permpro = identity_perm(lnz);
    nr = lnz;
  }
  else
    permpro = imagecomplspec(extramat, &nr);
  /* lnz = lg(permpro) */
  if (nlze)
  { /* put the nlze 0 rows (trivial generators) at the top */
    p1 = new_chunk(lk0+1);
    for (i=1; i<=nlze; i++) p1[i] = perm[i + k0];
    for (   ; i<=lk0; i++)  p1[i] = perm[i - nlze];
    for (i=1; i<=lk0; i++)  perm[i] = p1[i];
  }
  /* sort other rows according to permpro (nr redundant generators first) */
  p1 = new_chunk(lnz); p2 = perm + nlze;
  for (i=1; i<lnz; i++) p1[i] = p2[permpro[i]];
  for (i=1; i<lnz; i++) p2[i] = p1[i];
  /* perm indexes the rows of mat
   *   |_0__|__redund__|__dense__|__too big__|_____done______|
   *   0  nlze                              lig             li
   *         \___nr___/ \___k0__/
   *         \____________lnz ______________/
   *
   *               col   co
   *       [dep     |     ]
   *    i0 [--------|  B  ] (i0 = nlze + nr)
   *       [matbnew |     ] matbnew has maximal rank = lnz-1 - nr
   * mat = [--------|-----] lig
   *       [   0    | Id  ]
   *       [        |     ] li */

  matbnew = cgetg(col+1,t_MAT); /* dense+toobig, maximal rank. For hnffinal */
  dep    = cgetg(col+1,t_MAT); /* rows dependent from the ones in matbnew */
  for (j=1; j<=col; j++)
  {
    GEN z = gel(extramat,j);
    p1 = cgetg(nlze+nr+1,t_COL); gel(dep,j) = p1;
    p2 = cgetg(lnz-nr,t_COL); gel(matbnew,j) = p2;
    for (i=1; i<=nlze; i++) gel(p1,i) = gen_0;
    p1 += nlze; for (i=1; i<=nr; i++) p1[i] = z[permpro[i]];
    p2 -= nr;   for (   ; i<lnz; i++) p2[i] = z[permpro[i]];
  }

  /* redundant generators in terms of the genuine generators
   * (x_i) = - (g_i) B */
  B = cgetg(co-col,t_MAT);
  for (j=col+1; j<co; j++)
  {
    GEN y = gel(matt,j);
    GEN z = gel(matb,j);
    p1=cgetg(lig+1,t_COL); gel(B,j-col) = p1;
    for (i=1; i<=nlze; i++) p1[i] = z[i];
    p1 += nlze; z += nlze-k0;
    for (k=1; k<lnz; k++)
    {
      i = permpro[k];
      p1[k] = (i <= k0)? y[i]: z[i];
    }
  }
  if (T) C = typ(C)==t_MAT? RgM_mul(C,T): RgV_RgM_mul(C,T);
  *ptdep = dep;
  *ptB = B;
  H = hnffinal(matbnew, perm, ptdep, ptB, &C);
  if (DEBUGLEVEL)
    msgtimer("hnfspec [%ld x %ld] --> [%ld x %ld]",li-1,co-1, lig-1,col-1);
  if (CO > co)
  { /* treat the rest, N cols at a time (hnflll slow otherwise) */
    const long N = 300;
    long a, L = CO - co, l = minss(L, N); /* L columns to add */
    GEN CC = *ptC, m0 = mat0;
    setlg(CC, CO); /* restore */
    CC += co-1;
    m0 += co-1;
    for (a = l;;)
    {
      GEN MAT, emb;
      gerepileall(av, 4, &H,&C,ptB,ptdep);
      MAT = cgetg(l + 1, t_MAT);
      emb = cgetg(l + 1, t_MAT);
      for (j = 1 ; j <= l; j++)
      {
        MAT[j] = m0[j];
        emb[j] = CC[j];
      }
      H = hnfadd_i(H, perm, ptdep, ptB, &C, MAT, emb);
      if (a == L) break;
      CC += l;
      m0 += l;
      a += l; if (a > L) { l = L - (a - l); a = L; }
    }
  }
  *ptC = C; return H;
}

GEN
hnfspec(GEN mat, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, long k0)
{
  pari_sp av = avma;
  GEN H = hnfspec_i(mat, perm, ptdep, ptB, ptC, k0);
  gerepileall(av, 4, ptC, ptdep, ptB, &H); return H;
}

/* HNF reduce x, apply same transforms to C */
GEN
mathnfspec(GEN x, GEN *ptperm, GEN *ptdep, GEN *ptB, GEN *ptC)
{
  long i,j,k,ly,lx = lg(x);
  GEN z, perm;
  if (lx == 1) return cgetg(1, t_MAT);
  ly = lg(x[1]);
  z = cgetg(lx,t_MAT);
  perm = cgetg(ly,t_VECSMALL); *ptperm = perm;
  for (i=1; i<ly; i++) perm[i] = i;
  for (i=1; i<lx; i++)
  {
    GEN C = cgetg(ly,t_COL), D = gel(x,i);
    gel(z,i) = C;
    for (j=1; j<ly; j++)
    {
      GEN d = gel(D,j);
      if (is_bigint(d)) goto TOOLARGE;
      C[j] = itos(d);
    }
  }
  /*  [ dep |     ]
   *  [-----|  B  ]
   *  [  H  |     ]
   *  [-----|-----]
   *  [  0  | Id  ] */
  return hnfspec(z,perm, ptdep, ptB, ptC, 0);

TOOLARGE:
  if (lg(*ptC) > 1 && lg((*ptC)[1]) > 1)
    pari_err(impl,"mathnfspec with large entries");
  x = ZM_hnf(x); lx = lg(x); j = ly; k = 0;
  for (i=1; i<ly; i++)
  {
    if (equali1(gcoeff(x,i,i + lx-ly)))
      perm[--j] = i;
    else
      perm[++k] = i;
  }
  setlg(perm,k+1);
  x = rowpermute(x, perm); /* upper part */
  setlg(perm,ly);
  *ptB = vecslice(x, j+lx-ly, lx-1);
  setlg(x, j);
  *ptdep = rowslice(x, 1, lx-ly);
  return rowslice(x, lx-ly+1, k); /* H */
}

/* add new relations to a matrix treated by hnfspec (extramat / extraC) */
GEN
hnfadd_i(GEN H, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, /* cf hnfspec */
       GEN extramat,GEN extraC)
{
  GEN matb, extratop, Cnew, permpro, B = *ptB, C = *ptC, dep = *ptdep;
  long i, lH, lB, li, lig, co, col, nlze;

  if (lg(extramat) == 1) return H;
  co = lg(C)-1;
  lH = lg(H)-1;
  lB = lg(B)-1;
  li = lg(perm)-1;
  lig = li - lB;
  col = co - lB;
  nlze = lH? lg(dep[1])-1: lg(B[1])-1;

 /*               col    co
  *       [ 0 |dep |     ]
  *  nlze [--------|  B  ]
  *       [ 0 | H  |     ]
  *       [--------|-----] lig
  *       [   0    | Id  ]
  *       [        |     ] li */
  extratop = zm_to_ZM( rowslicepermute(extramat, perm, 1, lig) );
  if (li != lig)
  { /* zero out bottom part, using the Id block */
    GEN A = vecslice(C, col+1, co);
    GEN c = rowslicepermute(extramat, perm, lig+1, li);
    extraC   = gsub(extraC, typ(A)==t_MAT? RgM_zm_mul(A, c): RgV_zm_mul(A,c));
    extratop = ZM_sub(extratop, ZM_zm_mul(B, c));
  }

  extramat = shallowconcat(extratop, vconcat(dep, H));
  Cnew     = shallowconcat(extraC, vecslice(C, col-lH+1, co));
  if (DEBUGLEVEL>5) fprintferr("    1st phase done\n");
  permpro = imagecomplspec(extramat, &nlze);
  extramat = rowpermute(extramat, permpro);
  *ptB     = rowpermute(B,        permpro);
  permpro = vecpermute(perm, permpro);
  for (i=1; i<=lig; i++) perm[i] = permpro[i]; /* perm o= permpro */

  *ptdep  = rowslice(extramat, 1, nlze);
  matb    = rowslice(extramat, nlze+1, lig);
  if (DEBUGLEVEL>5) fprintferr("    2nd phase done\n");
  H = hnffinal(matb,perm,ptdep,ptB,&Cnew);
  *ptC = shallowconcat(vecslice(C, 1, col-lH), Cnew);
  if (DEBUGLEVEL)
  {
    msgtimer("hnfadd (%ld + %ld)", lg(extratop)-1, lg(dep)-1);
    if (DEBUGLEVEL>7) fprintferr("H = %Ps\nC = %Ps\n",H,*ptC);
  }
  return H;
}

GEN
hnfadd(GEN H, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, /* cf hnfspec */
       GEN extramat,GEN extraC)
{
  pari_sp av = avma;
  H = hnfadd_i(H, perm, ptdep, ptB, ptC, ZM_to_zm(extramat), extraC);
  gerepileall(av, 4, ptC, ptdep, ptB, &H); return H;
}

/* zero aj = Aij (!= 0)  using  ak = Aik (maybe 0), via linear combination of
 * A[j] and A[k] of determinant 1. If U != NULL, likewise update its columns */
static void
ZC_elem(GEN aj, GEN ak, GEN A, GEN U, long j, long k)
{
  GEN p1,u,v,d;

  if (!signe(ak)) {
    swap(gel(A,j), gel(A,k));
    if (U) swap(gel(U,j), gel(U,k));
    return;
  }
  d = bezout(aj,ak,&u,&v);
  /* frequent special case (u,v) = (1,0) or (0,1) */
  if (!signe(u))
  { /* ak | aj */
    p1 = diviiexact(aj,ak); togglesign(p1);
    ZC_lincomb1_inplace(gel(A,j), gel(A,k), p1);
    if (U)
      ZC_lincomb1_inplace(gel(U,j), gel(U,k), p1);
    return;
  }
  if (!signe(v))
  { /* aj | ak */
    p1 = diviiexact(ak,aj); togglesign(p1);
    ZC_lincomb1_inplace(gel(A,k), gel(A,j), p1);
    swap(gel(A,j), gel(A,k));
    if (U) {
      ZC_lincomb1_inplace(gel(U,k), gel(U,j), p1);
      swap(gel(U,j), gel(U,k));
    }
    return;
  }

  if (!is_pm1(d)) { aj = diviiexact(aj, d); ak = diviiexact(ak, d); }
  p1 = gel(A,k); aj = negi(aj); /* NOT togglesign */
  gel(A,k) = ZC_lincomb(u,v, gel(A,j),p1);
  gel(A,j) = ZC_lincomb(aj,ak, p1,gel(A,j));
  if (U)
  {
    p1 = gel(U,k);
    gel(U,k) = ZC_lincomb(u,v, gel(U,j),p1);
    gel(U,j) = ZC_lincomb(aj,ak, p1,gel(U,j));
  }
}

/* reduce A[i,j] mod A[i,j0] for j=j0+1... via column operations */
static void
ZM_reduce(GEN A, GEN U, long i, long j0)
{
  long j, lA = lg(A);
  GEN d = gcoeff(A,i,j0);
  if (signe(d) < 0)
  {
    ZV_neg_inplace(gel(A,j0));
    if (U) ZV_togglesign(gel(U,j0));
    d = gcoeff(A,i,j0);
  }
  for (j=j0+1; j<lA; j++)
  {
    GEN q = truedivii(gcoeff(A,i,j), d);
    if (!signe(q)) continue;

    togglesign(q);
    ZC_lincomb1_inplace(gel(A,j), gel(A,j0), q);
    if (U) ZC_lincomb1_inplace(gel(U,j), gel(U,j0), q);
  }
}

/* A,B square integral in upper HNF, of the same dimension > 0. Return Au
 * in Z^n (v in Z^n not computed), such that Au + Bv = [1, 0, ..., 0] */
GEN
hnfmerge_get_1(GEN A, GEN B)
{
  pari_sp av = avma;
  long j, k, c, l = lg(A), lb;
  GEN b, t, U = cgetg(l + 1, t_MAT), C = cgetg(l + 1, t_VEC);

  t = NULL; /* -Wall */
  b = gcoeff(B,1,1); lb = lgefint(b);
  if (!signe(b)) {
    if (!is_pm1(gcoeff(A,1,1))) return NULL;
    return scalarcol_shallow(gen_1, l-1);
  }
  for (j = 1; j < l; j++)
  {
    c = j+1;
    gel(U,j) = col_ei(l-1, j);
    gel(U,c) = zerocol(l-1); /* dummy */
    gel(C,j) = vecslice(gel(A,j), 1,j);
    gel(C,c) = vecslice(gel(B,j), 1,j);
    for (k = j; k > 0; k--)
    {
      t = gcoeff(C,k,c);
      if (gequal0(t)) continue;
      setlg(C[c], k+1);
      ZC_elem(t, gcoeff(C,k,k), C, U, c, k);
      if (lgefint(gcoeff(C,k,k)) > lb) gel(C,k) = FpC_red(gel(C,k), b);
      if (j > 4)
      {
        GEN u = gel(U,k);
        long h;
        for (h=1; h<l; h++)
          if (lgefint(u[h]) > lb) gel(u,h) = remii(gel(u,h), b);
      }
    }
    if (j == 1)
      t = gcoeff(C,1,1);
    else
    {
      GEN u;
      t = bezout(gcoeff(C,1,1), b, &u, NULL); /* >= 0 */
      if (signe(u) && !equali1(u)) gel(U,1) = ZC_Z_mul(gel(U,1), u);
      gcoeff(C,1,1) = t;
    }
    if (equali1(t)) break;
  }
  if (j >= l) return NULL;
  return gerepileupto(av, ZM_ZC_mul(A,gel(U,1)));
}

/* Inefficient compared to hnfall. 'remove' = throw away lin.dep columns */
static GEN
hnf_i(GEN A, int remove)
{
  pari_sp av0 = avma, av, lim;
  long s, m, n = lg(A)-1, i, j, k, li, def, ldef;
  GEN a;

  if (!n) return cgetg(1,t_MAT);
  av = avma; A = RgM_shallowcopy(A);
  m = lg(A[1])-1;

  lim = stack_lim(av,1);
  def = n; ldef = (m>n)? m-n: 0;
  for (li=m; li>ldef; li--)
  {
    for (j=def-1; j; j--)
    {
      a = gcoeff(A,li,j);
      if (!signe(a)) continue;

      /* zero a = Aij  using  b = Aik */
      k = (j==1)? def: j-1;
      ZC_elem(a,gcoeff(A,li,k), A,NULL, j,k);
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnf[1]. li=%ld",li);
        A = gerepilecopy(av, A);
      }
    }
    s = signe(gcoeff(A,li,def));
    if (s)
    {
      if (s < 0) ZV_neg_inplace(gel(A,def));
      ZM_reduce(A, NULL, li,def);
      def--;
    }
    else
      if (ldef) ldef--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnf[2]. li=%ld",li);
      A = gerepilecopy(av, A);
    }
  }
  if (remove)
  { /* remove 0 columns */
    for (i=1,j=1; j<=n; j++)
      if (!ZV_equal0(gel(A,j))) A[i++] = A[j];
    setlg(A,i);
  }
  return gerepileupto(av0, ZM_copy(A));
}

GEN
ZM_hnf(GEN x) { return lg(x) > 8? ZM_hnfall(x, NULL, 1): hnf_i(x, 1); }

/* u*z[1..k] mod b, in place */
static void
FpV_Fp_mul_part_ip(GEN z, GEN u, GEN p, long k)
{
  long i;
  if (is_pm1(u)) {
    if (signe(u) > 0) {
      for (i = 1; i <= k; i++)
        if (signe(z[i])) gel(z,i) = modii(gel(z,i), p);
    } else {
      for (i = 1; i <= k; i++)
        if (signe(z[i])) gel(z,i) = modii(negi(gel(z,i)), p);
    }
  }
  else {
    for (i = 1; i <= k; i++)
      if (signe(z[i])) gel(z,i) = Fp_mul(u,gel(z,i), p);
  }
}
static void
FpV_red_part_ip(GEN z, GEN p, long k)
{
  long i;
  for (i = 1; i <= k; i++) gel(z,i) = modii(gel(z,i), p);
}
/* dm = multiple of diag element (usually detint(x))
 * flag & hnf_MODID: reduce mod dm * matid [ otherwise as above ].
 * flag & hnf_PART: don't reduce once diagonal is known; */

/* x a ZM, dm a t_INT */
GEN
ZM_hnfmodall(GEN x, GEN dm, long flag)
{
  pari_sp av0 = avma, av, lim;
  const long modid = (flag & hnf_MODID);
  const long center = (flag & hnf_CENTER);
  long li, co, i, j, k, def, ldef, ldm;
  GEN a, b, p1, p2, u, dm2;

  co = lg(x); if (co == 1) return cgetg(1,t_MAT);
  li = lg(x[1]); dm2 = shifti(dm, -1);
  av = avma; lim = stack_lim(av,1);
  x = RgM_shallowcopy(x);

  ldef = 0;
  if (li > co)
  {
    ldef = li - co;
    if (!modid) pari_err(talker,"nb lines > nb columns in ZM_hnfmod");
  }
  /* To prevent coeffs explosion, only reduce mod dm when lg() > ldm */
  ldm = lgefint(dm);
  for (def = co-1,i = li-1; i > ldef; i--,def--)
  {
    gcoeff(x,i,def) = centermodii(gcoeff(x,i,def), dm,dm2);
    for (j = def-1; j; j--)
    {
      gcoeff(x,i,j) = centermodii(gcoeff(x,i,j), dm,dm2);
      a = gcoeff(x,i,j);
      if (!signe(a)) continue;

      k = (j==1)? def: j-1;
      gcoeff(x,i,k) = centermodii(gcoeff(x,i,k), dm,dm2);
      ZC_elem(a,gcoeff(x,i,k), x,NULL, j,k);
      p1 = gel(x,j);
      p2 = gel(x,k);
      for (k = 1; k < i; k++)
      {
        if (lgefint(p1[k]) > ldm) gel(p1,k) = centermodii(gel(p1,k), dm,dm2);
        if (lgefint(p2[k]) > ldm) gel(p2,k) = centermodii(gel(p2,k), dm,dm2);
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnfmod[1]. i=%ld",i);
        x = gerepilecopy(av, x);
      }
    }
    if (modid && !signe(gcoeff(x,i,def)))
    { /* missing pivot on line i, insert column */
      GEN a = cgetg(co + 1, t_MAT);
      for (k = 1; k <= def; k++) a[k] = x[k];
      gel(a,k++) = Rg_col_ei(dm, li-1, i);
      for (     ; k <= co;  k++) a[k] = x[k-1];
      ldef--; if (ldef < 0) ldef = 0;
      co++; def++; x = a;
    }
  }
  x += co - li;
  if (modid)
  { /* w[li] is an accumulator, discarded at the end */
    GEN w = cgetg(li+1, t_MAT);
    for (i = li-1; i > ldef; i--) w[i] = x[i];
    for (        ; i > 0;    i--) gel(w,i) = Rg_col_ei(dm, li-1, i);
    x = w;
    for (i = li-1; i > 0; i--)
    { /* check that dm*Id \subset L + add up missing dm*Id components */
      GEN d, c;
      d = bezout(gcoeff(x,i,i),dm, &u,NULL);
      gcoeff(x,i,i) = d;
      if (is_pm1(d))
      {
        FpV_Fp_mul_part_ip(gel(x,i), u, dm, i-1);
        continue;
      }
      c = cgetg(li, t_COL);
      for (j = 1; j < i; j++) gel(c,j) = remii(gcoeff(x,j,i),d);
      for (     ; j <li; j++) gel(c,j) = gen_0;
      if (!equalii(dm, d)) c = ZC_Z_mul(c, diviiexact(dm, d));
      gel(x,li) = c;
      FpV_Fp_mul_part_ip(gel(x,i), u, dm, i-1);
      for (j = i - 1; j > ldef; j--)
      {
        GEN a = gcoeff(x, j, li);
        if (!signe(a)) continue;
        ZC_elem(a, gcoeff(x,j,j), x, NULL, li,j);
        FpV_red_part_ip(gel(x,li), dm, j-1);
        FpV_red_part_ip(gel(x,j),  dm, j-1);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnfmod[2]. i=%ld", i);
          x = gerepilecopy(av, x);
        }
      }
    }
  }
  else
  {
    b = dm;
    for (i = li-1; i > 0; i--)
    {
      GEN d = bezout(gcoeff(x,i,i),b, &u,NULL);
      gcoeff(x,i,i) = d;
      FpV_Fp_mul_part_ip(gel(x,i), u, b, i-1);
      if (i > 1) b = diviiexact(b,d);
    }
  }
  x[0] = evaltyp(t_MAT) | evallg(li); /* kill 0 columns / discard accumulator */
  if (flag & hnf_PART) return x;

  if (modid) b = const_vec(li-1, dm);
  else
  { /* compute optimal value for dm */
    b = cgetg(li, t_VEC); gel(b,1) = gcoeff(x,1,1);
    for (i = 2; i < li; i++) gel(b,i) = mulii(gel(b,i-1), gcoeff(x,i,i));
  }
  dm = b;

  for (i = li-2; i > 0; i--)
  {
    GEN diag = gcoeff(x,i,i);
    ldm = lgefint(dm[i]);
    for (j = i+1; j < li; j++)
    {
      b = gcoeff(x,i,j);
      b = center? diviiround(b,diag): truedivii(b, diag);
      if (!signe(b)) continue;
      togglesign(b);
      ZC_lincomb1_inplace(gel(x,j), gel(x,i),b);
      p1 = gel(x,j);
      for (k=1; k<i; k++)
        if (lgefint(p1[k]) > ldm) gel(p1,k) = remii(gel(p1,k), gel(dm,i));
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnfmod[3]. i=%ld", i);
        gerepileall(av, 2, &x, &dm); diag = gcoeff(x,i,i);
      }
    }
  }
  return gerepilecopy(av0, x);
}
GEN
ZM_hnfmod(GEN x, GEN d) { return ZM_hnfmodall(x,d,0); }
GEN
ZM_hnfmodid(GEN x, GEN d) { return ZM_hnfmodall(x,d,hnf_MODID); }

static GEN
allhnfmod(GEN x, GEN dm, int flag)
{
  if (typ(dm)!=t_INT) pari_err(typeer,"allhnfmod");
  if (typ(x)!=t_MAT) pari_err(typeer,"allhnfmod");
  RgM_check_ZM(x, "allhnfmod");
  return signe(dm)? ZM_hnfmodall(x, dm, flag): ZM_hnf(x);
}
GEN
hnfmod(GEN x, GEN d) { return allhnfmod(x, d, 0); }
GEN
hnfmodid(GEN x, GEN d) { return allhnfmod(x, d, hnf_MODID); }

/* M a ZM in HNF. Normalize with *centered* residues */
GEN
ZM_hnfcenter(GEN M)
{
  long i, j, k, N = lg(M)-1;
  pari_sp av = avma, lim = stack_lim(av,1);

  for (j=N-1; j>0; j--) /* skip last line */
  {
    GEN Mj = gel(M,j), a = gel(Mj,j);
    for (k = j+1; k <= N; k++)
    {
      GEN Mk = gel(M,k), q = diviiround(gel(Mk,j), a);
      long s = signe(q);
      if (!s) continue;
      if (is_pm1(q))
      {
        if (s < 0)
          for (i = 1; i <= j; i++) gel(Mk,i) = addii(gel(Mk,i), gel(Mj,i));
        else
          for (i = 1; i <= j; i++) gel(Mk,i) = subii(gel(Mk,i), gel(Mj,i));
      }
      else
        for (i = 1; i <= j; i++) gel(Mk,i) = subii(gel(Mk,i), mulii(q,gel(Mj,i)));
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM) pari_warn(warnmem,"ZM_hnfcenter, j = %ld",j);
        M = gerepilecopy(av, M);
      }
    }
  }
  return M;
}

/***********************************************************************/
/*                                                                     */
/*                 HNFLLL (Havas, Majewski, Mathews)                   */
/*                                                                     */
/***********************************************************************/

static void
Minus(long j, GEN lambda)
{
  long k, n = lg(lambda);

  for (k=1  ; k<j; k++) togglesign_safe(&gcoeff(lambda,k,j));
  for (k=j+1; k<n; k++) togglesign_safe(&gcoeff(lambda,j,k));
}

/* index of first non-zero entry */
static long
findi(GEN M)
{
  long i, n = lg(M);
  for (i=1; i<n; i++)
    if (signe(M[i])) return i;
  return 0;
}

static long
findi_normalize(GEN Aj, GEN B, long j, GEN lambda)
{
  long r = findi(Aj);
  if (r && signe(Aj[r]) < 0)
  {
    ZV_togglesign(Aj); if (B) ZV_togglesign(gel(B,j));
    Minus(j,lambda);
  }
  return r;
}

static void
reduce2(GEN A, GEN B, long k, long j, long *row0, long *row1, GEN lambda, GEN D)
{
  GEN q;
  long i;

  *row0 = findi_normalize(gel(A,j), B,j,lambda);
  *row1 = findi_normalize(gel(A,k), B,k,lambda);
  if (*row0)
    q = truedivii(gcoeff(A,*row0,k), gcoeff(A,*row0,j));
  else if (absi_cmp(shifti(gcoeff(lambda,j,k), 1), gel(D,j)) > 0)
    q = diviiround(gcoeff(lambda,j,k), gel(D,j));
  else
    return;

  if (signe(q))
  {
    GEN Lk = gel(lambda,k), Lj = gel(lambda,j);
    togglesign_safe(&q);
    if (*row0) ZC_lincomb1_inplace(gel(A,k),gel(A,j),q);
    if (B) ZC_lincomb1_inplace(gel(B,k),gel(B,j),q);
    gel(Lk,j) = addii(gel(Lk,j), mulii(q,gel(D,j)));
    if (is_pm1(q))
    {
      if (signe(q) > 0)
      {
        for (i=1; i<j; i++)
          if (signe(Lj[i])) gel(Lk,i) = addii(gel(Lk,i), gel(Lj,i));
      }
      else
      {
        for (i=1; i<j; i++)
          if (signe(Lj[i])) gel(Lk,i) = subii(gel(Lk,i), gel(Lj,i));
      }
    }
    else
    {
      for (i=1; i<j; i++)
        if (signe(Lj[i])) gel(Lk,i) = addii(gel(Lk,i), mulii(q,gel(Lj,i)));
    }
  }
}

static void
hnfswap(GEN A, GEN B, long k, GEN lambda, GEN D)
{
  GEN t, p1, p2, Lk = gel(lambda,k);
  long i,j,n = lg(A);

  swap(gel(A,k), gel(A,k-1));
  if (B) swap(gel(B,k), gel(B,k-1));
  for (j=k-2; j; j--) swap(gcoeff(lambda,j,k-1), gel(Lk,j));
  for (i=k+1; i<n; i++)
  {
    GEN Li = gel(lambda,i);
    p1 = mulii(gel(Li,k-1), gel(D,k));
    p2 = mulii(gel(Li,k), gel(Lk,k-1));
    t = subii(p1,p2);

    p1 = mulii(gel(Li,k), gel(D,k-2));
    p2 = mulii(gel(Li,k-1), gel(Lk,k-1));
    gel(Li,k-1) = diviiexact(addii(p1,p2), gel(D,k-1));
    gel(Li,k) = diviiexact(t, gel(D,k-1));
  }
  p1 = mulii(gel(D,k-2), gel(D,k));
  p2 = sqri(gel(Lk,k-1));
  gel(D,k-1) = diviiexact(addii(p1,p2), gel(D,k-1));
}

/* reverse row order in matrix A, IN PLACE */
static GEN
reverse_rows(GEN A)
{
  long i, j, h, n = lg(A);
  if (n == 1) return A;
  h = lg(A[1]);
  for (j=1; j<n; j++)
  {
    GEN c = gel(A,j);
    /* start at (h-1) >>1 : if h = 2i even, no need to swap c[i] and itself */
    for (i=(h-1)>>1; i; i--) swap(gel(c,i), gel(c,h-i));
  }
  return A;
}

/* remove the first r columns */
static void
remove_0cols(long r, GEN *pA, GEN *pB, long remove)
{
  GEN A = *pA, B = *pB;
  long l = lg(A);
  A += r; A[0] = evaltyp(t_MAT) | evallg(l-r);
  if (B && remove == 2) { B += r; B[0] = A[0]; }
  *pA = A; *pB = B;
}

GEN
ZM_hnflll(GEN A, GEN *ptB, int remove)
{
  pari_sp av = avma, lim = stack_lim(av,3);
#ifdef HNFLLL_QUALITY
  const long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
#endif
  long n, k, kmax;
  GEN B, lambda, D;

  n = lg(A);
  A = reverse_rows(ZM_copy(A)); /* ZM_copy for in place findi_normalize() */
  B = ptB? matid(n-1): NULL;
  D = const_vec(n, gen_1) + 1;
  lambda = zeromatcopy(n-1,n-1);
  k = kmax = 2;
  while (k < n)
  {
    long row0, row1;
    int do_swap;
    reduce2(A,B,k,k-1,&row0,&row1,lambda,D);
    if (row0)
      do_swap = (!row1 || row0 <= row1);
    else if (!row1)
    { /* row0 == row1 == 0 */
      pari_sp av1 = avma;
      GEN z = addii(mulii(gel(D,k-2),gel(D,k)), sqri(gcoeff(lambda,k-1,k)));
#ifdef HNFLLL_QUALITY
      do_swap = (cmpii(mului(n1,z), mului(m1,sqri(gel(D,k-1)))) < 0);
#else /* assume m1 = n1 = 1 */
      do_swap = (cmpii(z, sqri(gel(D,k-1))) < 0);
#endif
      avma = av1;
    }
    else
      do_swap = 0;
    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k > 2) k--;
    }
    else
    {
      long i;
      for (i=k-2; i; i--)
      {
        long row0, row1;
        reduce2(A,B,k,i,&row0,&row1,lambda,D);
        if (low_stack(lim, stack_lim(av,3)))
        {
          GEN b = D-1;
          if (DEBUGMEM) pari_warn(warnmem,"hnflll (reducing), kmax = %ld",kmax);
          gerepileall(av, B? 4: 3, &A, &lambda, &b, &B);
          D = b+1;
        }
      }
      if (++k > kmax) kmax = k;
    }
    if (low_stack(lim, stack_lim(av,3)))
    {
      GEN b = D-1;
      if (DEBUGMEM) pari_warn(warnmem,"hnflll, kmax = %ld / %ld",kmax,n-1);
      gerepileall(av, B? 4: 3, &A, &lambda, &b, &B);
      D = b+1;
    }
  }
  /* handle trivial case: return negative diag coefficient otherwise */
  if (n == 2) (void)findi_normalize(gel(A,1), B,1,lambda);
  A = reverse_rows(A);
  if (remove)
  {
    long i;
    for (i = 1; i < n; i++)
      if (!ZV_equal0(gel(A,i))) break;
    remove_0cols(i-1, &A, &B, remove);
  }
  gerepileall(av, B? 2: 1, &A, &B);
  if (B) *ptB = B;
  return A;
}

GEN
hnflll(GEN x)
{
  GEN z = cgetg(3, t_VEC);
  gel(z,1) = ZM_hnflll(x, &gel(z,2), 0);
  return z;
}

/* Variation on HNFLLL: Extended GCD */

static void
reduce1(GEN A, GEN B, long k, long j, GEN lambda, GEN D)
{
  GEN q;
  long i;

  if (signe(A[j]))
    q = diviiround(gel(A,k),gel(A,j));
  else if (absi_cmp(shifti(gcoeff(lambda,j,k), 1), gel(D,j)) > 0)
    q = diviiround(gcoeff(lambda,j,k), gel(D,j));
  else
    return;

  if (signe(q))
  {
    GEN Lk = gel(lambda,k), Lj = gel(lambda,j);
    togglesign_safe(&q);
    gel(A,k) = addii(gel(A,k), mulii(q,gel(A,j)));
    ZC_lincomb1_inplace(gel(B,k),gel(B,j),q);
    gel(Lk,j) = addii(gel(Lk,j), mulii(q,gel(D,j)));
    for (i=1; i<j; i++)
      if (signe(Lj[i])) gel(Lk,i) = addii(gel(Lk,i), mulii(q,gel(Lj,i)));
  }
}

/* assume A is a ZV */
GEN
extendedgcd(GEN A)
{
#ifdef HNFLLL_QUALITY
  const long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
#endif
  pari_sp av = avma;
  long k, n = lg(A);
  GEN B, lambda, D;

  A = leafcopy(A);
  B = matid(n-1);
  lambda = zeromatcopy(n-1,n-1);
  D = const_vec(n, gen_1);
  k = 2;
  while (k < n)
  {
    int do_swap;

    reduce1(A,B,k,k-1,lambda,D);
    if (signe(A[k-1])) do_swap = 1;
    else if (!signe(A[k]))
    {
      pari_sp av1 = avma;
      GEN z = addii(mulii(gel(D,k-2),gel(D,k)), sqri(gcoeff(lambda,k-1,k)));
#ifdef HNFLLL_QUALITY
      do_swap = (cmpii(mului(n1,z), mului(m1,sqri(gel(D,k-1)))) < 0);
#else /* assume m1 = n1 = 1 */
      do_swap = (cmpii(z, sqri(gel(D,k-1))) < 0);
#endif
      avma = av1;
    }
    else do_swap = 0;

    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k > 2) k--;
    }
    else
    {
      long i;
      for (i=k-2; i; i--) reduce1(A,B,k,i,lambda,D);
      k++;
    }
  }
  if (signe(A[n-1]) < 0)
  {
    togglesign_safe(&gel(A,n-1));
    ZV_togglesign(gel(B,n-1));
  }
  return gerepilecopy(av, mkvec2(gel(A,n-1), B));
}

/* HNF with permutation. */
GEN
ZM_hnfperm(GEN A, GEN *ptU, GEN *ptperm)
{
  GEN U, c, l, perm, d, p, q, b;
  pari_sp av = avma, av1, lim;
  long r, t, i, j, j1, k, m, n;

  n = lg(A)-1;
  if (!n)
  {
    if (ptU) *ptU = cgetg(1,t_MAT);
    if (ptperm) *ptperm = cgetg(1,t_VEC);
    return cgetg(1, t_MAT);
  }
  m = lg(A[1])-1;
  c = const_vecsmall(m, 0);
  l = const_vecsmall(n, 0);
  perm = cgetg(m+1, t_VECSMALL);
  av1 = avma; lim = stack_lim(av1,1);
  A = RgM_shallowcopy(A);
  U = ptU? matid(n): NULL;
  /* U base change matrix : A0*U = A all along */
  for (r=0, k=1; k <= n; k++)
  {
    for (j=1; j<k; j++)
    {
      if (!l[j]) continue;
      t=l[j]; b=gcoeff(A,t,k);
      if (!signe(b)) continue;

      ZC_elem(b,gcoeff(A,t,j), A,U,k,j);
      d = gcoeff(A,t,j);
      if (signe(d) < 0)
      {
        ZV_neg_inplace(gel(A,j));
        if (U) ZV_togglesign(gel(U,j));
        d = gcoeff(A,t,j);
      }
      for (j1=1; j1<j; j1++)
      {
        if (!l[j1]) continue;
        q = truedivii(gcoeff(A,t,j1),d);
        if (!signe(q)) continue;

        togglesign(q);
        ZC_lincomb1_inplace(gel(A,j1), gel(A,j), q);
        if (U) ZC_lincomb1_inplace(gel(U,j1), gel(U,j), q);
      }
    }
    t = m; while (t && (c[t] || !signe(gcoeff(A,t,k)))) t--;
    if (t)
    {
      p = gcoeff(A,t,k);
      for (i=t-1; i; i--)
      {
        q = gcoeff(A,i,k);
        if (signe(q) && absi_cmp(p,q) > 0) { p = q; t = i; }
      }
      perm[++r] = l[k] = t; c[t] = k;
      if (signe(p) < 0)
      {
        ZV_neg_inplace(gel(A,k));
        if (U) ZV_togglesign(gel(U,k));
        p = gcoeff(A,t,k);
      }
      /* p > 0 */
      for (j=1; j<k; j++)
      {
        if (!l[j]) continue;
        q = truedivii(gcoeff(A,t,j),p);
        if (!signe(q)) continue;

        togglesign(q);
        ZC_lincomb1_inplace(gel(A,j), gel(A,k), q);
        if (U) ZC_lincomb1_inplace(gel(U,j), gel(U,k), q);
      }
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"hnfperm");
      gerepileall(av1, U? 2: 1, &A, &U);
    }
  }
  if (r < m)
  {
    for (i=1,k=r; i<=m; i++)
      if (!c[i]) perm[++k] = i;
  }

/* We have A0*U=A, U in Gl(n,Z)
 * basis for Im(A):  columns of A s.t l[j]>0 (r   cols)
 * basis for Ker(A): columns of U s.t l[j]=0 (n-r cols) */
  p = cgetg(r+1,t_MAT);
  for (i=1; i<=m/2; i++) lswap(perm[i], perm[m+1-i]);
  if (U)
  {
    GEN u = cgetg(n+1,t_MAT);
    for (t=1,k=r,j=1; j<=n; j++)
      if (l[j])
      {
        u[k + n-r] = U[j];
        gel(p,k--) = vecpermute(gel(A,j), perm);
      }
      else
        u[t++] = U[j];
    *ptU = u;
    if (ptperm) *ptperm = perm;
    gerepileall(av, ptperm? 3: 2, &p, ptU, ptperm);
  }
  else
  {
    for (k=r,j=1; j<=n; j++)
      if (l[j]) gel(p,k--) = vecpermute(gel(A,j), perm);
    if (ptperm) *ptperm = perm;
    gerepileall(av, ptperm? 2: 1, &p, ptperm);
  }
  return p;
}

GEN
hnfperm(GEN A)
{
  GEN y = cgetg(4, t_VEC);
  gel(y,1) = ZM_hnfperm(A, &gel(y,2), &gel(y,3));
  return y;
}

/* Hermite Normal Form, with base change matrix if ptB != NULL.
 * If 'remove' = 1, remove 0 columns (do NOT update *ptB accordingly)
 * If 'remove' = 2, remove 0 columns and update *ptB accordingly */
GEN
ZM_hnfall(GEN A, GEN *ptB, long remove)
{
  pari_sp av = avma, av1, lim;
  long m, n, r, i, j, k, li;
  GEN B, c, h, a;

  n = lg(A)-1;
  if (!n)
  {
    if (ptB) *ptB = cgetg(1,t_MAT);
    return cgetg(1,t_MAT);
  }
  m = lg(A[1])-1;
  c = const_vecsmall(m, 0);
  h = const_vecsmall(n, m);
  av1 = avma; lim = stack_lim(av1,1);
  A = RgM_shallowcopy(A);
  B = ptB? matid(n): NULL;
  r = n+1;
  for (li=m; li; li--)
  {
    for (j=1; j<r; j++)
    {
      for (i=h[j]; i>li; i--)
      {
        a = gcoeff(A,i,j);
        if (!signe(a)) continue;

        k = c[i]; /* zero a = Aij  using  Aik */
        ZC_elem(a,gcoeff(A,i,k), A,B,j,k);
        ZM_reduce(A,B, i,k);
        if (low_stack(lim, stack_lim(av1,1)))
        {
          if (DEBUGMEM>1) pari_warn(warnmem,"hnfall[1], li = %ld", li);
          gerepileall(av1, B? 2: 1, &A, &B);
        }
      }
      if (signe( gcoeff(A,li,j) )) break;
      h[j] = li-1;
    }
    if (j == r) continue;
    r--;
    if (j < r) /* A[j] != 0 */
    {
      swap(gel(A,j), gel(A,r));
      if (B) swap(gel(B,j), gel(B,r));
      h[j] = h[r]; h[r] = li; c[li] = r;
    }
    if (signe(gcoeff(A,li,r)) < 0)
    {
      ZV_neg_inplace(gel(A,r));
      if (B) ZV_togglesign(gel(B,r));
    }
    ZM_reduce(A,B, li,r);
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"hnfall[2], li = %ld", li);
      gerepileall(av1, B? 2: 1, &A, &B);
    }
  }

  if (DEBUGLEVEL>5) fprintferr("\nhnfall, final phase: ");
  r--; /* first r cols are in the image the n-r (independent) last ones */
  for (j=1; j<=r; j++)
    for (i=h[j]; i; i--)
    {
      a = gcoeff(A,i,j);
      k = c[i];
      if (signe(a)) ZC_elem(a,gcoeff(A,i,k), A,B, j,k);
      ZM_reduce(A,B, i,k); /* ensure non-negative entries, even if a = 0 */
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"hnfall[3], j = %ld", j);
        gerepileall(av1, B? 2: 1, &A, &B);
      }
    }
  if (DEBUGLEVEL>5) fprintferr("\n");
  if (remove) remove_0cols(r, &A, &B, remove);
  gerepileall(av, B? 2: 1, &A, &B);
  if (B) *ptB = B;
  return A;
}

GEN
hnfall(GEN x)
{
  GEN z = cgetg(3, t_VEC);
  gel(z,1) = ZM_hnfall(x, (GEN*)(z+2), 1);
  return z;
}
GEN
hnf(GEN x) { return mathnf0(x,0); }

/* C = A^(-1)(tB) where A, B, C are integral, A is upper triangular, t t_INT */
GEN
hnf_divscale(GEN A, GEN B, GEN t)
{
  long n = lg(A)-1, i,j,k;
  GEN m, c = cgetg(n+1,t_MAT);

  if (!n) return c;
  for (k=1; k<=n; k++)
  {
    GEN u = cgetg(n+1, t_COL), b = gel(B,k);
    pari_sp av = avma;
    gel(c,k) = u; m = mulii(gel(b,n),t);
    gel(u,n) = gerepileuptoint(av, diviiexact(m, gcoeff(A,n,n)));
    for (i=n-1; i>0; i--)
    {
      av = avma; m = mulii(gel(b,i),t);
      for (j=i+1; j<=n; j++) m = subii(m, mulii(gcoeff(A,i,j),gel(u,j)));
      gel(u,i) = gerepileuptoint(av, diviiexact(m, gcoeff(A,i,i)));
    }
  }
  return c;
}

/* A, B integral upper HNF. A^(-1) B integral ? */
int
hnfdivide(GEN A, GEN B)
{
  pari_sp av = avma;
  long n = lg(A)-1, i,j,k;
  GEN u, b, m, r;

  if (!n) return 1;
  if (lg(B)-1 != n) pari_err(consister,"hnfdivide");
  u = cgetg(n+1, t_COL);
  for (k=1; k<=n; k++)
  {
    b = gel(B,k);
    m = gel(b,k);
    gel(u,k) = dvmdii(m, gcoeff(A,k,k), &r);
    if (r != gen_0) { avma = av; return 0; }
    for (i=k-1; i>0; i--)
    {
      m = gel(b,i);
      for (j=i+1; j<=k; j++) m = subii(m, mulii(gcoeff(A,i,j),gel(u,j)));
      m = dvmdii(m, gcoeff(A,i,i), &r);
      if (r != gen_0) { avma = av; return 0; }
      gel(u,i) = m;
    }
  }
  avma = av; return 1;
}

/* A upper HNF, b integral vector. Return A^(-1) b if integral,
 * NULL otherwise. Assume #A[,1] = #b. */
GEN
hnf_invimage(GEN A, GEN b)
{
  pari_sp av = avma;
  long n = lg(A)-1, m, i, k;
  GEN u, r;

  if (!n) return NULL;
  m = lg(A[1])-1; /* m >= n */
  u = cgetg(n+1, t_COL);
  for (i = n, k = m; k > 0; k--)
  {
    pari_sp av2 = avma;
    long j;
    GEN t = gel(b,k), Aki = gcoeff(A,k,i);
    if (typ(t) != t_INT) pari_err(typeer,"hnf_invimage");
    for (j=i+1; j<=n; j++) t = subii(t, mulii(gcoeff(A,k,j),gel(u,j)));
    if (!signe(Aki))
    {
      if (signe(t)) { avma = av;return NULL; }
      avma = av2; gel(u,i) = gen_0; continue;
    }
    t = dvmdii(t, Aki, &r);
    if (r != gen_0) { avma = av; return NULL; }
    gel(u,i) = gerepileuptoint(av2, t);
    if (--i == 0) break;
  }
  /* If there is a solution, it must be u. Check remaining equations */
  for (; k > 0; k--)
  {
    pari_sp av2 = avma;
    long j;
    GEN t = gel(b,k);
    if (typ(t) != t_INT) pari_err(typeer,"hnf_invimage");
    for (j=1; j<=n; j++) t = subii(t, mulii(gcoeff(A,k,j),gel(u,j)));
    if (signe(t)) { avma = av;return NULL; }
    avma = av2;
  }
  return u;
}

/* A upper HNF, B integral matrix or column. Return A^(-1) B if integral,
 * NULL otherwise */
GEN
hnf_solve(GEN A, GEN B)
{
  pari_sp av;
  long i, l;
  GEN C;

  if (typ(B) == t_COL) return hnf_invimage(A, B);
  av = avma; C = cgetg_copy(B, &l);
  for (i = 1; i < l; i++) {
    GEN c = hnf_invimage(A, gel(B,i));
    if (!c) { avma = av; return NULL; }
    gel(C,i) = c;
  }
  return C;
}

/***************************************************************/
/**                                                           **/
/**               SMITH NORMAL FORM REDUCTION                 **/
/**                                                           **/
/***************************************************************/

static GEN
col_mul(GEN x, GEN c)
{
  if (typ(x) == t_INT)
  {
    long s = signe(x);
    if (!s) return NULL;
    if (is_pm1(x)) return (s > 0)? c: RgC_neg(c);
  }
  return RgC_Rg_mul(c, x);
}

static void
do_zero(GEN x)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) gel(x,i) = gen_0;
}

/* c1 <-- u.c1 + v.c2; c2 <-- a.c2 - b.c1 */
static void
update(GEN u, GEN v, GEN a, GEN b, GEN *c1, GEN *c2)
{
  GEN p1,p2;

  u = col_mul(u,*c1);
  v = col_mul(v,*c2);
  if (u) p1 = v? gadd(u,v): u;
  else   p1 = v? v: NULL;

  a = col_mul(a,*c2);
  b = col_mul(gneg_i(b),*c1);
  if (a) p2 = b? RgC_add(a,b): a;
  else   p2 = b? b: NULL;

  if (!p1) do_zero(*c1); else *c1 = p1;
  if (!p2) do_zero(*c2); else *c2 = p2;
}

static GEN
trivsmith(long all)
{
  GEN z;
  if (!all) return cgetg(1,t_VEC);
  z=cgetg(4,t_VEC);
  gel(z,1) = cgetg(1,t_MAT);
  gel(z,2) = cgetg(1,t_MAT);
  gel(z,3) = cgetg(1,t_MAT); return z;
}

static void
snf_pile(pari_sp av, GEN *x, GEN *U, GEN *V)
{
  GEN *gptr[3];
  int c = 1; gptr[0]=x;
  if (*U) gptr[c++] = U;
  if (*V) gptr[c++] = V;
  gerepilemany(av,gptr,c);
}

static GEN
bezout_step(GEN *pa, GEN *pb, GEN *pu, GEN *pv)
{
  GEN a = *pa, b = *pb, d;
  if (absi_equal(a,b))
  {
    long sa = signe(a), sb = signe(b);
    *pv = gen_0;
    if (sb == sa) {
      *pa = *pb = gen_1;
      if (sa > 0) {*pu=gen_1; return a;} else {*pu=gen_m1; return absi(a);}
    }
    if (sa > 0) { *pa = *pu = gen_1; *pb = gen_m1; return a; }
    *pa = *pu = gen_m1; *pb = gen_1; return b;
  }
  d = bezout(a,b, pu,pv);
  *pa = diviiexact(a, d);
  *pb = diviiexact(b, d); return d;
}

static int
negcmpii(void *E, GEN x, GEN y) { (void)E; return -cmpii(x,y); }

/* Return the SNF D of matrix X. If ptU/ptV non-NULL set them to U/V
 * to that D = UXV */
GEN
ZM_snfall_i(GEN x, GEN *ptU, GEN *ptV, int return_vec)
{
  pari_sp av0 = avma, av, lim = stack_lim(av0,1);
  long i, j, k, m0, m, n0, n;
  GEN p1, u, v, U, V, V0, mdet, ys, perm = NULL;

  n0 = n = lg(x)-1;
  if (!n) {
    if (ptU) *ptU = cgetg(1,t_MAT);
    if (ptV) *ptV = cgetg(1,t_MAT);
    return cgetg(1, return_vec? t_VEC: t_MAT);
  }
  av = avma;
  m0 = m = lg(x[1])-1;

  U = ptU? gen_1: NULL; /* TRANSPOSE of row transform matrix [act on columns]*/
  V = ptV? gen_1: NULL;
  V0 = NULL;
  x = RgM_shallowcopy(x);
  if (m == n && ZM_ishnf(x))
  {
    mdet = ZM_det_triangular(x);
    if (V) *ptV = matid(n);
  }
  else
  {
    mdet = ZM_detmult(x);
    if (signe(mdet))
    {
      if (!V)
        p1 = ZM_hnfmod(x,mdet);
      else
      {
        if (m == n)
        {
          p1 = ZM_hnfmod(x,mdet);
          *ptV = RgM_solve(x,p1);
        }
        else
          p1 = ZM_hnfperm(x, ptV, ptU? &perm: NULL);
      }
      mdet = ZM_det_triangular(p1);
    }
    else
      p1 = ZM_hnfperm(x, ptV, ptU? &perm: NULL);
    x = p1;
  }
  n = lg(x)-1;
  if (V)
  {
    V = *ptV;
    if (n != n0)
    {
      V0 = vecslice(V, 1, n0 - n); /* kernel */
      V  = vecslice(V, n0-n+1, n0);
      av = avma;
    }
  }
  /* independent columns */
  if (!signe(mdet))
  {
    if (n)
    {
      x = ZM_snfall_i(shallowtrans(x), ptV, ptU, return_vec); /* swap ptV,ptU */
      if (typ(x) == t_MAT && n != m) x = shallowtrans(x);
      if (V) V = ZM_mul(V, shallowtrans(*ptV));
      if (U) U = *ptU; /* TRANSPOSE */
    }
    else /* 0 matrix */
    {
      x = cgetg(1,t_MAT);
      if (V) V = cgetg(1, t_MAT);
      if (U) U = matid(m);
    }
    goto THEEND;
  }
  if (U) U = matid(n);

  /* square, maximal rank n */
  p1 = gen_indexsort(RgM_diagonal_shallow(x), NULL, &negcmpii);
  ys = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(ys,j) = vecpermute(gel(x, p1[j]), p1);
  x = ys;
  if (U) U = vecpermute(U, p1);
  if (V) V = vecpermute(V, p1);

  p1 = ZM_hnfmod(x, mdet);
  if (V) V = ZM_mul(V, RgM_solve(x,p1));
  x = p1;

  if (DEBUGLEVEL>7) fprintferr("starting SNF loop");
  for (i=n; i>1; i--)
  {
    if (DEBUGLEVEL>7) fprintferr("\ni = %ld: ",i);
    for(;;)
    {
      int c = 0;
      GEN a, b;
      for (j=i-1; j>=1; j--)
      {
        b = gcoeff(x,i,j); if (!signe(b)) continue;
        a = gcoeff(x,i,i);
        ZC_elem(b, a, x,V, j,i);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if (DEBUGMEM>1) pari_warn(warnmem,"[1]: ZM_snfall i = %ld", i);
          snf_pile(av, &x,&U,&V);
        }
      }
      if (DEBUGLEVEL>7) fprintferr("; ");
      for (j=i-1; j>=1; j--)
      {
        GEN d;
        b = gcoeff(x,j,i); if (!signe(b)) continue;
        a = gcoeff(x,i,i);
        d = bezout_step(&a, &b, &u, &v);
        for (k = 1; k < i; k++)
        {
          GEN t = addii(mulii(u,gcoeff(x,i,k)),mulii(v,gcoeff(x,j,k)));
          gcoeff(x,j,k) = subii(mulii(a,gcoeff(x,j,k)),
                                mulii(b,gcoeff(x,i,k)));
          gcoeff(x,i,k) = t;
        }
        gcoeff(x,j,i) = gen_0;
        gcoeff(x,i,i) = d;
        if (U) update(u,v,a,b,(GEN*)(U+i),(GEN*)(U+j));
        if (low_stack(lim, stack_lim(av,1)))
        {
          if (DEBUGMEM>1) pari_warn(warnmem,"[2]: ZM_snfall, i = %ld", i);
          snf_pile(av, &x,&U,&V);
        }
        c = 1;
      }
      if (!c)
      {
        b = gcoeff(x,i,i); if (!signe(b) || is_pm1(b)) break;

        for (k=1; k<i; k++)
        {
          for (j=1; j<i; j++)
            if (signe(remii(gcoeff(x,k,j),b))) break;
          if (j != i) break;
        }
        if (k == i) break;

        /* x[k,j] != 0 mod b */
        for (j=1; j<=i; j++)
          gcoeff(x,i,j) = addii(gcoeff(x,i,j),gcoeff(x,k,j));
        if (U) gel(U,i) = gadd(gel(U,i),gel(U,k));
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"[3]: ZM_snfall");
        snf_pile(av, &x,&U,&V);
      }
    }
  }
  if (DEBUGLEVEL>7) fprintferr("\n");
  for (k=1; k<=n; k++)
    if (signe(gcoeff(x,k,k)) < 0)
    {
      if (V) ZV_togglesign(gel(V,k));
      togglesign(gcoeff(x,k,k));
    }
THEEND:
  if (return_vec)
  {
    long l = lg(x)-1;
    if (typ(x) == t_MAT) x = RgM_diagonal_shallow(x);
    if (m0 > l) x = shallowconcat(zerovec(m0-l), x);
  }

  if (V0)
  {
    if (!return_vec) x = shallowconcat(zeromat(m,n0-n), x);
    if (V) V = shallowconcat(V0, V);
  }
  if (U)
  {
    U = shallowtrans(U);
    if (perm) U = vecpermute(U, perm_inv(perm));
  }
  snf_pile(av0, &x,&U,&V);
  if (ptU) *ptU = U;
  if (ptV) *ptV = V;
  return x;
}
GEN
ZM_snfall(GEN x, GEN *U, GEN *V) { return ZM_snfall_i(x, U, V, 0); }
GEN
ZM_snf(GEN x) { return ZM_snfall_i(x, NULL,NULL, 1); }

GEN
smith(GEN x) {
  if (typ(x)!=t_MAT) pari_err(typeer,"smith");
  RgM_check_ZM(x, "smith");
  return ZM_snfall_i(x, NULL,NULL, 1);
}
GEN
smithall(GEN x)
{
  GEN z = cgetg(4, t_VEC);
  if (typ(x)!=t_MAT) pari_err(typeer,"smithall");
  RgM_check_ZM(x, "smithall");
  gel(z,3) = ZM_snfall_i(x, (GEN*)(z+1),(GEN*)(z+2), 0);
  return z;
}

void
ZM_snfclean(GEN d, GEN u, GEN v)
{
  long i, c, l = lg(d);

  if (typ(d) == t_VEC)
    for (c=1; c<l; c++) { GEN t = gel(d,c); if (is_pm1(t)) break; }
  else
  {
    for (c=1; c<l; c++) { GEN t = gcoeff(d,c,c); if (is_pm1(t)) break; }
    if (c < l) for (i = 1; i < c; i++) setlg(gel(d,i), c);
  }
  setlg(d, c);
  if (u) for (i=1; i<l; i++) setlg(gel(u,i), c);
  if (v) setlg(v, c);
}

/* Assume z was computed by [g]smithall(). Remove the 1s on the diagonal */
GEN
smithclean(GEN z)
{
  long i,j,l,c;
  GEN u,v,y,d,p1;

  if (typ(z) != t_VEC) pari_err(typeer,"smithclean");
  l = lg(z); if (l == 1) return cgetg(1,t_VEC);
  u=gel(z,1);
  if (l != 4 || typ(u) != t_MAT)
  {
    for (c=1; c<l; c++)
      if (gequal1(gel(z,c))) break;
    return gcopy_lg(z, c);
  }
  v=gel(z,2); d=gel(z,3); l = lg(d);
  for (c=1; c<l; c++)
    if (gequal1(gcoeff(d,c,c))) break;

  y=cgetg(4,t_VEC);
  gel(y,1) = p1 = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(p1,i) = gcopy_lg(gel(u,i), c);
  gel(y,2) = gcopy_lg(v, c);
  gel(y,3) = p1 = cgetg(c,t_MAT);
  for (i=1; i<c; i++)
  {
    GEN p2 = cgetg(c,t_COL); gel(p1,i) = p2;
    for (j=1; j<c; j++) gel(p2,j) = i==j? gcopy(gcoeff(d,i,i)): gen_0;
  }
  return y;
}

INLINE int
is_RgX(GEN a, long v) { return typ(a) == t_POL && varn(a)==v; }

static GEN
gbezout_step(GEN *pa, GEN *pb, GEN *pu, GEN *pv, long vx)
{
  GEN a = *pa, b = *pb, d;
  if (gequal0(a))
  {
    *pa = gen_0; *pu = gen_0;
    *pb = gen_1; *pv = gen_1; return b;
  }
  a = is_RgX(a,vx)? RgX_renormalize(a): scalarpol(a, vx);
  b = is_RgX(b,vx)? RgX_renormalize(b): scalarpol(b, vx);
  d = RgX_extgcd(a,b, pu,pv);
  if (degpol(d)) { a = RgX_div(a, d); b = RgX_div(b, d); }
  else if (typ(d[2]) == t_REAL && lg(d[2]) <= 3)
#if 1
  { /* possible accuracy problem */
    GEN D = RgX_gcd_simple(a,b);
    if (degpol(D)) {
      D = RgX_Rg_div(D, leading_term(D));
      a = RgX_div(a, D);
      b = RgX_div(b, D);
      d = RgX_extgcd(a,b, pu,pv); /* retry now */
      d = RgX_mul(d, D);
    }
  }
#else
  { /* less stable */
    d = RgX_extgcd_simple(a,b, pu,pv);
    if (degpol(d)) { a = RgX_div(a, d); b = RgX_div(b, d); }
  }
#endif
  *pa = a;
  *pb = b; return d;
}

static GEN
gsmithall_i(GEN x,long all)
{
  pari_sp av, lim;
  long i, j, k, n;
  GEN z, u, v, U, V;
  long vx = gvar(x);
  if (typ(x)!=t_MAT) pari_err(typeer,"gsmithall");
  if (vx==NO_VARIABLE) return all?smithall(x):smith(x);
  n = lg(x)-1;
  if (!n) return trivsmith(all);
  if (lg(x[1]) != n+1) pari_err(mattype1,"gsmithall");
  av = avma; lim = stack_lim(av,1);
  x = RgM_shallowcopy(x);
  if (all) { U = matid(n); V = matid(n); }
  for (i=n; i>=2; i--)
  {
    for(;;)
    {
      GEN a, b, d;
      int c = 0;
      for (j=i-1; j>=1; j--)
      {
        b = gcoeff(x,i,j); if (gequal0(b)) continue;
        a = gcoeff(x,i,i);
        d = gbezout_step(&b, &a, &v, &u, vx);
        for (k = 1; k < i; k++)
        {
          GEN t = gadd(gmul(u,gcoeff(x,k,i)),gmul(v,gcoeff(x,k,j)));
          gcoeff(x,k,j) = gsub(gmul(a,gcoeff(x,k,j)),gmul(b,gcoeff(x,k,i)));
          gcoeff(x,k,i) = t;
        }
        gcoeff(x,i,j) = gen_0;
        gcoeff(x,i,i) = d;
        if (all) update(u,v,a,b,(GEN*)(V+i),(GEN*)(V+j));
      }
      for (j=i-1; j>=1; j--)
      {
        b = gcoeff(x,j,i); if (gequal0(b)) continue;
        a = gcoeff(x,i,i);
        d = gbezout_step(&b, &a, &v, &u, vx);
        for (k = 1; k < i; k++)
        {
          GEN t = gadd(gmul(u,gcoeff(x,i,k)),gmul(v,gcoeff(x,j,k)));
          gcoeff(x,j,k) = gsub(gmul(a,gcoeff(x,j,k)),gmul(b,gcoeff(x,i,k)));
          gcoeff(x,i,k) = t;
        }
        gcoeff(x,j,i) = gen_0;
        gcoeff(x,i,i) = d;
        if (all) update(u,v,a,b,(GEN*)(U+i),(GEN*)(U+j));
        c = 1;
      }
      if (!c)
      {
        b = gcoeff(x,i,i); if (!is_RgX(b,vx) || degpol(b)<=0) break;

        for (k=1; k<i; k++)
        {
          for (j=1; j<i; j++)
          {
            GEN z = gcoeff(x,k,j), r;
            if (!is_RgX(z,vx)) z = scalarpol(z, vx);
            r = RgX_rem(z, b);
            if (signe(r) && (! isinexactreal(r) ||
                   gexpo(r) > 16 + gexpo(b) - bit_accuracy(gprecision(r)))
               ) break;
          }
          if (j != i) break;
        }
        if (k == i) break;

        for (j=1; j<=i; j++)
          gcoeff(x,i,j) = gadd(gcoeff(x,i,j),gcoeff(x,k,j));
        if (all) gel(U,i) = gadd(gel(U,i),gel(U,k));
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"gsmithall");
        gerepileall(av, all? 3: 1, &x, &U, &V);
      }
    }
  }
  for (k=1; k<=n; k++)
  {
    GEN T = gcoeff(x,k,k);
    if (is_RgX(T,vx) && signe(T))
    {
      GEN d = leading_term(T);
      while (gequal0(d) || ( typ(d) == t_REAL && lg(d) == 3
                           && gexpo(T) - expo(d) > (long)BITS_IN_LONG)) {
         T = normalizepol_lg(T, lg(T)-1);
         if (!signe(T)) { gcoeff(x,k,k) = T; continue; }
         d = leading_term(T);
      }
      if (!gequal1(d))
      {
        gcoeff(x,k,k) = RgX_Rg_div(T,d);
        if (all) gel(V,k) = RgC_Rg_div(gel(V,k), d);
      }
    }
  }
  z = all? mkvec3(shallowtrans(U), V, x): RgM_diagonal_shallow(x);
  return gerepilecopy(av, z);
}

GEN
matsnf0(GEN x,long flag)
{
  pari_sp av = avma;
  if (flag > 7) pari_err(flagerr,"matsnf");
  if (typ(x) == t_VEC && flag & 4) return smithclean(x);
  if (flag & 2) x = flag&1 ? gsmithall(x): gsmith(x);
  else          x = flag&1 ?  smithall(x):  smith(x);
  if (flag & 4) x = gerepileupto(av, smithclean(x));
  return x;
}

GEN
gsmith(GEN x) { return gsmithall_i(x,0); }

GEN
gsmithall(GEN x) { return gsmithall_i(x,1); }

/* H relation matrix among row of generators g in HNF.  Let URV = D its SNF,
 * newU R newV = newD its clean SNF (no 1 in Dnew). Return the diagonal of
 * newD, newU and newUi such that  1/U = (newUi, ?).
 * Rationale: let (G,0) = g Ui be the new generators then
 * 0 = G U R --> G D = 0,  g = G newU  and  G = g newUi */
GEN
ZM_snf_group(GEN H, GEN *newU, GEN *newUi)
{
  GEN D = ZM_snfall_i(H, newU, newUi, 1);
  long i, j, l;

  ZM_snfclean(D, newU? *newU: NULL, newUi? *newUi: NULL);
  l = lg(D);
  if (newU) {
    GEN U = *newU;
    for (i = 1; i < l; i++)
    {
      GEN d = gel(D,i), d2 = shifti(d, 1);
      for (j = 1; j < lg(U); j++)
        gcoeff(U,i,j) = centermodii(gcoeff(U,i,j), d, d2);
    }
    *newU = U;
  }
  if (newUi) { /* UHV=D -> U^-1 = HVD^-1 -> U^-1 = H(VD^-1 mod 1) mod H */
    if (l > 1)
    { /* Ui = ZM_inv(U, gen_1); setlg(Ui, l); */
      GEN V = FpM_red(*newUi, gel(D,1));
      GEN Ui = ZM_mul(H, V);
      for (i = 1; i < l; i++) gel(Ui,i) = ZC_Z_divexact(gel(Ui,i), gel(D,i));
      *newUi = ZM_hnfrem(Ui, H);
    }
  }
  return D;
}

/***********************************************************************
 ****                                                               ****
 ****         Frobenius form and Jordan form of a matrix            ****
 ****                                                               ****
 ***********************************************************************/

static long
prod_degree(GEN V)
{
  long i, s=0, l = lg(V);
  for (i=1; i<l; i++)
  {
    long d = degpol(gel(V,i));
    if (d<0) return d;
    s += d;
  }
  return s;
}

GEN
Frobeniusform(GEN V, long n)
{
  long i, j, k;
  GEN M = zeromatcopy(n,n);
  for (k=1,i=1;i<lg(V);i++,k++)
  {
    GEN  P = gel(V,i);
    long d = degpol(P);
    if (k+d-1 > n) pari_err(talker, "accuracy lost in matfrobenius");
    for (j=0; j<d-1; j++, k++) gcoeff(M,k+1,k) = gen_1;
    for (j=0; j<d; j++) gcoeff(M,k-j,k) = gneg(gel(P, 1+d-j));
  }
  return M;
}

static GEN
build_frobeniusbc(GEN V, long n)
{
  long i, j, k, l, m = lg(V)-1;
  GEN M = zeromatcopy(n,n), z = monomial(gen_m1, 1, 0); /* -x */
  for (k=1,l=1+m,i=1;i<=m;i++,k++)
  {
    GEN  P = gel(V,i);
    long d = degpol(P);
    if (d <= 0) continue;
    if (l+d-2 > n) pari_err(talker, "accuracy lost in matfrobenius");
    gcoeff(M,k,i) = gen_1;
    for (j=1; j<d; j++,k++,l++)
    {
      gcoeff(M,k,l)   = z;
      gcoeff(M,k+1,l) = gen_1;
    }
  }
  return M;
}

static GEN
build_basischange(GEN N, GEN U)
{
  long i, j, n = lg(N)-1;
  GEN p2 = cgetg(n+1, t_MAT);
  for (j = 1; j <= n; ++j)
  {
    pari_sp btop = avma;
    GEN p3 = NULL;
    for (i = 1; i <= n; ++i)
    {
      GEN Uij = gcoeff(U, i, j), z;
      if (is_RgX(Uij, 0))
        z = RgX_RgM_eval_col(Uij, N, i);
      else
        z = Rg_col_ei(Uij, n, i);
      p3 = p3 ? RgC_add(p3, z):z;
    }
    gel(p2,j) = gerepileupto(btop, p3);
  }
  return p2;
}

GEN
matfrobenius(GEN M, long flag, long v)
{
  pari_sp ltop=avma;
  long n;
  GEN D, A, N, B, R, M_x;
  if (typ(M)!=t_MAT) pari_err(typeer,"matfrobenius");
  if (v<0) v=0;
  if (varncmp(gvar(M), v) <= 0)
    pari_err(talker,"variable must have higher priority in matfrobenius");
  n = lg(M)-1;
  if (n && lg(M[1])!=n+1) pari_err(mattype1,"matfrobenius");
  M_x = RgM_Rg_add_shallow(M, monomial(gen_m1, 1, v));
  if (flag<2)
  {
    D = matsnf0(M_x,6);
    if (prod_degree(D) != n) pari_err(talker, "accuracy lost in matfrobenius");
    if (flag != 1) D = Frobeniusform(D, n);
    return gerepileupto(ltop, D);
  }
  if (flag>2) pari_err(flagerr,"matfrobenius");
  A = matsnf0(M_x,3);
  D = smithclean(RgM_diagonal_shallow(gel(A,3)));
  if (prod_degree(D) != n) pari_err(talker, "accuracy lost in matfrobenius");
  N = Frobeniusform(D, n);
  B = build_frobeniusbc(D, n);
  R = build_basischange(N, RgM_mul(B,gel(A,1)));
  return gerepilecopy(ltop, mkvec2(N,R));
}
