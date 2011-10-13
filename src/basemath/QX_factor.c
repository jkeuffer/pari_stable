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

/* x,y two ZX, y non constant. Return q = x/y if y divides x in Z[X] and NULL
 * otherwise. If not NULL, B is a t_INT upper bound for ||q||_oo. */
static GEN
ZX_divides_i(GEN x, GEN y, GEN B)
{
  long dx, dy, dz, i, j;
  pari_sp av;
  GEN z,p1,y_lead;

  dy=degpol(y);
  dx=degpol(x);
  dz=dx-dy; if (dz<0) return NULL;
  z=cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;
  y_lead = gel(y,dy);
  if (equali1(y_lead)) y_lead = NULL;

  p1 = gel(x,dx);
  if (y_lead) {
    GEN r;
    p1 = dvmdii(p1,y_lead, &r);
    if (r != gen_0) return NULL;
  }
  else p1 = icopy(p1);
  gel(z,dz) = p1;
  for (i=dx-1; i>=dy; i--)
  {
    av = avma; p1 = gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (y_lead) {
      GEN r;
      p1 = dvmdii(p1,y_lead, &r);
      if (r != gen_0) return NULL;
    }
    if (B && absi_cmp(p1, B) > 0) return NULL;
    p1 = gerepileuptoint(av, p1);
    gel(z,i-dy) = p1;
  }
  av = avma;
  for (;; i--)
  {
    p1 = gel(x,i);
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (signe(p1)) return NULL;
    avma = av;
    if (!i) break;
  }
  return z - 2;
}
static GEN
ZX_divides(GEN x, GEN y) { return ZX_divides_i(x,y,NULL); }

#if 0
/* cf Beauzamy et al: upper bound for
 *      lc(x) * [2^(5/8) / pi^(3/8)] e^(1/4n) 2^(n/2) sqrt([x]_2)/ n^(3/8)
 * where [x]_2 = sqrt(\sum_i=0^n x[i]^2 / binomial(n,i)). One factor has
 * all coeffs less than then bound */
static GEN
two_factor_bound(GEN x)
{
  long i, j, n = lg(x) - 3;
  pari_sp av = avma;
  GEN *invbin, c, r = cgetr(3), z;

  x += 2; invbin = (GEN*)new_chunk(n+1);
  z = real_1(LOWDEFAULTPREC); /* invbin[i] = 1 / binomial(n, i) */
  for (i=0,j=n; j >= i; i++,j--)
  {
    invbin[i] = invbin[j] = z;
    z = divru(mulru(z, i+1), n-i);
  }
  z = invbin[0]; /* = 1 */
  for (i=0; i<=n; i++)
  {
    c = gel(x,i); if (!signe(c)) continue;
    affir(c, r);
    z = addrr(z, mulrr(sqrr(r), invbin[i]));
  }
  z = shiftr(sqrtr(z), n);
  z = divrr(z, dbltor(pow((double)n, 0.75)));
  z = roundr_safe(sqrtr(z));
  z = mulii(z, absi(gel(x,n)));
  return gerepileuptoint(av, shifti(z, 1));
}
#endif

/* A | S ==> |a_i| <= binom(d-1, i-1) || S ||_2 + binom(d-1, i) lc(S) */
static GEN
Mignotte_bound(GEN S)
{
  long i, d = degpol(S);
  GEN C, N2, t, binlS, lS = leading_term(S), bin = vecbinome(d-1);

  N2 = sqrtr(RgX_fpnorml2(S,DEFAULTPREC));
  binlS = is_pm1(lS)? bin: ZC_Z_mul(bin, lS);

  /* i = 0 */
  C = gel(binlS,1);
  /* i = d */
  t = N2; if (gcmp(C, t) < 0) C = t;
  for (i = 1; i < d; i++)
  {
    t = addri(mulir(gel(bin,i), N2), gel(binlS,i+1));
    if (mpcmp(C, t) < 0) C = t;
  }
  return C;
}
/* A | S ==> |a_i|^2 <= 3^{3/2 + d} / (4 \pi d) [P]_2^2,
 * where [P]_2 is Bombieri's 2-norm */
static GEN
Beauzamy_bound(GEN S)
{
  const long prec = DEFAULTPREC;
  long i, d = degpol(S);
  GEN bin, lS, s, C;
  bin = vecbinome(d);

  s = real_0(prec);
  for (i=0; i<=d; i++)
  {
    GEN c = gel(S,i+2);
    if (gequal0(c)) continue;
    /* s += P_i^2 / binomial(d,i) */
    s = addrr(s, divri(itor(sqri(c), prec), gel(bin,i+1)));
  }
  /* s = [S]_2^2 */
  C = powruhalf(stor(3,prec), 3 + 2*d); /* 3^{3/2 + d} */
  C = divrr(mulrr(C, s), mulur(4*d, mppi(prec)));
  lS = absi(leading_term(S));
  return mulir(lS, sqrtr(C));
}

static GEN
factor_bound(GEN S)
{
  pari_sp av = avma;
  GEN a = Mignotte_bound(S);
  GEN b = Beauzamy_bound(S);
  if (DEBUGLEVEL>2)
  {
    err_printf("Mignotte bound: %Ps\n",a);
    err_printf("Beauzamy bound: %Ps\n",b);
  }
  return gerepileupto(av, ceil_safe(gmin(a, b)));
}

/* Naive recombination of modular factors: combine up to maxK modular
 * factors, degree <= klim
 *
 * target = polynomial we want to factor
 * famod = array of modular factors.  Product should be congruent to
 * target/lc(target) modulo p^a
 * For true factors: S1,S2 <= p^b, with b <= a and p^(b-a) < 2^31 */
static GEN
cmbf(GEN pol, GEN famod, GEN bound, GEN p, long a, long b,
     long klim, long *pmaxK, int *done)
{
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1;
  ulong spa_b, spa_bs2, Sbound;
  GEN lc, lcpol, pa = powiu(p,a), pas2 = shifti(pa,-1);
  uGEN trace1   = (uGEN)cgetg(lfamod+1, t_VECSMALL);
  uGEN trace2   = (uGEN)cgetg(lfamod+1, t_VECSMALL);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN deg      = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN listmod  = cgetg(lfamod+1, t_COL);
  GEN fa       = cgetg(lfamod+1, t_COL);

  *pmaxK = cmbf_maxK(lfamod);
  lc = absi(leading_term(pol));
  if (is_pm1(lc)) lc = NULL;
  lcpol = lc? ZX_Z_mul(pol, lc): pol;

  {
    GEN pa_b,pa_bs2,pb, lc2 = lc? sqri(lc): NULL;

    pa_b = powiu(p, a-b); /* < 2^31 */
    pa_bs2 = shifti(pa_b,-1);
    pb= powiu(p, b);
    for (i=1; i <= lfamod; i++)
    {
      GEN T1,T2, P = gel(famod,i);
      long d = degpol(P);

      deg[i] = d; P += 2;
      T1 = gel(P,d-1);/* = - S_1 */
      T2 = sqri(T1);
      if (d > 1) T2 = subii(T2, shifti(gel(P,d-2),1));
      T2 = modii(T2, pa); /* = S_2 Newton sum */
      if (lc)
      {
        T1 = Fp_mul(lc, T1, pa);
        T2 = Fp_mul(lc2,T2, pa);
      }
      trace1[i] = itou(diviiround(T1, pb));
      trace2[i] = itou(diviiround(T2, pb));
    }
    spa_b   = (ulong)  pa_b[2]; /* < 2^31 */
    spa_bs2 = (ulong)pa_bs2[2]; /* < 2^31 */
  }
  degsofar[0] = 0; /* sentinel */

  /* ind runs through strictly increasing sequences of length K,
   * 1 <= ind[i] <= lfamod */
nextK:
  if (K > *pmaxK || 2*K > lfamod) goto END;
  if (DEBUGLEVEL > 3)
    err_printf("\n### K = %d, %Ps combinations\n", K,binomial(utoipos(lfamod), K));
  setlg(ind, K+1); ind[1] = 1;
  Sbound = (ulong) ((K+1)>>1);
  i = 1; curdeg = deg[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++)
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += deg[ind[j+1]];
    }
    if (curdeg <= klim) /* trial divide */
    {
      GEN y, q, list;
      pari_sp av;
      ulong t;

      /* d - 1 test */
      for (t=trace1[ind[1]],i=2; i<=K; i++)
        t = Fl_add(t, trace1[ind[i]], spa_b);
      if (t > spa_bs2) t = spa_b - t;
      if (t > Sbound)
      {
        if (DEBUGLEVEL>6) err_printf(".");
        goto NEXT;
      }
      /* d - 2 test */
      for (t=trace2[ind[1]],i=2; i<=K; i++)
        t = Fl_add(t, trace2[ind[i]], spa_b);
      if (t > spa_bs2) t = spa_b - t;
      if (t > Sbound)
      {
        if (DEBUGLEVEL>6) err_printf("|");
        goto NEXT;
      }

      av = avma;
      /* check trailing coeff */
      y = lc;
      for (i=1; i<=K; i++)
      {
        GEN q = constant_term(gel(famod,ind[i]));
        if (y) q = mulii(y, q);
        y = centermodii(q, pa, pas2);
      }
      if (!signe(y) || remii(constant_term(lcpol), y) != gen_0)
      {
        if (DEBUGLEVEL>3) err_printf("T");
        avma = av; goto NEXT;
      }
      y = lc; /* full computation */
      for (i=1; i<=K; i++)
      {
        GEN q = gel(famod,ind[i]);
        if (y) q = gmul(y, q);
        y = centermod_i(q, pa, pas2);
      }

      /* y is the candidate factor */
      if (! (q = ZX_divides_i(lcpol,y,bound)) )
      {
        if (DEBUGLEVEL>3) err_printf("*");
        avma = av; goto NEXT;
      }
      /* found a factor */
      list = cgetg(K+1, t_VEC);
      gel(listmod,cnt) = list;
      for (i=1; i<=K; i++) list[i] = famod[ind[i]];

      y = Q_primpart(y);
      gel(fa,cnt++) = y;
      /* fix up pol */
      pol = q;
      if (lc) pol = Q_div_to_int(pol, leading_term(y));
      for (i=j=k=1; i <= lfamod; i++)
      { /* remove used factors */
        if (j <= K && i == ind[j]) j++;
        else
        {
          famod[k] = famod[i];
          trace1[k] = trace1[i];
          trace2[k] = trace2[i];
          deg[k] = deg[i]; k++;
        }
      }
      lfamod -= K;
      *pmaxK = cmbf_maxK(lfamod);
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = deg[ind[1]];
      bound = factor_bound(pol);
      if (lc) lc = absi(leading_term(pol));
      lcpol = lc? ZX_Z_mul(pol, lc): pol;
      if (DEBUGLEVEL>3)
        err_printf("\nfound factor %Ps\nremaining modular factor(s): %ld\n",
                   y, lfamod);
      continue;
    }

NEXT:
    for (i = K+1;;)
    {
      if (--i == 0) { K++; goto nextK; }
      if (++ind[i] <= lfamod - K + i)
      {
        curdeg = degsofar[i-1] + deg[ind[i]];
        if (curdeg <= klim) break;
      }
    }
  }
END:
  *done = 1;
  if (degpol(pol) > 0)
  { /* leftover factor */
    if (signe(leading_term(pol)) < 0) pol = ZX_neg(pol);
    if (lfamod >= 2*K) *done = 0;

    setlg(famod, lfamod+1);
    gel(listmod,cnt) = leafcopy(famod);
    gel(fa,cnt++) = pol;
  }
  if (DEBUGLEVEL>6) err_printf("\n");
  setlg(listmod, cnt);
  setlg(fa, cnt); return mkvec2(fa, listmod);
}

void
factor_quad(GEN x, GEN res, long *ptcnt)
{
  GEN a = gel(x,4), b = gel(x,3), c = gel(x,2), d, u, z1, z2, t;
  GEN D = subii(sqri(b), shifti(mulii(a,c), 2));
  long v, cnt = *ptcnt;

  if (!Z_issquareall(D, &d)) { gel(res,cnt++) = x; *ptcnt = cnt; return; }

  t = shifti(negi(addii(b, d)), -1);
  z1 = gdiv(t, a); u = denom(z1);
  z2 = gdiv(addii(t, d), a);
  v = varn(x);
  gel(res,cnt++) = gmul(u, gsub(pol_x(v), z1)); u = diviiexact(a, u);
  gel(res,cnt++) = gmul(u, gsub(pol_x(v), z2)); *ptcnt = cnt;
}

/* y > 1 and B > 0 integers. Return e such that y^(e-1) <= B < y^e, i.e
 * e = 1 + floor(log_y B). Set *ptq = y^e if non-NULL */
long
logint(GEN B, GEN y, GEN *ptq)
{
  pari_sp av = avma;
  long e,i,fl;
  GEN q,pow2, r = y;

  if (typ(B) != t_INT) B = ceil_safe(B);
  if (expi(B) <= (expi(y) << 6)) /* e small, be naive */
  {
    for (e=1;; e++)
    { /* here, r = y^e */
      fl = cmpii(r, B);
      if (fl > 0) goto END;
      r = mulii(r,y);
    }
  }
  /* binary splitting: compute bits of e one by one */
  /* compute pow2[i] = y^(2^i) [i < very crude upper bound for log_2(n)] */
  pow2 = new_chunk(expi(B)+1);
  gel(pow2,0) = y;
  for (i=0,q=r;; )
  {
    fl = cmpii(r,B); if (fl >= 0) break;
    q = r; r = sqri(q);
    i++; gel(pow2,i) = r;
  }
  if (i == 0) { e = 1; goto END; } /* y <= B */

  for (i--, e=1L<<i;;)
  { /* y^e = q < B <= r = q * y^(2^i) */
    if (!fl) break; /* B = r */
    /* q < B < r */
    if (--i < 0) { if (fl > 0) e++; break; }
    r = mulii(q, gel(pow2,i));
    fl = cmpii(r, B);
    if (fl <= 0) { e += (1L<<i); q = r; }
  }
  if (fl <= 0) { e++; r = mulii(r,y); }
END:
  if (ptq) *ptq = gerepileuptoint(av, icopy(r)); else avma = av;
  return e;
}

/* recombination of modular factors: van Hoeij's algorithm */

/* Q in Z[X], return Q(2^n) */
static GEN
shifteval(GEN Q, long n)
{
  long i, l = lg(Q);
  GEN s;

  if (!signe(Q)) return gen_0;
  s = gel(Q,l-1);
  for (i = l-2; i > 1; i--) s = addii(gel(Q,i), shifti(s, n));
  return s;
}

/* return integer y such that all |a| <= y if P(a) = 0 */
static GEN
root_bound(GEN P0)
{
  GEN Q = leafcopy(P0), lP = absi(leading_term(Q)), x,y,z;
  long k, d = degpol(Q);

  /* P0 = lP x^d + Q, deg Q < d */
  Q = normalizepol_lg(Q, d+2);
  for (k=lg(Q)-1; k>1; k--) gel(Q,k) = absi(gel(Q,k));
  k = (long)(cauchy_bound(P0) / LOG2);
  for (  ; k >= 0; k--)
  {
    pari_sp av = avma;
    /* y = 2^k; Q(y) >= lP y^d ? */
    if (cmpii(shifteval(Q,k), shifti(lP, d*k)) >= 0) break;
    avma = av;
  }
  if (k < 0) k = 0;
  x = int2n(k);
  y = int2n(k+1);
  for(k=0; ; k++)
  {
    z = shifti(addii(x,y), -1);
    if (equalii(x,z) || k > 5) break;
    if (cmpii(poleval(Q,z), mulii(lP, powiu(z, d))) < 0)
      y = z;
    else
      x = z;
  }
  return y;
}

GEN
special_pivot(GEN x)
{
  GEN t, perm, H = ZM_hnfperm(x,NULL,&perm);
  long i,j, l = lg(H), h = lg(H[1]);
  for (i=1; i<h; i++)
  {
    int fl = 0;
    for (j=1; j<l; j++)
    {
      t = gcoeff(H,i,j);
      if (signe(t))
      {
        if (!is_pm1(t) || fl) return NULL;
        fl = 1;
      }
    }
  }
  return rowpermute(H, perm_inv(perm));
}

GEN
chk_factors_get(GEN lt, GEN famod, GEN c, GEN T, GEN N)
{
  long i = 1, j, l = lg(famod);
  GEN V = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
    if (signe(c[j])) V[i++] = famod[j];
  if (lt && i > 1) gel(V,1) = RgX_Rg_mul(gel(V,1), lt);
  setlg(V, i);
  return T? FpXQXV_prod(V, T, N): FpXV_prod(V,N);
}

static GEN
chk_factors(GEN P, GEN M_L, GEN bound, GEN famod, GEN pa)
{
  long i, r;
  GEN pol = P, list, piv, y, ltpol, lt, paov2;

  piv = special_pivot(M_L);
  if (!piv) return NULL;
  if (DEBUGLEVEL>7) err_printf("special_pivot output:\n%Ps\n",piv);

  r  = lg(piv)-1;
  list = cgetg(r+1, t_COL);
  lt = absi(leading_term(pol));
  if (is_pm1(lt)) lt = NULL;
  ltpol = lt? ZX_Z_mul(pol, lt): pol;
  paov2 = shifti(pa,-1);
  for (i = 1;;)
  {
    if (DEBUGLEVEL) err_printf("LLL_cmbf: checking factor %ld\n",i);
    y = chk_factors_get(lt, famod, gel(piv,i), NULL, pa);
    y = FpX_center(y, pa, paov2);
    if (! (pol = ZX_divides_i(ltpol,y,bound)) ) return NULL;
    if (lt) y = Q_primpart(y);
    gel(list,i) = y;
    if (++i >= r) break;

    if (lt)
    {
      pol = ZX_Z_divexact(pol, leading_term(y));
      lt = absi(leading_term(pol));
      ltpol = ZX_Z_mul(pol, lt);
    }
    else
      ltpol = pol;
  }
  y = Q_primpart(pol);
  gel(list,i) = y; return list;
}

GEN
LLL_check_progress(GEN Bnorm, long n0, GEN m, int final, long *ti_LLL)
{
  GEN norm, u;
  long i, R;
  pari_timer T;

  if (DEBUGLEVEL>2) timer_start(&T);
  u = ZM_lll_norms(m, final? 0.999: 0.75, LLL_INPLACE, &norm);
  if (DEBUGLEVEL>2) *ti_LLL += timer_delay(&T);
  for (R=lg(m)-1; R > 0; R--)
    if (cmprr(gel(norm,R), Bnorm) < 0) break;
  for (i=1; i<=R; i++) setlg(u[i], n0+1);
  if (R <= 1)
  {
    if (!R) pari_err_BUG("LLL_cmbf [no factor]");
    return NULL; /* irreducible */
  }
  setlg(u, R+1); return u;
}

static ulong
next2pow(ulong a)
{
  ulong b = 1;
  while (b < a) b <<= 1;
  return b;
}

/* Recombination phase of Berlekamp-Zassenhaus algorithm using a variant of
 * van Hoeij's knapsack
 *
 * P = squarefree in Z[X].
 * famod = array of (lifted) modular factors mod p^a
 * bound = Mignotte bound for the size of divisors of P (for the sup norm)
 * previously recombined all set of factors with less than rec elts */
static GEN
LLL_cmbf(GEN P, GEN famod, GEN p, GEN pa, GEN bound, long a, long rec)
{
  const long N0 = 1; /* # of traces added at each step */
  double BitPerFactor = 0.4; /* nb bits in p^(a-b) / modular factor */
  long i,j,tmax,n0,C, dP = degpol(P);
  double logp = log((double)itos(p)), LOGp2 = LOG2/logp;
  double b0 = log((double)dP*2) / logp, logBr;
  GEN lP, Br, Bnorm, Tra, T2, TT, CM_L, m, list, ZERO;
  pari_sp av, av2, lim;
  long ti_LLL = 0, ti_CF  = 0;

  lP = absi(leading_term(P));
  if (is_pm1(lP)) lP = NULL;
  Br = root_bound(P);
  if (lP) Br = mulii(lP, Br);
  logBr = gtodouble(glog(Br, DEFAULTPREC)) / logp;

  n0 = lg(famod) - 1;
  C = (long)ceil( sqrt(N0 * n0 / 4.) ); /* > 1 */
  Bnorm = dbltor(n0 * (C*C + N0*n0/4.) * 1.00001);
  ZERO = zeromat(n0, N0);

  av = avma; lim = stack_lim(av, 1);
  TT = cgetg(n0+1, t_VEC);
  Tra  = cgetg(n0+1, t_MAT);
  for (i=1; i<=n0; i++)
  {
    TT[i]  = 0;
    gel(Tra,i) = cgetg(N0+1, t_COL);
  }
  CM_L = scalarmat_s(C, n0);
  /* tmax = current number of traces used (and computed so far) */
  for (tmax = 0;; tmax += N0)
  {
    long b, bmin, bgood, delta, tnew = tmax + N0, r = lg(CM_L)-1;
    GEN M_L, q, CM_Lp, oldCM_L;
    int first = 1;
    pari_timer ti2, TI;

    bmin = (long)ceil(b0 + tnew*logBr);
    if (DEBUGLEVEL>2)
      err_printf("\nLLL_cmbf: %ld potential factors (tmax = %ld, bmin = %ld)\n",
                 r, tmax, bmin);

    /* compute Newton sums (possibly relifting first) */
    if (a <= bmin)
    {
      a = (long)ceil(bmin + 3*N0*logBr) + 1; /* enough for 3 more rounds */
      a = (long)next2pow((ulong)a);

      pa = powiu(p,a);
      famod = ZpX_liftfact(P,famod,NULL,p,a,pa);
      for (i=1; i<=n0; i++) TT[i] = 0;
    }
    for (i=1; i<=n0; i++)
    {
      GEN p1 = gel(Tra,i);
      GEN p2 = polsym_gen(gel(famod,i), gel(TT,i), tnew, NULL, pa);
      gel(TT,i) = p2;
      p2 += 1+tmax; /* ignore traces number 0...tmax */
      for (j=1; j<=N0; j++) p1[j] = p2[j];
      if (lP)
      { /* make Newton sums integral */
        GEN lPpow = powiu(lP, tmax);
        for (j=1; j<=N0; j++)
        {
          lPpow = mulii(lPpow,lP);
          gel(p1,j) = mulii(gel(p1,j), lPpow);
        }
      }
    }

    /* compute truncation parameter */
    if (DEBUGLEVEL>2) { timer_start(&ti2); timer_start(&TI); }
    oldCM_L = CM_L;
    av2 = avma;
    delta = b = 0; /* -Wall */
AGAIN:
    M_L = Q_div_to_int(CM_L, utoipos(C));
    T2 = centermod( ZM_mul(Tra, M_L), pa );
    if (first)
    { /* initialize lattice, using few p-adic digits for traces */
      double t = gexpo(T2) - maxdd(32.0, BitPerFactor*r);
      bgood = (long) (t * LOGp2);
      b = maxss(bmin, bgood);
      delta = a - b;
    }
    else
    { /* add more p-adic digits and continue reduction */
      long b0 = (long)(gexpo(T2) * LOGp2);
      if (b0 < b) b = b0;
      b = maxss(b-delta, bmin);
      if (b - delta/2 < bmin) b = bmin; /* near there. Go all the way */
    }

    q = powiu(p, b);
    m = vconcat( CM_L, gdivround(T2, q) );
    if (first)
    {
      GEN P1 = scalarmat(powiu(p, a-b), N0);
      first = 0;
      m = shallowconcat( m, vconcat(ZERO, P1) );
      /*     [ C M_L        0     ]
       * m = [                    ]   square matrix
       *     [  T2'  p^(a-b) I_N0 ]   T2' = Tra * M_L  truncated
       */
    }

    CM_L = LLL_check_progress(Bnorm, n0, m, b == bmin, /*dbg:*/ &ti_LLL);
    if (DEBUGLEVEL>2)
      err_printf("LLL_cmbf: (a,b) =%4ld,%4ld; r =%3ld -->%3ld, time = %ld\n",
                 a,b, lg(m)-1, CM_L? lg(CM_L)-1: 1, timer_delay(&TI));
    if (!CM_L) { list = mkcol(P); break; }
    if (b > bmin)
    {
      CM_L = gerepilecopy(av2, CM_L);
      goto AGAIN;
    }
    if (DEBUGLEVEL>2) timer_printf(&ti2, "for this block of traces");

    i = lg(CM_L) - 1;
    if (i == r && ZM_equal(CM_L, oldCM_L))
    {
      CM_L = oldCM_L;
      avma = av2; continue;
    }

    CM_Lp = FpM_image(CM_L, utoipos(27449)); /* inexpensive test */
    if (lg(CM_Lp) != lg(CM_L))
    {
      if (DEBUGLEVEL>2) err_printf("LLL_cmbf: rank decrease\n");
      CM_L = ZM_hnf(CM_L);
    }

    if (i <= r && i*rec < n0)
    {
      pari_timer ti;
      if (DEBUGLEVEL>2) timer_start(&ti);
      list = chk_factors(P, Q_div_to_int(CM_L,utoipos(C)), bound, famod, pa);
      if (DEBUGLEVEL>2) ti_CF += timer_delay(&ti);
      if (list) break;
      if (DEBUGLEVEL>2) err_printf("LLL_cmbf: chk_factors failed");
    }
    CM_L = gerepilecopy(av2, CM_L);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"LLL_cmbf");
      gerepileall(av, 5, &CM_L, &TT, &Tra, &famod, &pa);
    }
  }
  if (DEBUGLEVEL>2)
    err_printf("* Time LLL: %ld\n* Time Check Factor: %ld\n",ti_LLL,ti_CF);
  return list;
}

/* Find a,b minimal such that A < q^a, B < q^b, 1 << q^(a-b) < 2^31 */
static int
cmbf_precs(GEN q, GEN A, GEN B, long *pta, long *ptb, GEN *qa, GEN *qb)
{
  long a,b,amin,d = (long)(31 * LOG2/gtodouble(glog(q,DEFAULTPREC)) - 1e-5);
  int fl = 0;

  b = logint(B, q, qb);
  amin = b + d;
  if (gcmp(powiu(q, amin), A) <= 0)
  {
    a = logint(A, q, qa);
    b = a - d; *qb = powiu(q, b);
  }
  else
  { /* not enough room */
    a = amin;  *qa = powiu(q, a);
    fl = 1;
  }
  if (DEBUGLEVEL > 3) {
    err_printf("S_2   bound: %Ps^%ld\n", q,b);
    err_printf("coeff bound: %Ps^%ld\n", q,a);
  }
  *pta = a;
  *ptb = b; return fl;
}

/* use van Hoeij's knapsack algorithm */
static GEN
combine_factors(GEN target, GEN famod, GEN p, long klim)
{
  GEN la, B, A, res, L, pa, pb, listmod;
  long a,b, l, maxK, n = degpol(target);
  int done;
  pari_timer T;

  A = factor_bound(target);

  la = absi(leading_term(target));
  B = mului(n, sqri(mulii(la, root_bound(target)))); /* = bound for S_2 */

  (void)cmbf_precs(p, A, B, &a, &b, &pa, &pb);

  if (DEBUGLEVEL>2) timer_start(&T);
  famod = ZpX_liftfact(target,famod,NULL,p,a,pa);
  if (DEBUGLEVEL>2) timer_printf(&T, "Hensel lift (mod %Ps^%ld)", p,a);
  L = cmbf(target, famod, A, p, a, b, klim, &maxK, &done);
  if (DEBUGLEVEL>2) timer_printf(&T, "Naive recombination");

  res     = gel(L,1);
  listmod = gel(L,2); l = lg(listmod)-1;
  famod = gel(listmod,l);
  if (maxK >= 0 && lg(famod)-1 > 2*maxK)
  {
    if (l!=1) A = factor_bound(gel(res,l));
    if (DEBUGLEVEL > 4) err_printf("last factor still to be checked\n");
    L = LLL_cmbf(gel(res,l), famod, p, pa, A, a, maxK);
    if (DEBUGLEVEL>2) timer_printf(&T,"Knapsack");
    /* remove last elt, possibly unfactored. Add all new ones. */
    setlg(res, l); res = shallowconcat(res, L);
  }
  return res;
}

/* assume pol(0) != 0, polp = pol/lc(pol) mod p.
 * Return vector of rational roots of a */
GEN
DDF_roots(GEN pol, GEN polp, GEN p)
{
  GEN lc, lcpol, z, pe, pes2, bound;
  long i, m, e, lz, v = varn(pol);
  pari_sp av, lim;
  pari_timer T;

  if (DEBUGLEVEL>2) timer_start(&T);
  lc = absi(leading_term(pol));
  if (is_pm1(lc)) lc = NULL;
  lcpol = lc? ZX_Z_mul(pol, lc): pol;

  bound = root_bound(pol);
  if (lc) bound = mulii(lc, bound);
  e = logint(addis(shifti(bound, 1), 1), p, &pe);
  pes2 = shifti(pe, -1);
  if (DEBUGLEVEL>2) timer_printf(&T, "Root bound");

  av = avma; lim = stack_lim(av,2);
  z = FpX_roots(polp, p);
  lz = lg(z)-1;
  if (lz > (degpol(pol) >> 2))
  { /* many roots */
    z = shallowconcat(deg1_from_roots(z, v),
                 FpX_div(polp, FpV_roots_to_pol(z, p, v), p));
    z = ZpX_liftfact(pol, z, NULL, p, e, pe);
  }
  else
  {
    z = ZpX_liftroots(pol, z, p, e);
    z = deg1_from_roots(z, v);
  }
  if (DEBUGLEVEL>2) timer_printf(&T, "Hensel lift (mod %Ps^%ld)", p,e);

  for (m=1, i=1; i <= lz; i++)
  {
    GEN q, r, y = gel(z,i);
    if (lc) y = ZX_Z_mul(y, lc);
    y = centermod_i(y, pe, pes2);
    if (! (q = ZX_divides(lcpol, y)) ) continue;

    lcpol = pol = q;
    r = negi( constant_term(y) );
    if (lc) {
      r = gdiv(r,lc);
      pol = Q_primpart(pol);
      lc = absi( leading_term(pol) );
      if (is_pm1(lc)) lc = NULL; else lcpol = ZX_Z_mul(pol, lc);
    }
    gel(z,m++) = r;
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"DDF_roots, m = %ld", m);
      gerepileall(av, lc? 4:2, &z, &pol, &lc, &lcpol);

    }
  }
  if (DEBUGLEVEL>2) timer_printf(&T, "Recombination");
  z[0] = evaltyp(t_VEC) | evallg(m); return z;
}

/* Assume a squarefree, degree(a) > 0, a(0) != 0.
 * If fl != 0 look only for rational roots */
static GEN
DDF(GEN a, int fl)
{
  GEN lead, prime, famod, z, ap;
  const long da = degpol(a);
  long chosenp, p, nfacp, np, nmax, ti = 0;
  pari_sp av = avma, av1;
  byteptr pt = diffptr;
  const long MAXNP = 7;
  pari_timer T, T2;

  if (DEBUGLEVEL>2) { timer_start(&T); timer_start(&T2); }
  nmax = da+1;
  chosenp = 0;
  lead = gel(a,da+2); if (equali1(lead)) lead = NULL;
  av1 = avma;
  for (p = np = 0; np < MAXNP; avma = av1)
  {
    NEXT_PRIME_VIADIFF_CHECK(p,pt);
    if (lead && !smodis(lead,p)) continue;
    z = ZX_to_Flx(a, p);
    if (!Flx_is_squarefree(z, p)) continue;

    nfacp = fl? Flx_nbroots(z, p): Flx_nbfact(z, p);
    if (DEBUGLEVEL>4)
      err_printf("...tried prime %3ld (%-3ld %s). Time = %ld\n",
                  p, nfacp, fl?"roots": "factors", timer_delay(&T2));
    if (nfacp < nmax)
    {
      if (nfacp <= 1)
      {
        if (!fl) { avma = av; return mkcol(a); } /* irreducible */
        if (!nfacp) return cgetg(1, t_VEC); /* no root */
      }
      nmax = nfacp; chosenp = p;
      if (da > 100 && nmax < 5) break; /* large degree, few factors. Enough */
    }
    np++;
  }
  prime = utoipos(chosenp);
  ap = lead? FpX_normalize(a, prime): FpX_red(a, prime);
  if (fl) return gerepilecopy(av, DDF_roots(a, ap, prime));

  famod = cgetg(nmax+1,t_COL);
  gel(famod,1) = ap;
  if (nmax != FpX_split_Berlekamp((GEN*)(famod+1), prime))
    pari_err_BUG("DDF: wrong numbers of factors");
  if (DEBUGLEVEL>2)
  {
    if (DEBUGLEVEL>4) timer_printf(&T2, "splitting mod p = %ld", chosenp);
    ti = timer_delay(&T);
    err_printf("Time setup: %ld\n", ti);
  }
  z = combine_factors(a, famod, prime, da-1);
  if (DEBUGLEVEL>2)
    err_printf("Total Time: %ld\n===========\n", ti + timer_delay(&T));
  return gerepilecopy(av, z);
}

/* Distinct Degree Factorization (deflating first)
 * Assume x squarefree, degree(x) > 0, x(0) != 0 */
GEN
ZX_DDF(GEN x)
{
  GEN L;
  long m;
  x = RgX_deflate_max(x, &m);
  L = DDF(x, 0);
  if (m > 1)
  {
    GEN e, v, fa = factoru(m);
    long i,j,k, l;

    e = gel(fa,2); k = 0;
    fa= gel(fa,1); l = lg(fa);
    for (i=1; i<l; i++) k += e[i];
    v = cgetg(k+1, t_VECSMALL); k = 1;
    for (i=1; i<l; i++)
      for (j=1; j<=e[i]; j++) v[k++] = fa[i];
    for (k--; k; k--)
    {
      GEN L2 = cgetg(1,t_VEC);
      for (i=1; i < lg(L); i++)
              L2 = shallowconcat(L2, DDF(RgX_inflate(gel(L,i), v[k]), 0));
      L = L2;
    }
  }
  return L;
}

/* SquareFree Factorization. f = prod P^e, all e distinct, in Z[X] (char 0
 * would be enough, if ZX_gcd --> ggcd). Return (P), set *ex = (e) */
GEN
ZX_squff(GEN f, GEN *ex)
{
  GEN T, V, W, P, e;
  long i, k, dW, n, val;

  if (signe(leading_term(f)) < 0) f = gneg_i(f);
  val = ZX_valrem(f, &f);
  n = 1 + degpol(f); if (val) n++;
  e = cgetg(n,t_VECSMALL);
  P = cgetg(n,t_COL);

  T = ZX_gcd_all(f, ZX_deriv(f), &V);
  for (k=i=1;; k++)
  {
    W = ZX_gcd_all(T,V, &T); dW = degpol(W);
    /* W = prod P^e, e > k; V = prod P^e, e >= k */
    if (dW != degpol(V)) { gel(P,i) = Q_primpart(RgX_div(V,W)); e[i] = k; i++; }
    if (dW <= 0) break;
    V = W;
  }
  if (val) { gel(P,i) = pol_x(varn(f)); e[i] = val; i++;}
  setlg(P,i);
  setlg(e,i); *ex = e; return P;
}

GEN
fact_from_DDF(GEN fa, GEN e, long n)
{
  GEN v,w, y = cgetg(3, t_MAT);
  long i,j,k, l = lg(fa);

  v = cgetg(n+1,t_COL); gel(y,1) = v;
  w = cgetg(n+1,t_COL); gel(y,2) = w;
  for (k=i=1; i<l; i++)
  {
    GEN L = gel(fa,i), ex = utoipos(e[i]);
    long J = lg(L);
    for (j=1; j<J; j++,k++)
    {
      gel(v,k) = gcopy(gel(L,j));
      gel(w,k) = ex;
    }
  }
  return y;
}

/* Factor x in Z[t] */
static GEN
ZX_factor_i(GEN x)
{
  GEN fa,ex,y;
  long n,i,l;

  if (!signe(x)) return zero_fact(x);
  fa = ZX_squff(x, &ex);
  l = lg(fa); n = 0;
  for (i=1; i<l; i++)
  {
    gel(fa,i) = ZX_DDF(gel(fa,i));
    n += lg(fa[i])-1;
  }
  y = fact_from_DDF(fa,ex,n);
  return sort_factor_pol(y, cmpii);
}
GEN
ZX_factor(GEN x)
{
  pari_sp av = avma;
  return gerepileupto(av, ZX_factor_i(x));
}
GEN
QX_factor(GEN x)
{
  pari_sp av = avma;
  return gerepileupto(av, ZX_factor_i(Q_primpart(x)));
}

long
ZX_is_irred(GEN x)
{
  pari_sp av = avma;
  long l = lg(x);
  GEN y;
  if (l <= 3) return 0; /* degree < 1 */
  if (l == 4) return 1; /* degree 1 */
  if (ZX_val(x)) return 0;
  if (!ZX_is_squarefree(x)) return 0;
  y = ZX_DDF(x); avma = av;
  return (lg(y) == 2);
}

GEN
nfrootsQ(GEN x)
{
  pari_sp av = avma;
  GEN z;
  long val;

  if (typ(x)!=t_POL) pari_err_TYPE("nfrootsQ",x);
  if (!signe(x)) pari_err_ZEROPOL("nfrootsQ");
  x = Q_primpart(x);
  if (!RgX_is_ZX(x)) pari_err_TYPE("nfrootsQ",x);
  val = ZX_valrem(x, &x);
  (void)ZX_gcd_all(x, ZX_deriv(x), &x);
  z = DDF(x, 1);
  if (val) z = shallowconcat(z, gen_0);
  return gerepilecopy(av, z);
}

/************************************************************************
 *                   GCD OVER Z[X] / Q[X]                               *
 ************************************************************************/
int
ZX_is_squarefree(GEN x)
{
  pari_sp av = avma;
  GEN d = ZX_gcd(x,ZX_deriv(x));
  int r = (lg(d) == 3); avma = av; return r;
}

#if 0
/* ceil( || p ||_oo / lc(p) ) */
static GEN
maxnorm(GEN p)
{
  long i, n = degpol(p), av = avma;
  GEN x, m = gen_0;

  p += 2;
  for (i=0; i<n; i++)
  {
    x = gel(p,i);
    if (absi_cmp(x,m) > 0) m = x;
  }
  m = divii(m, gel(p,n));
  return gerepileuptoint(av, addis(absi(m),1));
}
#endif

/* A, B in Z[X] */
GEN
ZX_gcd_all(GEN A, GEN B, GEN *Anew)
{
  GEN R, a, b, q, qp, H, Hp, g, Ag, Bg;
  long m, n, valX, valA, vA = varn(A);
  ulong p;
  pari_sp ltop, av, avlim;
  byteptr d;

  if (!signe(A)) { if (Anew) *Anew = pol_0(vA); return ZX_copy(B); }
  if (!signe(B)) { if (Anew) *Anew = pol_1(vA); return ZX_copy(A); }
  valA = ZX_valrem(A, &A);
  valX = minss(valA, ZX_valrem(B, &B));
  ltop = avma;

  n = 1 + minss(degpol(A), degpol(B)); /* > degree(gcd) */
  g = gcdii(leading_term(A), leading_term(B)); /* multiple of lead(gcd) */
  if (is_pm1(g)) {
    g = NULL;
    Ag = A;
    Bg = B;
  } else {
    Ag = ZX_Z_mul(A,g);
    Bg = ZX_Z_mul(B,g);
  }

  av = avma; avlim = stack_lim(av, 1);
  H = NULL; d = init_modular(&p);
  for(;;)
  {
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    if (g && !umodiu(g,p)) continue;
    a = ZX_to_Flx(A, p);
    b = ZX_to_Flx(B, p); Hp = Flx_gcd(a,b, p);
    m = degpol(Hp);
    if (m == 0) { /* coprime. DONE */
      avma = ltop;
      if (Anew) {
        if (valA != valX) A = RgX_shift(A, valA - valX);
        *Anew = A;
      }
      return monomial(gen_1, valX, vA);
    }
    if (m > n) continue; /* p | Res(A/G, B/G). Discard */

    if (!g) /* make sure lead(H) = g mod p */
      Hp = Flx_normalize(Hp, p);
    else
    {
      ulong t = Fl_mul(umodiu(g, p), Fl_inv(Hp[m+2],p), p);
      Hp = Flx_Fl_mul(Hp, t, p);
    }
    if (m < n)
    { /* First time or degree drop [all previous p were as above; restart]. */
      H = ZX_init_CRT(Hp,p,vA);
      q = utoipos(p); n = m; continue;
    }
    if (DEBUGLEVEL>5) err_printf("gcd mod %lu (bound 2^%ld)\n", p,expi(q));
    if (low_stack(avlim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"QX_gcd");
      gerepileall(av, 3, &H, &q, &Hp);
    }

    qp = muliu(q,p);
    if (!ZX_incremental_CRT(&H, Hp, q, qp, p)) { q = qp; continue; }
    /* H stable: check divisibility */
    q = qp;
    if (!ZX_divides(Bg, H)) continue;
    R = ZX_divides(Ag, H);
    if (!R) continue;
    if (Anew) {
      A = R;
      if (valA != valX) A = RgX_shift(A, valA - valX);
      *Anew = A;
    }
    return valX ? RgX_shift(H, valX): H;
  }
}
GEN
ZX_gcd(GEN A, GEN B) { return ZX_gcd_all(A,B,NULL); }

static GEN
_gcd(GEN a, GEN b)
{
  if (!a) a = gen_1;
  if (!b) b = gen_1;
  return Q_gcd(a,b);
}
/* A0 and B0 in Q[X] */
GEN
QX_gcd(GEN A0, GEN B0)
{
  GEN a, b, D;
  pari_sp av = avma, av2;

  D = ZX_gcd(Q_primitive_part(A0, &a), Q_primitive_part(B0, &b));
  av2 = avma; a = _gcd(a,b);
  if (isint1(a)) avma = av2; else D = RgX_Rg_mul(D, a);
  return gerepileupto(av, D);
}
