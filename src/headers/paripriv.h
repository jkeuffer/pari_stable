/* $Id$

Copyright (C) 2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/* for qsort */
typedef int (*QSCOMP)(const void *, const void *);

/* swap */
#define lswap(x,y) {long _z=x; x=y; y=_z;}
#define pswap(x,y) {GEN *_z=x; x=y; y=_z;}
#define swap(x,y)  {GEN  _z=x; x=y; y=_z;}
#define dswap(x,y) { double _t=x; x=y; y=_t; }
#define pdswap(x,y) { double* _t=x; x=y; y=_t; }
#define swapspec(x,y, nx,ny) {swap(x,y); lswap(nx,ny);}

/* */
#define both_odd(x,y) ((x)&(y)&1)

/* generic */
GEN arith_proto(long f(GEN), GEN x, int do_error);
GEN arith_proto2(long f(GEN,GEN), GEN x, GEN n);
GEN arith_proto2gs(long f(GEN,long), GEN x, long y);
GEN garith_proto(GEN f(GEN), GEN x, int do_error);
GEN garith_proto2gs(GEN f(GEN,long), GEN x, long y);
GEN trans_fix_arg(long *prec, GEN *s0, GEN *sig, pari_sp *av, GEN *res);
GEN transc(GEN (*f) (GEN, long), GEN x, long prec);

/* loops */
GEN incloop(GEN a);
GEN incpos(GEN a);
GEN resetloop(GEN a, GEN b);
GEN setloop(GEN a);

/* "abs" routines for t_REAL ( disregard sign ) */
int absrnz_egal1(GEN x);
int absrnz_egal2n(GEN x);
GEN exp1r_abs(GEN x);
GEN logagmr_abs(GEN q);
GEN logr_abs(GEN x);
GEN sqrtr_abs(GEN x);

/* hnf */
GEN gauss_triangle_i(GEN A, GEN B,GEN t);
GEN hnfadd(GEN m,GEN p,GEN* ptdep,GEN* ptA,GEN* ptC,GEN extramat,GEN extraC);
GEN hnfadd_i(GEN m,GEN p,GEN* ptdep,GEN* ptA,GEN* ptC,GEN extramat,GEN extraC);
GEN hnfall_i(GEN A, GEN *ptB, long remove);
GEN hnf_gauss(GEN A, GEN B);
GEN hnf_invimage(GEN A, GEN b);
GEN hnfmerge_get_1(GEN A, GEN B);
GEN hnfperm_i(GEN A, GEN *ptU, GEN *ptperm);
GEN hnfspec_i(long** m,GEN p,GEN* ptdep,GEN* ptA,GEN* ptC,long k0);
GEN hnfspec(long** m,GEN p,GEN* ptdep,GEN* ptA,GEN* ptC,long k0);
GEN idealhermite_aux(GEN nf, GEN x);
GEN mathnfspec(GEN x, GEN *ptperm, GEN *ptdep, GEN *ptB, GEN *ptC);

/* LLL */
GEN lllint_fp_ip(GEN x, long D);
GEN lllfp_marked(long *M, GEN x, long D, long flag, long prec, int gram);
GEN lllint_marked(long *M, GEN x, long D, int g, GEN *h, GEN *f, GEN *B);
GEN LLL_check_progress(GEN Bnorm, long n0, GEN m, int final, long *ti_LLL);

/* other linear algebra */
GEN imagecomplspec(GEN x, long *nlze);

/* famat */
GEN famat_inv(GEN f);
GEN famat_makecoprime(GEN nf, GEN g, GEN e, GEN pr, GEN prk, GEN EX);
GEN famat_mul(GEN f, GEN g);
GEN famat_mul(GEN f, GEN g);
GEN famat_pow(GEN f, GEN n);
GEN famat_reduce(GEN fa);
GEN famat_to_arch(GEN nf, GEN fa, long prec);
GEN famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id, GEN EX);
GEN famat_to_nf_modidele(GEN nf, GEN g, GEN e, GEN bid);
GEN famat_to_nf_modidele(GEN nf, GEN g, GEN e, GEN bid);
GEN to_famat_all(GEN x, GEN y);
GEN to_famat(GEN g, GEN e);

GEN trivfact(void);
GEN vconcat(GEN Q1, GEN Q2);

GEN _checkbnf(GEN bnf);
GEN _checknf(GEN nf);

/* powers & floats */
#define sqrs(b) mulss((b),(b))
#define sqru(b) muluu((b),(b))
ulong usqrtsafe(ulong a);
ulong dblmantissa(double x);
GEN ishiftr_spec(GEN x, long lx, long n);
GEN rpowuu(ulong a, ulong n, long prec);
GEN powrshalf(GEN x, long s);
GEN powrfrac(GEN x, long n, long d);
ulong u_pow10(int n);

/* quadratic forms */
void qfb_comp(GEN z,GEN x,GEN y);
GEN qfr5_dist(GEN e, GEN d, long prec);
GEN qfr5_init(GEN x, long prec);
GEN qfr5_comp(GEN x, GEN y, GEN D, GEN sqrtD, GEN isqrtD);
GEN qfr5_red(GEN x, GEN D, GEN sqrtD, GEN isqrtD);
GEN qfr_rho(GEN x, GEN D, GEN sqrtD, GEN isqrtD);
GEN qfr_pow(GEN x, GEN n);
GEN qfr_unit(GEN x);
GEN qfi_unit(GEN x);

/* Dedekind zeta */
GEN zeta_get_limx(long r1, long r2, long bit);
long zeta_get_i0(long r1, long r2, long bit, GEN limx);
long zeta_get_N0(GEN C,  GEN limx);

/* polynomials */
GEN  bezout_lift_fact(GEN T, GEN Tmod, GEN p, long e);
long FpX_split_Berlekamp(GEN *t, GEN pp);
GEN  FqX_split_all(GEN z, GEN T, GEN p);
long FqX_split_by_degree(GEN *pz, GEN u, GEN q, GEN T, GEN p);
long FqX_split_deg1(GEN *pz, GEN u, GEN q, GEN T, GEN p);
GEN  FqX_split_roots(GEN z, GEN T, GEN p, GEN pol);
GEN  polratlift(GEN P, GEN mod, GEN amax, GEN bmax, GEN denom);
GEN  polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N);
GEN  ZX_caract_sqf(GEN A, GEN B, long *lambda, long v);
GEN  ZX_disc_all(GEN,ulong);
long ZX_get_prec(GEN x);
GEN  ZX_resultant_all(GEN A, GEN B, GEN dB, ulong bound);
GEN  ZY_ZXY_resultant_all(GEN A, GEN B0, long *lambda, GEN *LPRS);
GEN  ZY_ZXY_resultant(GEN A, GEN B0, long *lambda);

GEN addmulXn(GEN x, GEN y, long d);
GEN gmulXn(GEN x, long d);
GEN monomial(GEN a, int degpol, int v);
GEN mulmat_pol(GEN A, GEN x);
GEN ser_to_pol_i(GEN x, long lx);

GEN cauchy_bound(GEN p);
GEN initgaloisborne(GEN T, GEN dn, long prec, GEN *pL, GEN *pprep, GEN *pdis);
GEN max_modulus(GEN p, double tau);
GEN polint_i(GEN xa, GEN ya, GEN x, long n, GEN *ptdy);
GEN quicktrace(GEN x, GEN sym);
GEN roots_to_pol_intern(GEN L, GEN a, long v, int plus);
GEN roots_to_pol_r1r2(GEN a, long r1, long v);
GEN special_pivot(GEN x);
GEN vandermondeinverse(GEN L, GEN T, GEN den, GEN prep);
int cmbf_precs(GEN q, GEN A, GEN B, long *a, long *b, GEN *qa, GEN *qb);

/* CRT */
GEN ZM_init_CRT(GEN Hp, ulong p);
int ZM_incremental_CRT(GEN H, GEN Hp, GEN q, GEN qp, ulong p);

/* tunings */
void setsqri(long a);
void setmuli(long a);
void setmulr(long a);

/* */
GEN   init_remiimul(GEN M);
ulong invrev(ulong b);
GEN   red_montgomery(GEN T, GEN N, ulong inv);
GEN   remiimul(GEN x, GEN sy);
GEN   addrex01(GEN x);
GEN   subrex01(GEN x);

/* FIXME: adapt/use mpn_[lr]shift instead */
#define shift_left(z2,z1,imin,imax,f, sh) {\
  register const ulong _m = BITS_IN_LONG - (sh);\
  shift_left2((z2),(z1),(imin),(imax),(f),(sh),(_m)); }

#define shift_right(z2,z1,imin,imax,f, sh) {\
  register const ulong _m = BITS_IN_LONG - (sh);\
  shift_right2((z2),(z1),(imin),(imax),(f),(sh),(_m)); }
