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

typedef struct {
  GEN x; /* defining polynomial (monic, integral) */
  GEN dK; /* disc(K) */
  GEN index; /* [O_K : Z[X]/(x)] */
  GEN bas;  /* Z-basis of O_K (t_VEC of t_POL) */
  long r1; /* number of real places of K */
/* possibly NULL = irrelevant or not computed */
  GEN lead; /* leading coeff of initial polynomial defining K if non monic */
  GEN dx;   /* disc(x) */
  GEN basden; /* [nums(bas), dens(bas)] */
} nfbasic_t;

typedef struct {
  GEN x;
  GEN ro;   /* roots of x */
  long r1;
  GEN basden;
  long prec;
/* possibly -1 = irrelevant or not computed */
  long extraprec;
/* possibly NULL = irrelevant or not computed */
  GEN M;
  GEN G;
} nffp_t;

#define id_PRINCIPAL 0
#define id_PRIME     1
#define id_MAT       2

/* for _initalg */
#define nf_ROUND2      64
#define nf_NOROOTS     32
#define nf_PARTIALFACT 16 /* and allbase */
#define nf_RED          8
#define nf_PARTRED      2
#define nf_ORIG         1

/* for rnfpolredabs */
#define nf_ABSOLUTE     2
#define nf_ADDZK      256

/* for isprincipal */
#define nf_GEN   1
#define nf_FORCE 2
#define nf_GIVEPREC 4
#define nf_GENMAT 8
#define nf_GEN_IF_PRINCIPAL 512

/* for buchray */
#define nf_INIT  4

/* for buchall */
#define nf_ROOT1 512
#define nf_UNITS 1024
enum { fupb_NONE, fupb_RELAT, fupb_LARGE, fupb_PRECI };

/* for discray */
#define nf_REL  1
#define nf_COND 2

/* for polredabs */
#define nf_ALL   4
#define nf_RAW   8

/* for lllgramall[gen] */
#define lll_ALL 0
#define lll_KER 1
#define lll_IM  2
#define lll_GRAM 0x100

/* for minim */
#define min_ALL   0
#define min_FIRST 1
#define min_PERF  2

/* for fincke_pohst() */
typedef struct FP_chk_fun {
  GEN (*f)(void *,GEN);
  GEN (*f_init)(struct FP_chk_fun*,GEN,GEN);
  void *data;
  int skipfirst;
} FP_chk_fun;

extern GEN _initalg(GEN x, long flag, long prec);
extern GEN fincke_pohst(GEN a,GEN BOUND,long stockmax,long PREC, FP_chk_fun *CHECK);
extern GEN polredfirstpol(GEN x, long flag, FP_chk_fun *CHECK);

/* for ideallog / zlog */
typedef struct {
  GEN lists; /* lists[i] = */
  GEN ind;  /* ind[i] = start of vector */
  GEN P, e; /* finit part of conductor = prod P^e */
  GEN archp; /* archimedean part of conductor, in permutation form */
  long n;  /* total number of generators for all (O_K/P^e)^* and (O_K/f_oo) */
  GEN U; /* base change matrix from generators to bid.gen */
} zlog_S;
extern void init_zlog_bid(zlog_S *S, GEN bid);
