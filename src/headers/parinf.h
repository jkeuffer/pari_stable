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

#define id_PRINCIPAL 0
#define id_PRIME     1
#define id_MAT       2

/* for _initalg */
#define nf_NOROOTS     32
#define nf_PARTIALFACT 16
#define nf_RED          8
#define nf_SMALL        4
#define nf_PARTRED      2
#define nf_ORIG         1

/* for isprincipal */
#define nf_GEN   1
#define nf_FORCE 2
#define nf_GIVEPREC 4
#define nf_GENMAT 8

/* for buchray */
#define nf_INIT  4

/* for discray */
#define nf_REL  1
#define nf_COND 2

/* for polredabs */
#define nf_ALL   4
#define nf_RAW   8

/* for polred (FIXME: unify with polredabs)*/
#define red_PARTIAL 1
#define red_ORIG    2

/* for lllgramall[gen] */
#define lll_ALL 0
#define lll_KER 1
#define lll_IM  2
#define lll_GRAM 0x100

/* for minim */
#define min_ALL   0
#define min_FIRST 1
#define min_PERF  2

/* for allbase */
#define ba_PARTIAL 1
#define ba_ROUND2  2

/* for fincke_pohst() */
typedef struct FP_chk_fun {
  GEN (*f)(void *,GEN);
  GEN (*f_init)(struct FP_chk_fun*,GEN,GEN);
  GEN (*f_post)(void *,GEN);
  void *data;
  int skipfirst;
} FP_chk_fun;

extern GEN _initalg(GEN x, long flag, long prec);
extern GEN fincke_pohst(GEN a,GEN BOUND,long stockmax,long flag, long PREC, FP_chk_fun *CHECK);
extern GEN polredfirstpol(GEN x, long flag, FP_chk_fun *CHECK);
