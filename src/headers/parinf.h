/* $Id$ */
GEN initalgall0(GEN x, long flag, long prec);

#define id_PRINCIPAL 0
#define id_PRIME     1
#define id_MAT       2

/* for initalgredall */
#define nf_REDUCE       8
#define nf_SMALL        4 /* for both */
#define nf_PARTIAL      2
#define nf_ORIG         1

/* for initalgall0 */
#define nf_DIFFERENT   16
#define nf_REGULAR      0 /* for both */

/* for isprincipal */
#define nf_GEN   1 /* for polredabs also */
#define nf_FORCE 2

/* for buchray */
#define nf_INIT  4

/* for discray */
#define nf_REL  1
#define nf_COND 2

/* for polredabs */
#define nf_NORED 2
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
