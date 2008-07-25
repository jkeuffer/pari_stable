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

/******************************************************************/
/*                                                                */
/*              PARI header file (common to all versions)         */
/*                                                                */
/******************************************************************/
#ifdef STMT_START /* perl headers */
#  undef STMT_START
#endif
#ifdef STMT_END
#  undef STMT_END
#endif
/* STMT_START { statements; } STMT_END;
 * can be used as a single statement, as in
 * if (x) STMT_START { ... } STMT_END; else ...
 * [ avoid "dangling else" problem in macros ] */
#define STMT_START	do
#define STMT_END	while (0)
/*=====================================================================*/
/* CATCH(numer) {
 *   recovery
 * } TRY {
 *   code
 * } ENDCATCH
 * will execute 'code', then 'recovery' if exception 'numer' is thrown
 * [ any exception if numer == CATCH_ALL ].
 * RETRY = as TRY, but execute 'recovery', then 'code' again [still catching] */
#define CATCH(err) {         \
  VOLATILE long __err = err; \
  int pari_errno;            \
  jmp_buf __env;             \
  void *__catcherr = NULL;   \
  if ((pari_errno = setjmp(__env)))

#define RETRY { __catcherr = err_catch(__err, &__env); {
#define TRY else RETRY

/* Take address of __catcher to prevent compiler from putting it into a register
 * (could be clobbered by longjmp otherwise) */
#define CATCH_RELEASE() err_leave(&__catcherr)
#define ENDCATCH }} CATCH_RELEASE(); }

#define CATCH_ALL -1
/*=====================================================================*/
/* VOLATILE int errorN;
 * CATCH_ERR(errorN) {
 *   code
 * } ENDCATCH_ERR
 * executes 'code', setting errorN to the number of exception thrown;
 * errorN is 0 if no error was thrown. */

#define CATCH_ERR(__err) {  \
  jmp_buf __env;            \
  __err = setjmp(__env);    \
  if (!__err) {		    \
    void *__catcherr = err_catch(CATCH_ALL, &__env);

#define ENDCATCH_ERR	    \
    CATCH_RELEASE();	    \
  }}
/*=====================================================================*/

#define LOG2   (0.6931471805599453) /* log(2) */
#define LOG10_2 (0.3010299956639812) /* log_10(2) */

#ifndef  PI
#  define PI (3.141592653589)
#endif

/*3.32~log_2(10)*/
#define ndec2nlong(x) (1 + (long)((x)*(3.321928094887362/BITS_IN_LONG)))
#define ndec2prec(x) (3 + (long)((x)*(3.321928094887362/BITS_IN_LONG)))
#define nbits2prec(x) (((x)+3*BITS_IN_LONG-1) >> TWOPOTBITS_IN_LONG)
#define nbits2nlong(x) (((x)+BITS_IN_LONG-1) >> TWOPOTBITS_IN_LONG)
#define nchar2nlong(x) (((x)+sizeof(long)-1) / sizeof(long))
#define bit_accuracy(x) (((x)-2) * BITS_IN_LONG)
#define bit_accuracy_mul(x,y) (((x)-2) * (BITS_IN_LONG*(y)))
#define prec2ndec(x) ((long)bit_accuracy_mul((x), LOG10_2))
#define GSTR(x) ((char*) (((GEN) (x)) + 1 ))
#define divsBIL(n) ((n)>> TWOPOTBITS_IN_LONG)
#define remsBIL(n) ((n) & (BITS_IN_LONG-1))

#include "pariold.h"

/* Common global variables: */
extern ulong DEBUGFILES, DEBUGLEVEL, DEBUGMEM, precdl;
extern THREAD GEN  bernzone,gpi,geuler;
extern GEN   primetab;
extern GEN   gen_m1,gen_1,gen_2,gen_m2,ghalf,gi,gen_0,gnil;
extern VOLATILE int PARI_SIGINT_block, PARI_SIGINT_pending;

extern const long lontyp[];
extern void* global_err_data;

extern int new_galois_format, factor_add_primes, factor_proven;

enum manage_var_t {
  manage_var_create,
  manage_var_delete,
  manage_var_init,
  manage_var_next,
  manage_var_max_avail,
  manage_var_pop
};

/* pari_init_opts */
enum {
  INIT_JMPm = 1,
  INIT_SIGm = 2,
  INIT_DFTm = 4
};

#ifndef HAS_EXP2
#  undef exp2
#  ifdef __cplusplus
     inline double exp2(double x) {return exp(x*LOG2);}
#  else
#    define exp2(x) (exp((double)(x)*LOG2))
#  endif
#endif
#ifndef HAS_LOG2
#  undef log2
#  ifdef __cplusplus
     inline double log2(double x) {return log(x)/LOG2;}
#  else
#    define log2(x) (log((double)(x))/LOG2)
#  endif
#endif

#define bern(i)       (bernzone + 3 + (i)*bernzone[2])

/* works only for POSITIVE integers */
#define mod2BIL(x)  (*int_LSW(x))
#define mod64(x)  (mod2BIL(x) & 63)
#define mod32(x)  (mod2BIL(x) & 31)
#define mod16(x)  (mod2BIL(x) & 15)
#define mod8(x)   (mod2BIL(x) & 7)
#define mod4(x)   (mod2BIL(x) & 3)
#define mod2(x)   (mod2BIL(x) & 1)
#define is_bigint_lg(n,l) ((l)>3 || ((l)==3 && (((GEN)(n))[2] & HIGHBIT)))
#define is_pm1_lg(n,l)    ((l)==3 && ((GEN)(n))[2]==1)
#define is_pm1(n)    is_pm1_lg   (n, lgefint(n))
#define is_bigint(n) is_bigint_lg(n, lgefint(n))

#define degpol(a) ((long)lg(a)-3)
#define lgpol(a) ((long)lg(a)-2)

#define odd(x) ((x) & 1)
#define both_odd(x,y) ((x)&(y)&1)

#define ONLY_REM ((GEN*)0x1L)
#define ONLY_DIVIDES ((GEN*)0x2L)

#define DIFFPTR_SKIP	255		/* Skip these entries */
#define NEXT_PRIME_VIADIFF(p,d)	 STMT_START \
  { while (*(d) == DIFFPTR_SKIP) (p) += *(d)++; (p) += *(d)++; } STMT_END
#define NEXT_PRIME_VIADIFF_CHECK(p,d)  STMT_START \
  { if (!*(d)) pari_err(primer1); NEXT_PRIME_VIADIFF(p,d); } STMT_END
