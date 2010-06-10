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
#define STMT_START        do
#define STMT_END        while (0)
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
  VOLATILE long __err = err, __catcherr = -1; \
  int pari_errno;            \
  jmp_buf __env;             \
  if ((pari_errno = setjmp(__env)))

#define RETRY { __catcherr = err_catch(__err, &__env);
#define TRY else RETRY

#define CATCH_RELEASE() err_leave(__catcherr)
#define ENDCATCH } CATCH_RELEASE(); }
extern const long CATCH_ALL;

extern const double LOG2, LOG10_2, LOG2_10;
#ifndef  PI
#  define PI (3.141592653589)
#endif

/* Common global variables: */
extern int new_galois_format, factor_add_primes, factor_proven;
extern ulong DEBUGFILES, DEBUGLEVEL, DEBUGMEM, precdl;
extern THREAD GEN  bernzone;
extern GEN primetab;
extern GEN gen_m1,gen_1,gen_2,gen_m2,ghalf,gen_0,gnil;
extern VOLATILE int PARI_SIGINT_block, PARI_SIGINT_pending;

extern const long lontyp[];
extern THREAD void* global_err_data;
extern void (*cb_pari_ask_confirm)(const char *);
extern int  (*cb_pari_whatnow)(const char *, int);
extern void (*cb_pari_sigint)(void);
extern int (*cb_pari_handle_exception)(long);
extern void (*cb_pari_err_recover)(long);

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
#  define exp2(x) (exp((double)(x)*LOG2))
#endif
#ifndef HAS_LOG2
#  undef log2
#  define log2(x) (log((double)(x))/LOG2)
#endif

#define bern(i)       (bernzone + 3 + (i)*bernzone[2])

#define ONLY_REM ((GEN*)0x1L)
#define ONLY_DIVIDES ((GEN*)0x2L)

#define DIFFPTR_SKIP        255                /* Skip these entries */
#define NEXT_PRIME_VIADIFF(p,d)         STMT_START \
  { while (*(d) == DIFFPTR_SKIP) (p) += *(d)++; (p) += *(d)++; } STMT_END
#define NEXT_PRIME_VIADIFF_CHECK(p,d)  STMT_START \
  { if (!*(d)) pari_err(primer1,0); NEXT_PRIME_VIADIFF(p,d); } STMT_END
