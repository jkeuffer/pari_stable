/* $Id$

Copyright (C) 2001  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/* This file is a quick hack adapted from gmp-4.0 tuning utilities
 * (T. Granlund et al.)
 * 
 * (GMU MP Library is Copyright Free Software Foundation, Inc.) */
#include <pari.h>

/* you might wish to tweak the Makefile so as to use GMP cycle counting
 * functions (look for GMP in Oxxx/Makefile) */

#define numberof(x) (sizeof(x) / sizeof((x)[0]))

static int option_trace = 0;

typedef struct {
  ulong reps, size, type;
  GEN x, y;
} speed_param;

typedef double (*speed_function_t)(ANYARG);

#define MAX_TABLE 2
#define MAX_SIZE 1000

typedef struct {
  const char        *name[MAX_TABLE];
  speed_function_t  fun1;
  speed_function_t  fun2;
  double            step_factor;    /* how much to step sizes (rounded down) */
  double            function_fudge; /* multiplier for "function" speeds */
  int               stop_since_change;
  double            stop_factor;
  long              min_size[MAX_TABLE];
  long              max_size[MAX_TABLE];
  int               type; /* t_INT or t_REAL */
} tune_param;

/* ========================================================== */
#ifdef GMP_TIMER
/* needed to link with gmp-4.0/tune/{time,freq}.o */
int speed_option_verbose = 0;
extern double speed_unittime;
extern int    speed_precision;
void speed_starttime(void);
double speed_endtime(void);
#else
static pari_timer __T;
static double speed_unittime = 1e-4;
static int    speed_precision= 1000;
static void speed_starttime() { (void)TIMER(&__T); }
static double speed_endtime() { return (double)TIMER(&__T)/1000.; }
#endif

/* ========================================================== */

/* random int, n words */
static GEN
rand_INT(long n)
{
  pari_sp av = avma;
  GEN x, N = shifti(gun, n*BITS_IN_LONG);
  if (n <= 0) err(talker,"n too small in rand_INT (%ld)", n);
  do
    x = genrand(N);
  while (lgefint(x) != n+2);
  return gerepileuptoint(av, x);
}

static GEN
rand_REAL(long n)
{
  GEN r = cgetr(n+2);
  pari_sp av = avma;
  GEN x = rand_INT(n);
  affir(x,r); avma = av; return r;
}

static GEN
rand_g(long n, long type)
{
  return (type == t_INT)? rand_INT(n): rand_REAL(n);
}

/* ========================================================== */

#define TIME_FUN(call) {\
  {                                            \
    pari_sp av = avma;                         \
    int i;                                     \
    speed_starttime();                         \
    i = (s)->reps;                             \
    do { call; avma = av; } while (--i != 0);  \
  }                                            \
  return speed_endtime();                      \
}

extern void setsqri(long a);
extern void setmuli(long a);
extern void setmulr(long a);
#define disable_Karatsuba_r(s) (setmulr(lg(s->x)))
#define  enable_Karatsuba_r(s) (setmulr(lg(s->x)-2))
#define disable_Karatsuba_i(s) (setmuli(lg(s->x)), setsqri(lg(s->x)))
#define  enable_Karatsuba_i(s) (setmuli(lg(s->x)-2), setsqri(lg(s->x)-2))
#define MULFUN_i(call, s) {\
  disable_Karatsuba_i(s);  \
  TIME_FUN(call(s->x, s->y)); }

#define MULFUN_r(call, s) {\
  disable_Karatsuba_r(s);  \
  TIME_FUN(call(s->x, s->y)); }

#define SQRFUN_i(call, s) {\
  disable_Karatsuba_i(s);  \
  TIME_FUN(call(s->x)); }

#define KARAMULFUN_i(call, s) {\
  enable_Karatsuba_i(s);     \
  TIME_FUN(call(s->x, s->y)); }

#define KARAMULFUN_r(call, s) {\
  enable_Karatsuba_r(s);     \
  TIME_FUN(call(s->x, s->y)); }

#define KARASQRFUN_i(call, s) {\
  enable_Karatsuba_i(s);     \
  TIME_FUN(call(s->x)); }

static double speed_mulrr(speed_param *s) { MULFUN_r(mulrr, s); }
static double speed_mulii(speed_param *s) { MULFUN_i(mulii, s); }
static double speed_sqri (speed_param *s) { SQRFUN_i( sqri, s); }
static double speed_karamulrr(speed_param *s) { KARAMULFUN_r(mulrr, s); }
static double speed_karamulii(speed_param *s) { KARAMULFUN_i(mulii, s); }
static double speed_karasqri (speed_param *s) { KARASQRFUN_i( sqri, s); }
 
extern  GEN init_remainder(GEN M);
extern ulong invrev(ulong b);
extern GEN red_montgomery(GEN T, GEN N, ulong inv);
extern GEN resiimul(GEN x, GEN sy);

#define INIT_RED(s, op)                                 \
  long i, lx = lg(s->x);                                \
  op = cgeti(2*lx - 2);                                 \
  op[1] = evallgefint(2*lx - 2) | evalsigne(1);         \
  for (i=2; i<lx; i++) op[i]      = s->x[i];            \
  for (i=2; i<lx; i++) op[lx-2+i] = s->x[i];            \
  modBIL(s->y) |= 1; /* make sure modulus is odd */

static double speed_redc(speed_param *s) {
  ulong inv;
  GEN op;
  INIT_RED(s, op);
  inv = (ulong) -invrev(modBIL(s->y));
  TIME_FUN( red_montgomery(op, s->y, inv) );
};
static double speed_modii(speed_param *s) {
  GEN op;
  INIT_RED(s, op);
  TIME_FUN( resii(op, s->y) );
};
static double speed_resiimul(speed_param *s) {
  GEN op, sM;
  INIT_RED(s, op);
  sM = init_remainder(s->y);
  TIME_FUN( resiimul(op, sM) );
}

/* ========================================================== */

int
double_cmp_ptr(double *x, double *y) { return *x - *y; }

double
time_fun(speed_function_t fun, speed_param *s)
{
#define TOLERANCE 1.005 /* 0.5% */
  pari_sp av = avma;
  double t[30];
  long i,j,e;


  s->x = rand_g(s->size, s->type);
  s->y = rand_g(s->size, s->type);
  s->reps = 1;
  for (i = 0; i < numberof(t); i++)
  {
    for (;;)
    {
      double reps_d;
      t[i] = fun(s);
      
      if (!t[i]) { s->reps *= 10; continue; }

      if (t[i] >= speed_unittime * speed_precision) break;


      /* go to a value of reps to make t[i] >= precision */
      reps_d = ceil (1.1 * s->reps
                     * speed_unittime * speed_precision
                     / max(t[i], speed_unittime));
      if (reps_d > 2e9 || reps_d < 1.0)
        err(talker, "Fatal error: new reps bad: %.2f\n", reps_d);

      s->reps = (ulong)reps_d;
    }
    
    t[i] /= s->reps;

    /* require 3 values within TOLERANCE when >= 2 secs, 4 when below */
    e = (t[0] >= 2.0)? 3: 4;

   /* Look for e many t[]'s within TOLERANCE of each other to consider a
      valid measurement.  Return smallest among them.  */
    if (i >= e)
    {
      qsort (t, i+1, sizeof(t[0]), (QSCOMP)double_cmp_ptr);
      for (j = e-1; j < i; j++)
        if (t[j] <= t[j-e+1] * TOLERANCE) { avma = av; return t[j-e+1]; }
    }
  }
  err(talker,"couldn't measure time");
  return -1.0; /* not reached */
}

struct dat_t {
  long size;
  double d;
} *dat = NULL;
int ndat = 0;
int allocdat = 0;

void
add_dat(long size, double d)
{
  if (ndat == allocdat)
  {
    allocdat += max(allocdat, 100);
    dat = (struct dat_t*) gprealloc((void*)dat, allocdat * sizeof(dat[0]));
  }
  dat[ndat].size = size;
  dat[ndat].d    = d;
  ndat++;
}

long
analyze_dat(int final)
{
  double  x, min_x;
  int     j, min_j;

  /* If the threshold is set at dat[0].size, any positive values are bad. */
  x = 0.0;
  for (j = 0; j < ndat; j++)
    if (dat[j].d > 0.0) x += dat[j].d;

  if (final && option_trace >= 3)
  {
    printf("\n");
    printf("x is the sum of the badness from setting thresh at given size\n");
    printf("  (minimum x is sought)\n");
    printf("size=%ld  first x=%.4f\n", dat[j].size, x);
  }

  min_x = x;
  min_j = 0;

  /* When stepping to the next dat[j].size, positive values are no longer
     bad (so subtracted), negative values become bad (so add the absolute
     value, meaning subtract). */
  for (j = 0; j < ndat; j++)
  {
    if (final && option_trace >= 3)
      printf ("size=%ld  x=%.4f\n", dat[j].size, x);

    if (x < min_x) { min_x = x; min_j = j; }
    x -= dat[j].d;
  }
   
  return min_j;
}

void
print_define(const char *name, long value)
{
  printf("#define %-25s  %5ld\n\n", name, value);
}

int
one(tune_param *param)
{
  int  since_positive, since_thresh_change;
  int  thresh_idx, new_thresh_idx;
  speed_param s;

#define DEFAULT(x,n)  if (! (param->x))  param->x = (n);
  DEFAULT (function_fudge, 1.0);
  DEFAULT (fun2, param->fun1);
  DEFAULT (step_factor, 0.01);  /* small steps by default */
  DEFAULT (stop_since_change, 80);
  DEFAULT (stop_factor, 1.2);
  DEFAULT (type, t_INT);

  s.type = param->type;
  s.size = param->min_size[0];
  ndat = 0;
  since_positive = 0;
  since_thresh_change = 0;
  thresh_idx = 0;
  if (option_trace >= 1) 
    printf("Setting %s...\n", param->name[0]);
  if (option_trace >= 2)
  {
    printf("             algorithm-A  algorithm-B   ratio  possible\n");
    printf("              (seconds)    (seconds)    diff    thresh\n");
  }

  for (;
        s.size < MAX_SIZE;
        s.size += max((long)floor(s.size * param->step_factor), 1))
  {
    double t1,t2,d;
    t1 = time_fun(param->fun1, &s);
    t2 = time_fun(param->fun2, &s);
    if (t2 >= t1)
      d = (t2 - t1) / t2; /* <= 0 */
    else
      d = (t2 - t1) / t1; /* > 0  */

    add_dat(s.size, d);
    new_thresh_idx = analyze_dat(0);

    if (option_trace >= 2)
    {
      printf ("size =%3ld    %.9f  %.9f  % .4f %c  %ld\n",
               s.size, t1, t2, d,
               t1 > t2 ? '#' : ' ', dat[new_thresh_idx].size);
    }

    /* Stop if the last time method 1 was faster was more than a
        certain number of measurements ago.  */
#define STOP_SINCE_POSITIVE 100
    if (d >= 0) 
      since_positive = 0;
    else
      if (++since_positive > STOP_SINCE_POSITIVE)
      {
        if (option_trace >= 1)
          printf ("stopped due to since_positive (%d)\n",
                  STOP_SINCE_POSITIVE);
      }
    /* Stop if method 1 has become slower by a certain factor. */
    if (t1 >= t2 * param->stop_factor)
    {
      if (option_trace >= 1)
        printf ("stopped due to t1 >= t2 * factor (%.1f)\n",
                param->stop_factor);
      break;
    }
    /* Stop if the threshold implied hasn't changed in a certain
       number of measurements. */
    if (thresh_idx != new_thresh_idx)
      since_thresh_change = 0, thresh_idx = new_thresh_idx;
    else
      if (++since_thresh_change > param->stop_since_change)
      {
        if (option_trace >= 1)
          printf ("stopped due to since_thresh_change (%d)\n",
                  param->stop_since_change);
        break;
      }
  }
  thresh_idx = dat[analyze_dat(1)].size;
  print_define(param->name[0], thresh_idx);
  return thresh_idx;
}

void error(int argc/* ignored */, char **argv)
{
  (void)argv;
  err(talker, "usage: %s [-t] [-t] [-u unittime]", argv[0]);
}

int
main(int argc, char **argv)
{
  int i, MONTGOMERY_LIMIT, KARATSUBA_MULI_LIMIT;
  pari_init(4000000, 2);
  for (i = 1; i < argc; i++)
  {
    char *s = argv[i];
    if (*s++ != '-') error(argc,argv);
    switch(*s) {
      case 't': option_trace++; continue;
      case 'u': s++;
        if (!*s)
        {
          if (++i == argc) error(argc,argv);
          s = argv[i];
        }
        speed_unittime = atof(s);
        break;
      default: error(argc,argv);
    }
  }
  
  { static tune_param param; 
    param.name[0] = "KARATSUBA_MULI_LIMIT";
    param.min_size[0] = 4;
    param.fun1 = &speed_mulii;
    param.fun2 = &speed_karamulii;
    KARATSUBA_MULI_LIMIT = one(&param);
  }
  { static tune_param param; 
    param.name[0] = "KARATSUBA_MULR_LIMIT";
    param.min_size[0] = 4;
    param.type = t_REAL;
    setmuli(KARATSUBA_MULI_LIMIT);
    param.fun1 = &speed_mulrr;
    param.fun2 = &speed_karamulrr;
    (void)one(&param);
  }
  { static tune_param param; 
    param.name[0] = "KARATSUBA_SQRI_LIMIT";
    param.min_size[0] = 4;
    param.fun1 = (speed_function_t)&speed_sqri;
    param.fun2 = (speed_function_t)&speed_karasqri;
    (void)one(&param);
  }
  { static tune_param param; 
    param.name[0] = "MONTGOMERY_LIMIT";
    param.min_size[0] = 1;
    param.fun1 = &speed_redc;
    param.fun2 = &speed_modii;
    MONTGOMERY_LIMIT = one(&param);
  }
  { static tune_param param; 
    param.name[0] = "RESIIMUL_LIMIT";
    param.min_size[0] = MONTGOMERY_LIMIT;
    param.fun1 = &speed_modii;
    param.fun2 = &speed_resiimul;
    (void)one(&param);
  }

  if (dat) free((void*)dat);
  return 1;
}
