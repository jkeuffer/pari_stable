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
#include "anal.h"
/********************************************************************/
/**                                                                **/
/**                        ITERATIONS                              **/
/**                                                                **/
/********************************************************************/

void
forpari(GEN a, GEN b, GEN code)
{
  pari_sp ltop=avma, av, lim;
  b = gcopy(b); /* Kludge to work-around the a+(a=2) bug */
  av=avma; lim = stack_lim(av,1);
  push_lex(a,code);
  while (gcmp(a,b) <= 0)
  {
    closure_evalvoid(code); if (loop_break()) break;
    a = get_lex(-1); a = typ(a) == t_INT? addis(a, 1): gaddgs(a,1);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"forpari");
      a = gerepileupto(av,a);
    }
    set_lex(-1, a);
  }
  pop_lex(1); avma = ltop;
}

void
whilepari(GEN a, GEN b)
{
  pari_sp av = avma;
  for(;;)
  {
    GEN res = closure_evalnobrk(a);
    if (gequal0(res)) break;
    avma = av;
    closure_evalvoid(b); if (loop_break()) break;
  }
  avma = av;
}

void
untilpari(GEN a, GEN b)
{
  pari_sp av = avma;
  for(;;)
  {
    GEN res;
    closure_evalvoid(b); if (loop_break()) break;
    res = closure_evalnobrk(a);
    if (!gequal0(res)) break;
    avma = av;
  }
  avma = av;
}

static int negcmp(GEN x, GEN y) { return gcmp(y,x); }

void
forstep(GEN a, GEN b, GEN s, GEN code)
{
  long ss, i;
  pari_sp av, av0 = avma, lim;
  GEN v = NULL;
  int (*cmp)(GEN,GEN);

  b = gcopy(b); av=avma; lim = stack_lim(av,1);
  push_lex(a,code);
  if (is_vec_t(typ(s)))
  {
    v = s; s = gen_0;
    for (i=lg(v)-1; i; i--) s = gadd(s,gel(v,i));
  }
  ss = gsigne(s);
  if (!ss) pari_err(talker, "step equal to zero in forstep");
  cmp = (ss > 0)? &gcmp: &negcmp;
  i = 0;
  while (cmp(a,b) <= 0)
  {
    closure_evalvoid(code); if (loop_break()) break;
    if (v)
    {
      if (++i >= lg(v)) i = 1;
      s = gel(v,i);
    }
    a = get_lex(-1); a = gadd(a,s);

    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"forstep");
      a = gerepileupto(av,a);
    }
    set_lex(-1,a);
  }
  pop_lex(1); avma = av0;
}

/* value changed during the loop, replace by the first prime whose
   value is strictly larger than new value */
static void
update_p(byteptr *ptr, ulong prime[])
{
  GEN z = get_lex(-1);
  ulong a, c;

  if (typ(z) == t_INT) a = 1; else { z = gceil(z); a = 0; }
  if (lgefint(z) > 3) { prime[2] = ULONG_MAX; /* = infinity */ return; }
  a += itou(z); c = prime[2];
  if (c < a)
    prime[2] = init_primepointer(a, c, ptr); /* increased */
  else if (c > a)
  { /* lowered, reset p */
    *ptr = diffptr;
    prime[2] = init_primepointer(a, 0, ptr);
  }
  set_lex(-1,(GEN)prime);
}

static byteptr
prime_loop_init(GEN ga, GEN gb, ulong *a, ulong *b, ulong *p)
{
  byteptr d = diffptr;

  ga = gceil(ga); gb = gfloor(gb);
  if (typ(ga) != t_INT || typ(gb) != t_INT)
    pari_err(typeer,"prime_loop_init");
  if (signe(gb) < 0) return NULL;
  if (signe(ga) < 0) ga = gen_1;
  if (lgefint(ga)>3 || lgefint(gb)>3)
  {
    if (cmpii(ga, gb) > 0) return NULL;
    pari_err(primer1, 0);
  }
  *a = itou(ga);
  *b = itou(gb); if (*a > *b) return NULL;
  maxprime_check(*b);
  *p = init_primepointer(*a, 0, &d); return d;
}

void
forprime(GEN ga, GEN gb, GEN code)
{
  long p[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
  ulong *prime = (ulong*)p;
  ulong a, b;
  pari_sp av = avma;
  byteptr d;

  d = prime_loop_init(ga,gb, &a,&b, (ulong*)&prime[2]);
  if (!d) { avma = av; return; }

  avma = av; push_lex((GEN)prime,code);
  while (prime[2] < b)
  {
    closure_evalvoid(code); if (loop_break()) break;
    if (get_lex(-1) == (GEN) prime)
      NEXT_PRIME_VIADIFF(prime[2], d);
    else
      update_p(&d, prime);
    avma = av;
  }
  /* if b = P --> *d = 0 now and the loop wouldn't end if it read 'while
   * (prime[2] <= b)' */
  if (prime[2] == b) { closure_evalvoid(code); (void)loop_break(); avma = av; }
  pop_lex(1);
}

void
fordiv(GEN a, GEN code)
{
  long i, l;
  pari_sp av2, av = avma;
  GEN t = divisors(a);

  push_lex(gen_0,code); l=lg(t); av2 = avma;
  for (i=1; i<l; i++)
  {
    set_lex(-1,gel(t,i));
    closure_evalvoid(code); if (loop_break()) break;
    avma = av2;
  }
  pop_lex(1); avma=av;
}

/* Embedded for loops:
 *   fl = 0: execute ch (a), where a = (ai) runs through all n-uplets in
 *     [m1,M1] x ... x [mn,Mn]
 *   fl = 1: impose a1 <= ... <= an
 *   fl = 2:        a1 <  ... <  an
 */

typedef struct {
  GEN *a, *m, *M; /* current n-uplet, minima, Maxima */
  long n; /* length */
} forvec_data;

static GEN /* used for empty vector, n = 0 */
forvec_dummy(GEN d, GEN a) { (void)d; (void)a; return NULL; }

/* increment and return d->a [over integers]*/
static GEN
forvec_next_i(GEN gd, GEN ignored)
{
  forvec_data *d=(forvec_data *) gd;
  long i = d->n;
  (void)ignored;
  for (;;) {
    if (cmpii(d->a[i], d->M[i]) < 0) {
      d->a[i] = incloop(d->a[i]);
      return (GEN)d->a;
    }
    d->a[i] = resetloop(d->a[i], d->m[i]);
    if (--i <= 0) return NULL;
  }
}
/* increment and return d->a [generic]*/
static GEN
forvec_next(GEN gd, GEN v)
{
  forvec_data *d=(forvec_data *) gd;
  long i = d->n;
  for (;;) {
    gel(v,i) = gaddgs(gel(v,i), 1);
    if (gcmp(gel(v,i), d->M[i]) <= 0) return v;
    gel(v,i) = d->m[i];
    if (--i <= 0) return NULL;
  }
}

/* non-decreasing order [over integers] */
static GEN
forvec_next_le_i(GEN gd, GEN ignored)
{
  forvec_data *d=(forvec_data *) gd;
  long i = d->n;
  (void)ignored;
  for (;;) {
    if (cmpii(d->a[i], d->M[i]) < 0)
    {
      d->a[i] = incloop(d->a[i]);
      /* m[i] < a[i] <= M[i] < M[i+1] */
      while (i < d->n)
      {
        GEN t;
        i++;
        if (cmpii(d->a[i-1], d->a[i]) <= 0) continue;
        /* a[i-1] <= M[i-1] <= M[i] */
        t = d->a[i-1]; if (cmpii(t, d->m[i]) < 0) t = d->m[i];
        d->a[i] = resetloop(d->a[i], t);/*a[i]:=max(a[i-1],m[i])*/
      }
      return (GEN)d->a;
    }
    d->a[i] = resetloop(d->a[i], d->m[i]);
    if (--i <= 0) return NULL;
  }
}
/* non-decreasing order [generic] */
static GEN
forvec_next_le(GEN gd, GEN v)
{
  forvec_data *d=(forvec_data *) gd;
  long i = d->n, imin = d->n;
  for (;;) {
    gel(v,i) = gaddgs(gel(v,i), 1);
    if (gcmp(gel(v,i), d->M[i]) <= 0)
    {
      while (i < d->n)
      {
        i++;
        if (gcmp(gel(v,i-1), gel(v,i)) <= 0) continue;
        while (gcmp(gel(v,i-1), d->M[i]) > 0)
        {
          i = imin - 1; if (!i) return NULL;
          imin = i;
          gel(v,i) = gaddgs(gel(v,i), 1);
          if (gcmp(gel(v,i), d->M[i]) <= 0) break;
        }
        if (i > 1) { /* a >= a[i-1] - a[i] */
          GEN a = gceil(gsub(gel(v,i-1), gel(v,i)));
          gel(v,i) = gadd(gel(v,i), a);
        }
      }
      return v;
    }
    gel(v,i) = d->m[i];
    if (--i <= 0) return NULL;
    if (i < imin) imin = i;
  }
}
/* strictly increasing order [over integers] */
static GEN
forvec_next_lt_i(GEN gd, GEN ignored)
{
  forvec_data *d=(forvec_data *) gd;
  long i = d->n;
  (void)ignored;
  for (;;) {
    if (cmpii(d->a[i], d->M[i]) < 0)
    {
      d->a[i] = incloop(d->a[i]);
      /* m[i] < a[i] <= M[i] < M[i+1] */
      while (i < d->n)
      {
        pari_sp av;
        GEN t;
        i++;
        if (cmpii(d->a[i-1], d->a[i]) < 0) continue;
        av = avma;
        /* a[i-1] <= M[i-1] < M[i] */
        t = addis(d->a[i-1],1); if (cmpii(t, d->m[i]) < 0) t = d->m[i];
        d->a[i] = resetloop(d->a[i], t);/*a[i]:=max(a[i-1]+1,m[i]) <= M[i]*/
        avma = av;
      }
      return (GEN)d->a;
    }
    d->a[i] = resetloop(d->a[i], d->m[i]);
    if (--i <= 0) return NULL;
  }
}
/* strictly increasing order [generic] */
static GEN
forvec_next_lt(GEN gd, GEN v)
{
  forvec_data *d=(forvec_data *) gd;
  long i = d->n, imin = d->n;
  for (;;) {
    gel(v,i) = gaddgs(gel(v,i), 1);
    if (gcmp(gel(v,i), d->M[i]) <= 0)
    {
      while (i < d->n)
      {
        i++;
        if (gcmp(gel(v,i-1), gel(v,i)) < 0) continue;
        for(;;)
        {
          GEN a, b;
          a = addis(gfloor(gsub(gel(v,i-1), gel(v,i))), 1); /* a> v[i-1]-v[i] */
          b = gadd(gel(v,i), a);
          /* v[i-1] < b <= v[i-1] + 1 */
          if (gcmp(b, d->M[i]) <= 0) { gel(v,i) = b; break; }

          for (; i >= imin; i--) gel(v,i) = d->m[i];
          if (!i) return NULL;
          imin = i;
          gel(v,i) = gaddgs(gel(v,i), 1);
          if (gcmp(gel(v,i), d->M[i]) <= 0) break;
        }
      }
      return v;
    }
    gel(v,i) = d->m[i];
    if (--i <= 0) return NULL;
    if (i < imin) imin = i;
  }
}

/* Initialize minima (m) and maxima (M); guarantee
 *   if flag = 1: m[i-1] <= m[i] <= M[i] <= M[i+1]
 *   if flag = 2: m[i-1] <  m[i] <= M[i] <  M[i+1] */
GEN
forvec_start(GEN x, long flag, GEN *gd, GEN (**next)(GEN,GEN))
{
  long i, tx = typ(x), l = lg(x), t = t_INT;
  forvec_data *d;
  if (!is_vec_t(tx)) pari_err(talker,"not a vector in forvec");
  if (l == 1) { *next = &forvec_dummy; return cgetg(1, tx); }
  *gd = cgetg(sizeof(forvec_data)/sizeof(long) + 1, t_VECSMALL) + 1;
  d = (forvec_data*) *gd;
  d->n = l - 1;
  d->a = (GEN*)cgetg(l,tx);
  d->m = (GEN*)cgetg(l,tx);
  d->M = (GEN*)cgetg(l,tx);
  for (i = 1; i < l; i++)
  {
    GEN a, e = gel(x,i), m = gel(e,1), M = gel(e,2);
    tx = typ(e);
    if (! is_vec_t(tx) || lg(e)!=3)
      pari_err(talker,"not a vector of two-component vectors in forvec");
    if (typ(m) != t_INT) t = t_REAL;
    if (i > 1) switch(flag)
    {
      case 1: /* a >= m[i-1] - m */
        a = gceil(gsub(d->m[i-1], m));
        if (typ(a) != t_INT) pari_err(typeer,"forvec");
        if (signe(a) > 0) m = gadd(m, a); else m = gcopy(m);
        break;
      case 2: /* a > m[i-1] - m */
        a = gfloor(gsub(d->m[i-1], m));
        if (typ(a) != t_INT) pari_err(typeer,"forvec");
        a = addis(a, 1);
        if (signe(a) > 0) m = gadd(m, a); else m = gcopy(m);
        break;
      default: m = gcopy(m);
        break;
    }
    if (gcmp(m,M) > 0) return (GEN)NULL;
    d->m[i] = m;
    d->M[i] = M;
  }
  for (i = l-2; i >= 1; i--)
  {
    GEN a, M = d->M[i];
    switch(flag) {
      case 1:/* a >= M - M[i] */
        a = gfloor(gsub(d->M[i+1], M));
        if (typ(a) != t_INT) pari_err(typeer,"forvec");
        if (signe(a) < 0) M = gadd(M, a); else M = gcopy(M);
        /* M <= M[i+1] */
        break;
      case 2:
        a = gceil(gsub(d->M[i+1], M));
        if (typ(a) != t_INT) pari_err(typeer,"forvec");
        a = subis(a, 1);
        if (signe(a) < 0) M = gadd(M, a); else M = gcopy(M);
        /* M < M[i+1] */
        break;
      default:
        M = gcopy(M);
        break;
    }
    d->M[i] = M;
  }
  if (t == t_INT) {
    for (i = 1; i < l; i++) {
      d->a[i] = setloop(d->m[i]);
      if (typ(d->M[i]) != t_INT) d->M[i] = gfloor(d->M[i]);
    }
  } else {
    for (i = 1; i < l; i++) d->a[i] = d->m[i];
  }
  switch(flag)
  {
    case 0: *next = t==t_INT? &forvec_next_i:    &forvec_next; break;
    case 1: *next = t==t_INT? &forvec_next_le_i: &forvec_next_le; break;
    case 2: *next = t==t_INT? &forvec_next_lt_i: &forvec_next_lt; break;
    default: pari_err(flagerr,"forvec");
  }
  return (GEN)d->a;
}

void
forvec(GEN x, GEN code, long flag)
{
  pari_sp av = avma;
  GEN (*next)(GEN,GEN);
  GEN D, v = forvec_start(x, flag, &D, &next);
  push_lex(v,code);
  while (v) {
    closure_evalvoid(code); if (loop_break()) break;
    v = next(D, v);
  }
  pop_lex(1); avma = av;
}

/********************************************************************/
/**                                                                **/
/**                              SUMS                              **/
/**                                                                **/
/********************************************************************/

GEN
somme(GEN a, GEN b, GEN code, GEN x)
{
  pari_sp av, av0 = avma, lim;
  GEN p1;

  if (typ(a) != t_INT) pari_err(talker,"non integral index in sum");
  if (!x) x = gen_0;
  if (gcmp(b,a) < 0) return gcopy(x);

  b = gfloor(b);
  a = setloop(a);
  av=avma; lim = stack_lim(av,1);
  push_lex(a,code);
  for(;;)
  {
    p1 = closure_evalnobrk(code);
    x=gadd(x,p1); if (cmpii(a,b) >= 0) break;
    a = incloop(a);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sum");
      x = gerepileupto(av,x);
    }
    set_lex(-1,a);
  }
  pop_lex(1); return gerepileupto(av0,x);
}

GEN
suminf(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  long fl, G;
  pari_sp av0 = avma, av, lim;
  GEN p1,x = real_1(prec);

  if (typ(a) != t_INT) pari_err(talker,"non integral index in suminf");
  a = setloop(a);
  av = avma; lim = stack_lim(av,1);
  fl=0; G = bit_accuracy(prec) + 5;
  for(;;)
  {
    p1 = eval(a, E); x = gadd(x,p1); a = incloop(a);
    if (gequal0(p1) || gexpo(p1) <= gexpo(x)-G)
      { if (++fl==3) break; }
    else
      fl=0;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"suminf");
      x = gerepileupto(av,x);
    }
  }
  return gerepileupto(av0, gaddgs(x,-1));
}
GEN
suminf0(GEN a, GEN code, long prec)
{ EXPR_WRAP(code, suminf(EXPR_ARG, a, prec)); }

GEN
divsum(GEN num, GEN code)
{
  pari_sp av = avma;
  GEN y = gen_0, t = divisors(num);
  long i, l = lg(t);

  push_lex(gen_0, code);
  for (i=1; i<l; i++)
  {
    set_lex(-1,gel(t,i));
    y = gadd(y, closure_evalnobrk(code));
  }
  pop_lex(1); return gerepileupto(av,y);
}

/********************************************************************/
/**                                                                **/
/**                           PRODUCTS                             **/
/**                                                                **/
/********************************************************************/

GEN
produit(GEN a, GEN b, GEN code, GEN x)
{
  pari_sp av, av0 = avma, lim;
  GEN p1;

  if (typ(a) != t_INT) pari_err(talker,"non integral index in sum");
  if (!x) x = gen_1;
  if (gcmp(b,a) < 0) return gcopy(x);

  b = gfloor(b);
  a = setloop(a);
  av=avma; lim = stack_lim(av,1);
  push_lex(a,code);
  for(;;)
  {
    p1 = closure_evalnobrk(code);
    x = gmul(x,p1); if (cmpii(a,b) >= 0) break;
    a = incloop(a);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prod");
      x = gerepileupto(av,x);
    }
    set_lex(-1,a);
  }
  pop_lex(1); return gerepileupto(av0,x);
}

GEN
prodinf(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  pari_sp av0 = avma, av, lim;
  long fl,G;
  GEN p1,x = real_1(prec);

  if (typ(a) != t_INT) pari_err(talker,"non integral index in prodinf");
  a = setloop(a);
  av = avma; lim = stack_lim(av,1);
  fl=0; G = -bit_accuracy(prec)-5;
  for(;;)
  {
    p1 = eval(a, E); if (gequal0(p1)) { x = p1; break; }
    x = gmul(x,p1); a = incloop(a);
    p1 = gsubgs(p1, 1);
    if (gequal0(p1) || gexpo(p1) <= G) { if (++fl==3) break; } else fl=0;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prodinf");
      x = gerepileupto(av,x);
    }
  }
  return gerepilecopy(av0,x);
}
GEN
prodinf1(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  pari_sp av0 = avma, av, lim;
  long fl,G;
  GEN p1,p2,x = real_1(prec);

  if (typ(a) != t_INT) pari_err(talker,"non integral index in prodinf1");
  a = setloop(a);
  av = avma; lim = stack_lim(av,1);
  fl=0; G = -bit_accuracy(prec)-5;
  for(;;)
  {
    p2 = eval(a, E); p1 = gaddgs(p2,1);
    if (gequal0(p1)) { x = p1; break; }
    x = gmul(x,p1); a = incloop(a);
    if (gequal0(p2) || gexpo(p2) <= G) { if (++fl==3) break; } else fl=0;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prodinf1");
      x = gerepileupto(av,x);
    }
  }
  return gerepilecopy(av0,x);
}
GEN
prodinf0(GEN a, GEN code, long flag, long prec)
{
  switch(flag)
  {
    case 0: EXPR_WRAP(code, prodinf (EXPR_ARG, a, prec));
    case 1: EXPR_WRAP(code, prodinf1(EXPR_ARG, a, prec));
  }
  pari_err(flagerr);
  return NULL; /* not reached */
}

GEN
prodeuler(void *E, GEN (*eval)(GEN,void*), GEN ga, GEN gb, long prec)
{
  long p[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
  ulong a, b;
  pari_sp av, av0 = avma, lim;
  GEN prime = p, x = real_1(prec);
  byteptr d;

  av = avma;
  d = prime_loop_init(ga,gb, &a,&b, (ulong*)&prime[2]);
  if (!d) { avma = av; return x; }

  av = avma;
  lim = stack_lim(avma,1);
  while ((ulong)prime[2] < b)
  {
    x = gmul(x, eval(prime, E));
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prodeuler");
      x = gerepilecopy(av, x);
    }
    NEXT_PRIME_VIADIFF(prime[2], d);
  }
  if ((ulong)prime[2] == b) x = gmul(x, eval(prime, E));
  return gerepilecopy(av0,x);
}
GEN
prodeuler0(GEN a, GEN b, GEN code, long prec)
{ EXPR_WRAP(code, prodeuler(EXPR_ARG, a, b, prec)); }

GEN
direuler(void *E, GEN (*eval)(GEN,void*), GEN ga, GEN gb, GEN c)
{
  long pp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
  ulong a, b, i, k, n, p;
  pari_sp av0 = avma, av, lim = stack_lim(av0, 1);
  long j, tx, lx;
  GEN x, y, s, polnum, polden, prime = pp;
  byteptr d;

  d = prime_loop_init(ga,gb, &a,&b, (ulong*)&prime[2]);
  n = c? itou(c): b;
  if (!d || b < 2 || (c && signe(c) < 0)) return mkvec(gen_1);
  if (n < b) b = n;

  y = cgetg(n+1,t_VEC); av = avma;
  x = zerovec(n); gel(x,1) = gen_1; p = prime[2];
  while (p <= b)
  {
    s = eval(prime, E);
    polnum = numer(s);
    polden = denom(s);
    tx = typ(polnum);
    if (is_scalar_t(tx))
    {
      if (!gequal1(polnum))
      {
        if (!gequalm1(polnum)) pari_err(talker,"constant term != 1 in direuler");
        polden = gneg(polden);
      }
    }
    else
    {
      ulong k1, q, qlim;
      if (tx != t_POL) pari_err(typeer,"direuler");
      lx = degpol(polnum);
      if (lx < 0) pari_err(talker,"constant term != 1 in direuler");
      c = gel(polnum,2);
      if (!gequal1(c))
      {
        if (!gequalm1(c)) pari_err(talker,"constant term != 1 in direuler");
        polnum = gneg(polnum);
        polden = gneg(polden);
      }
      for (i=1; i<=n; i++) y[i]=x[i];
      q = p; qlim = n/p;
      for (j = 1; q<=n && j<=lx; j++)
      {
        c = gel(polnum,j+2);
        if (!gequal0(c))
          for (k=1,k1=q; k1<=n; k1+=q,k++)
            gel(x,k1) = gadd(gel(x,k1), gmul(c,gel(y,k)));
        if (q > qlim) break;
        q *= p;
      }
    }
    tx = typ(polden);
    if (is_scalar_t(tx))
    {
      if (!gequal1(polden)) pari_err(talker,"constant term != 1 in direuler");
    }
    else
    {
      if (tx != t_POL) pari_err(typeer,"direuler");
      c = gel(polden,2);
      if (!gequal1(c)) pari_err(talker,"constant term != 1 in direuler");
      lx = degpol(polden);
      for (i=p; i<=n; i+=p)
      {
        s = gen_0; k = i;
        for (j = 1; !(k%p) && j<=lx; j++)
        {
          c = gel(polden,j+2); k /= p;
          if (!gequal0(c)) s = gadd(s, gmul(c,gel(x,k)));
        }
        gel(x,i) = gsub(gel(x,i),s);
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"direuler");
      x = gerepilecopy(av, x);
    }
    NEXT_PRIME_VIADIFF(p, d);
    prime[2] = p;
  }
  return gerepilecopy(av0,x);
}
GEN
direuler0(GEN a, GEN b, GEN code, GEN c)
{ EXPR_WRAP(code, direuler(EXPR_ARG, a, b, c)); }

/********************************************************************/
/**                                                                **/
/**                       VECTORS & MATRICES                       **/
/**                                                                **/
/********************************************************************/

GEN
vecteur(GEN nmax, GEN code)
{
  GEN y,p1;
  long i,m;
  long c[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};

  m = gtos(nmax);
  if (m < 0)  pari_err(talker,"negative number of components in vector");
  if (!code) return zerovec(m);
  y = cgetg(m+1,t_VEC); push_lex(c, code);
  for (i=1; i<=m; i++)
  {
    c[2] = i; p1 = closure_evalnobrk(code);
    gel(y,i) = isonstack(p1)? p1 : gcopy(p1);
    set_lex(-1,c);
  }
  pop_lex(1); return y;
}

GEN
vecteursmall(GEN nmax, GEN code)
{
  GEN y;
  long i,m;
  long c[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};

  m = gtos(nmax);
  if (m < 0)  pari_err(talker,"negative number of components in vector");
  if (!code) return const_vecsmall(m, 0);
  y = cgetg(m+1,t_VECSMALL); push_lex(c,code);
  for (i=1; i<=m; i++)
  {
    c[2] = i;
    y[i] = gtos(closure_evalnobrk(code));
    set_lex(-1,c);
  }
  pop_lex(1); return y;
}

GEN
vvecteur(GEN nmax, GEN n)
{
  GEN y = vecteur(nmax,n);
  settyp(y,t_COL); return y;
}

GEN
matrice(GEN nlig, GEN ncol, GEN code)
{
  GEN y, z, p1;
  long i, j, m, n;
  long c1[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 1};
  long c2[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 1};

  m = gtos(ncol);
  n = gtos(nlig);
  if (m < 0) pari_err(talker,"negative number of columns in matrix");
  if (n < 0) pari_err(talker,"negative number of rows in matrix");
  if (!m) return cgetg(1,t_MAT);
  if (!code || !n) return zeromatcopy(n, m);
  push_lex(c1,code);
  push_lex(c2,NULL); y = cgetg(m+1,t_MAT);
  for (i=1; i<=m; i++)
  {
    c2[2] = i; z = cgetg(n+1,t_COL); gel(y,i) = z;
    for (j=1; j<=n; j++)
    {
      c1[2] = j; p1 = closure_evalnobrk(code);
      gel(z,j) = isonstack(p1)? p1 : gcopy(p1);
      set_lex(-2,c1);
      set_lex(-1,c2);
    }
  }
  pop_lex(2); return y;
}

/********************************************************************/
/**                                                                **/
/**                         SUMMING SERIES                         **/
/**                                                                **/
/********************************************************************/
GEN
polzag(long n, long m)
{
  pari_sp av = avma;
  long k, d = n - m;
  GEN A, Bx, g, s;

  if (d <= 0 || m < 0) return gen_0;
  A  = mkpoln(2, stoi(-2), gen_1); /* 1 - 2x */
  Bx = mkpoln(3, stoi(-2), gen_2, gen_0); /* 2x - 2x^2 */
  g = gmul(poleval(ZX_deriv(polchebyshev1(d,0)), A), gpowgs(Bx, (m+1)>>1));
  for (k = m; k >= 0; k--)
    g = (k&1)? ZX_deriv(g): gadd(gmul(A,g), gmul(Bx,ZX_deriv(g)));
  s = mulii(sqru(d), mpfact(m+1));
  return gerepileupto(av, gdiv(g,s));
}

#ifdef _MSC_VER /* Bill Daly: work around a MSVC bug */
#pragma optimize("g",off)
#endif
static GEN
polzagreel(long n, long m, long prec)
{
  const long d = n - m, d2 = d<<1, r = (m+1)>>1;
  long j, k, k2;
  pari_sp av = avma;
  GEN Bx, g, h, v, b, s;

  if (d <= 0 || m < 0) return gen_0;
  Bx = mkpoln(3, gen_1, gen_1, gen_0); /* x + x^2 */
  v = cgetg(d+1,t_VEC);
  g = cgetg(d+1,t_VEC);
  gel(v,d) = gen_1; b = stor(d2, prec);
  gel(g,d) = b;
  for (k = 1; k < d; k++)
  {
    gel(v,d-k) = gen_1;
    for (j=1; j<k; j++)
      gel(v,d-k+j) = addii(gel(v,d-k+j), gel(v,d-k+j+1));
    /* v[d-k+j] = binom(k, j), j = 0..k */
    k2 = k+k; b = divri(mulri(b,mulss(d2-k2+1,d2-k2)), mulss(k2,k2+1));
    for (j=1; j<=k; j++)
      gel(g,d-k+j) = mpadd(gel(g,d-k+j), mulri(b,gel(v,d-k+j)));
    gel(g,d-k) = b;
  }
  g = gmul(RgV_to_RgX(g,0), gpowgs(Bx,r));
  for (j=0; j<=r; j++)
  {
    if (j) g = RgX_deriv(g);
    if (j || !(m&1))
    {
      h = cgetg(n+3,t_POL);
      h[1] = evalsigne(1);
      h[2] = g[2];
      for (k=1; k<n; k++)
        gel(h,k+2) = gadd(gmulsg(k+k+1,gel(g,k+2)), gmulsg(k<<1,gel(g,k+1)));
      gel(h,n+2) = gmulsg(n<<1, gel(g,n+1));
      g = h;
    }
  }
  g = gmul2n(g, r-1);
  s = mului(d, mpfact(m+1));
  return gerepileupto(av, gdiv(g,s));
}

#ifdef _MSC_VER
#pragma optimize("g",on)
#endif
GEN
sumalt(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  long k, N;
  pari_sp av = avma;
  GEN s, az, c, e1, d;

  if (typ(a) != t_INT) pari_err(talker,"non integral index in sumalt");
  e1 = addsr(3, sqrtr(stor(8,prec)));
  N = (long)(0.4*(bit_accuracy(prec) + 7));
  d = powru(e1,N);
  d = shiftr(addrr(d, invr(d)),-1);
  az = gen_m1; c = d;
  s = gen_0;
  for (k=0; ; k++)
  {
    c = gadd(az,c); s = gadd(s, gmul(c, eval(a, E)));
    az = diviiexact(mulii(mulss(N-k,N+k),shifti(az,1)),mulss(k+1,k+k+1));
    if (k==N-1) break;
    a = addsi(1,a);
  }
  return gerepileupto(av, gdiv(s,d));
}

GEN
sumalt2(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  long k, N;
  pari_sp av = avma;
  GEN s, dn, pol;

  if (typ(a) != t_INT) pari_err(talker,"non integral index in sumalt");
  N = (long)(0.31*(bit_accuracy(prec) + 5));
  pol = polzagreel(N,N>>1,prec+1);
  pol = RgX_div_by_X_x(pol, gen_1, &dn);
  N = degpol(pol);
  s = gen_0;
  for (k=0; k<=N; k++)
  {
    s = gadd(s, gmul(gel(pol,k+2), eval(a, E)));
    if (k == N) break;
    a = addsi(1,a);
  }
  return gerepileupto(av, gdiv(s,dn));
}

GEN
sumalt0(GEN a, GEN code, long flag, long prec)
{
  switch(flag)
  {
    case 0: EXPR_WRAP(code, sumalt (EXPR_ARG,a,prec));
    case 1: EXPR_WRAP(code, sumalt2(EXPR_ARG,a,prec));
    default: pari_err(flagerr);
  }
  return NULL; /* not reached */
}

GEN
sumpos(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  long k, kk, N, G;
  pari_sp av = avma;
  GEN r, reel, s, az, c, x, e1, d, *stock;

  if (typ(a) != t_INT) pari_err(talker,"non integral index in sumpos");

  a = subis(a,1); reel = cgetr(prec);
  e1 = addsr(3, sqrtr(stor(8,prec)));
  N = (long)(0.4*(bit_accuracy(prec) + 7));
  d = powru(e1,N);
  d = shiftr(addrr(d, invr(d)),-1);
  az = gen_m1; c = d;
  s = gen_0;

  G = -bit_accuracy(prec) - 5;
  stock = (GEN*)new_chunk(N+1); for (k=1; k<=N; k++) stock[k] = NULL;
  for (k=0; k<N; k++)
  {
    if (odd(k) && stock[k]) x = stock[k];
    else
    {
      pari_sp av2 = avma;
      x = gen_0; r = utoipos(2*k+2);
      for(kk=0;;kk++)
      {

        long ex;
        affgr(eval(addii(r,a), E), reel);
        ex = expo(reel) + kk; setexpo(reel,ex);
        x = mpadd(x,reel); if (kk && ex < G) break;
        r = shifti(r,1);
      }
      x = gerepileupto(av2, x);
      if (2*k < N) stock[2*k+1] = x;
      affgr(eval(addsi(k+1,a), E), reel);
      x = addrr(reel, gmul2n(x,1));
    }
    c = addir(az,c);
    s = mpadd(s, mulrr(x, k&1? negr(c): c));
    az = diviiexact(mulii(mulss(N-k,N+k),shifti(az,1)),mulss(k+1,k+k+1));
  }
  return gerepileupto(av, gdiv(s,d));
}

GEN
sumpos2(void *E, GEN (*eval)(GEN,void*), GEN a, long prec)
{
  long k, kk, N, G;
  pari_sp av = avma;
  GEN r, reel, s, pol, dn, x, *stock;

  if (typ(a) != t_INT) pari_err(talker,"non integral index in sumpos2");

  a = subis(a,1); reel = cgetr(prec);
  N = (long)(0.31*(bit_accuracy(prec) + 5));

  G = -bit_accuracy(prec) - 5;
  stock = (GEN*)new_chunk(N+1); for (k=1; k<=N; k++) stock[k] = NULL;
  for (k=1; k<=N; k++)
    if (odd(k) || !stock[k])
    {
      pari_sp av2 = avma;
      x = gen_0; r = utoipos(2*k);
      for(kk=0;;kk++)
      {
        long ex;
        affgr(eval(addii(r,a), E), reel);
        ex = expo(reel) + kk; setexpo(reel,ex);
        x = mpadd(x,reel); if (kk && ex < G) break;
        r = shifti(r,1);
      }
      x = gerepileupto(av2, x);
      if (2*k-1 < N) stock[2*k] = x;
      affgr(eval(addsi(k,a), E), reel);
      stock[k] = addrr(reel, gmul2n(x,1));
    }
  s = gen_0;
  pol = polzagreel(N,N>>1,prec+1);
  pol = RgX_div_by_X_x(pol, gen_1, &dn);
  for (k=1; k<=lg(pol)-2; k++)
  {
    GEN p1 = gmul(gel(pol,k+1),stock[k]);
    if (!odd(k)) p1 = gneg_i(p1);
    s = gadd(s,p1);
  }
  return gerepileupto(av, gdiv(s,dn));
}

GEN
sumpos0(GEN a, GEN code, long flag, long prec)
{
  switch(flag)
  {
    case 0: EXPR_WRAP(code, sumpos (EXPR_ARG,a,prec));
    case 1: EXPR_WRAP(code, sumpos2(EXPR_ARG,a,prec));
    default: pari_err(flagerr);
  }
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**            SEARCH FOR REAL ZEROS of an expression              **/
/**                                                                **/
/********************************************************************/
/* Brent's method, [a,b] bracketing interval */
GEN
zbrent(void *E, GEN (*eval)(GEN,void*), GEN a, GEN b, long prec)
{
  long sig, iter, itmax;
  pari_sp av = avma;
  GEN c,d,e,tol,tol1,min1,min2,fa,fb,fc,p,q,r,s,xm;

  a = gtofp(a,prec);
  b = gtofp(b,prec); sig = cmprr(b,a);
  if (!sig) return gerepileupto(av, a);
  if (sig < 0) { c=a; a=b; b=c; } else c = b;

  fa = eval(a, E);
  fb = eval(b, E);
  if (gsigne(fa)*gsigne(fb) > 0) pari_err(talker,"roots must be bracketed in solve");
  itmax = (prec * (2*BITS_IN_LONG)) + 1;
  tol = real2n(5-bit_accuracy(prec), 3);
  fc = fb;
  e = d = NULL; /* gcc -Wall */
  for (iter=1; iter<=itmax; iter++)
  {
    if (gsigne(fb)*gsigne(fc) > 0)
    {
      c = a; fc = fa; e = d = subrr(b,a);
    }
    if (gcmp(gabs(fc,0),gabs(fb,0)) < 0)
    {
      a = b; b = c; c = a; fa = fb; fb = fc; fc = fa;
    }
    tol1 = mulrr(tol, gmax(tol,absr(b)));
    xm = shiftr(subrr(c,b),-1);
    if (cmprr(absr(xm),tol1) <= 0 || gequal0(fb)) break; /* SUCCESS */

    if (cmprr(absr(e),tol1) >= 0 && gcmp(gabs(fa,0),gabs(fb,0)) > 0)
    { /* attempt interpolation */
      s = gdiv(fb,fa);
      if (cmprr(a,c)==0)
      {
        p = gmul2n(gmul(xm,s),1); q = gsubsg(1,s);
      }
      else
      {
        q = gdiv(fa,fc); r = gdiv(fb,fc);
        p = gmul2n(gmul(gsub(q,r),gmul(xm,q)),1);
        p = gmul(s, gsub(p, gmul(gsub(b,a),gsubgs(r,1))));
        q = gmul(gmul(gsubgs(q,1),gsubgs(r,1)),gsubgs(s,1));
      }
      if (gsigne(p) > 0) q = gneg_i(q); else p = gneg_i(p);
      min1 = gsub(gmulsg(3,gmul(xm,q)), gabs(gmul(q,tol1),0));
      min2 = gabs(gmul(e,q),0);
      if (gcmp(gmul2n(p,1), gmin(min1,min2)) < 0)
        { e = d; d = gdiv(p,q); } /* interpolation OK */
      else
        { d = xm; e = d; } /* failed, use bisection */
    }
    else { d = xm; e = d; } /* bound decreasing too slowly, use bisection */
    a = b; fa = fb;
    if (gcmp(gabs(d,0),tol1) > 0) b = gadd(b,d);
    else if (gsigne(xm) > 0)      b = addrr(b,tol1);
    else                          b = subrr(b,tol1);
    fb = eval(b, E);
  }
  if (iter > itmax) pari_err(talker,"too many iterations in solve");
  return gerepileuptoleaf(av, rcopy(b));
}

GEN
zbrent0(GEN a, GEN b, GEN code, long prec)
{ EXPR_WRAP(code, zbrent(EXPR_ARG, a,b, prec)); }

/* x = solve_start(&D, a, b, prec)
 * while (x) {
 *   y = ...(x);
 *   x = solve_next(&D, y);
 * }
 * return D.res; */

/********************************************************************/
/**                                                                **/
/**            Numerical derivation                                **/
/**                                                                **/
/********************************************************************/

/* Rationale: (f(2^-e) - f(-2^-e) + O(2^-pr)) / (2 * 2^-e) = f'(0) + O(2^-2e)
 * since 2nd derivatives cancel.
 *   prec(LHS) = pr - e
 *   prec(RHS) = 2e, equal when  pr = 3e = 3/2 fpr (fpr = required final prec)
 *
 * For f'(x), x far from 0: prec(LHS) = pr - e - expo(x)
 * --> pr = 3/2 fpr + expo(x) */
GEN
derivnum(void *E, GEN (*eval)(GEN,void*), GEN x, long prec)
{
  GEN eps,a,b, y;
  long fpr, pr, l, e, ex;
  pari_sp av = avma;
  fpr = precision(x)-2; /* required final prec (in sig. words) */
  if (fpr == -2) fpr = prec-2;
  ex = gexpo(x);
  if (ex < 0) ex = 0; /* at 0 */
  pr = (long)ceil(fpr * 1.5 + (ex / BITS_IN_LONG));
  l = 2+pr;
  e = fpr * (BITS_IN_LONG/2); /* 1/2 required prec (in sig. bits) */

  eps = real2n(-e, l);
  y = gtofp(gsub(x, eps), l); a = eval(y, E);
  y = gtofp(gadd(x, eps), l); b = eval(y, E);
  setexpo(eps, e-1);
  return gerepileupto(av, gmul(gsub(b,a), eps));
}

GEN
derivfun(void *E, GEN (*eval)(GEN,void*), GEN x, long prec)
{
  pari_sp av = avma;
  long vx;
  switch(typ(x))
  {
  case t_REAL: case t_INT: case t_FRAC: case t_COMPLEX:
    return derivnum(E,eval, x, prec);
  case t_POL:
    x = RgX_to_ser(x, precdl+2+1); /* +1 because deriv reduce the precision by 1 */
  case t_SER: /* FALL THROUGH */
    vx = varn(x);
    return gerepileupto(av, gdiv(deriv(eval(x, E),vx), deriv(x,vx)));
  default: pari_err(typeer, "formal derivation");
    return NULL; /*NOT REACHED*/
  }
}

GEN
derivnum0(GEN a, GEN code, long prec)
{
  EXPR_WRAP(code, derivfun (EXPR_ARG,a,prec));
}

struct deriv_data
{
  GEN code;
  GEN args;
};

static GEN deriv_eval(GEN x, void *E)
{
 struct deriv_data *data=(struct deriv_data *)E;
 gel(data->args,1)=x;
 return closure_callgenvec(data->code, data->args);
}

GEN
derivfun0(GEN code, GEN args, long prec)
{
  struct deriv_data E;
  E.code=code; E.args=args;
  return derivfun((void*)&E, deriv_eval, gel(args,1), prec);
}
