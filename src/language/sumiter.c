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

/********************************************************************/
/**                                                                **/
/**                   SUMS, PRODUCTS, ITERATIONS                   **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "anal.h"
extern void changevalue_p(entree *ep, GEN x);
extern GEN polint_i(GEN xa, GEN ya, GEN x, long n, GEN *ptdy);
extern void lisseq_void(char *t);

/********************************************************************/
/**                                                                **/
/**                        ITERATIONS                              **/
/**                                                                **/
/********************************************************************/

void
forpari(entree *ep, GEN a, GEN b, char *ch)
{
  pari_sp av, av0 = avma, lim;

  b = gcopy(b); av=avma; lim = stack_lim(av,1);
 /* gcopy nedeed in case b gets overwritten in ch, as in
  * b=10; for(a=1,b, print(a);b=1)
  */
  push_val(ep, a);
  while (gcmp(a,b) <= 0)
  {
    pari_sp av1=avma; lisseq_void(ch); avma=av1;
    if (loop_break()) break;
    a = (GEN) ep->value; a = typ(a) == t_INT? addis(a, 1): gadd(a,gun);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"forpari");
      a = gerepileupto(av,a);
    }
    changevalue_p(ep,a);
  }
  pop_val(ep); avma = av0;
}

static int negcmp(GEN x, GEN y) { return gcmp(y,x); }

void
forstep(entree *ep, GEN a, GEN b, GEN s, char *ch)
{
  long ss, i;
  pari_sp av, av0 = avma, lim;
  GEN v = NULL;
  int (*cmp)(GEN,GEN);

  b = gcopy(b); av=avma; lim = stack_lim(av,1);
  push_val(ep, a);
  if (is_vec_t(typ(s)))
  {
    v = s; s = gzero;
    for (i=lg(v)-1; i; i--) s = gadd(s,(GEN)v[i]);
  }
  ss = gsigne(s);
  if (!ss) err(talker, "step equal to zero in forstep");
  cmp = (ss > 0)? gcmp: negcmp;
  i = 0;
  while (cmp(a,b) <= 0)
  {
    pari_sp av1=avma; lisseq_void(ch); avma=av1;
    if (loop_break()) break;
    if (v)
    {
      if (++i >= lg(v)) i = 1;
      s = (GEN)v[i];
    }
    a = (GEN) ep->value; a = gadd(a,s);

    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"forstep");
      a = gerepileupto(av,a);
    }
    changevalue_p(ep,a);
  }
  pop_val(ep); avma = av0;
}

/* assume ptr is the address of a diffptr containing the succesive
 * differences between primes, and c = current prime (up to *p excluded)
 * return smallest prime >= a, update ptr */
static ulong
sinitp(ulong a, ulong c, byteptr *ptr)
{
  byteptr p = *ptr;
  if (a <= 0) a = 2;
  maxprime_check((ulong)a);
  while (a > c)
     NEXT_PRIME_VIADIFF(c,p);
  *ptr = p; return c;
}

/* value changed during the loop, replace by the first prime whose
   value is strictly larger than new value */
static void
update_p(entree *ep, byteptr *ptr, ulong prime[])
{
  GEN z = (GEN)ep->value;
  ulong a, c;

  if (typ(z) == t_INT) a = 1; else { z = gceil(z); a = 0; }
  if (lgefint(z) > 3) { prime[2] = (long)MAXULONG; /* = infinity */ return; }
  a += itou(z); c = prime[2];
  if (c < a)
    prime[2] = sinitp(a, c, ptr); /* increased */
  else if (c > a)
  { /* lowered, reset p */
    *ptr = diffptr;
    prime[2] = sinitp(a, 0, ptr);
  }
  changevalue_p(ep, (GEN)prime);
}

static byteptr
prime_loop_init(GEN ga, GEN gb, ulong *a, ulong *b, ulong prime[])
{
  byteptr d = diffptr;

  ga = gceil(ga); gb = gfloor(gb);
  if (typ(ga) != t_INT || typ(gb) != t_INT)
    err(typeer,"prime_loop_init");
  if (signe(gb) < 0) return NULL;
  if (signe(ga) < 0) ga = gun;
  if (lgefint(ga)>3 || lgefint(gb)>3)
  {
    if (cmpii(ga, gb) > 0) return NULL;
    err(primer1);
  }
  *a = itou(ga);
  *b = itou(gb); if (*a > *b) return NULL;
  maxprime_check(*b);
  prime[2] = sinitp(*a, 0, &d);
  return d;
}

void
forprime(entree *ep, GEN ga, GEN gb, char *ch)
{
  long p[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
  ulong *prime = (ulong*)p;
  ulong a, b;
  pari_sp av = avma;
  byteptr d;

  d = prime_loop_init(ga,gb, &a,&b, prime);
  if (!d) { avma = av; return; }

  avma = av; push_val(ep, (GEN)prime);
  while (prime[2] < b)
  {
    lisseq_void(ch); if (loop_break()) break;
    if (ep->value == prime)
      NEXT_PRIME_VIADIFF(prime[2], d);
    else
      update_p(ep, &d, prime);
    avma = av;
  }
  /* if b = P --> *d = 0 now and the loop wouldn't end if it read 'while
   * (prime[2] <= b)' */
  if (prime[2] == b) { lisseq_void(ch); (void)loop_break(); avma = av; }
  pop_val(ep);
}

void
fordiv(GEN a, entree *ep, char *ch)
{
  long i, l;
  pari_sp av2, av = avma;
  GEN t = divisors(a);

  push_val(ep, NULL); l=lg(t); av2 = avma;
  for (i=1; i<l; i++)
  {
    ep->value = (void*) t[i];
    lisseq_void(ch); if (loop_break()) break;
    avma = av2;
  }
  pop_val(ep); avma=av;
}

/* Embedded for loops:
 *   fl = 0: execute ch (a), where a = (ai) runs through all n-uplets in
 *     [m1,M1] x ... x [mn,Mn]
 *   fl = 1: impose a1 <= ... <= an
 *   fl = 2:        a1 <  ... <  an
 */
typedef struct {
  GEN *a, *m, *M;
  long n,fl;
  char *ch;
} fvdat;

/* general case */
static void
fvloop(long i, fvdat *d)
{
  d->a[i] = d->m[i];
  if (d->fl && i > 1)
  {
    GEN p1 = gsub(d->a[i], d->a[i-1]);
    if (gsigne(p1) < 0)
      d->a[i] = gadd(d->a[i], gceil(gneg_i(p1)));
    if (d->fl == 2 && gegal(d->a[i], d->a[i-1]))
      d->a[i] = gadd(d->a[i], gun);
  }
  if (i+1 == d->n)
    while (gcmp(d->a[i], d->M[i]) <= 0)
    {
      pari_sp av = avma; lisseq_void(d->ch); avma = av;
      if (loop_break()) { d->n = 0; return; }
      d->a[i] = gadd(d->a[i], gun);
    }
  else
    while (gcmp(d->a[i], d->M[i]) <= 0)
    {
      pari_sp av = avma; fvloop(i+1, d); avma = av;
      if (!d->n) return;
      d->a[i] = gadd(d->a[i], gun);
    }
}

/* we run through integers */
static void
fvloop_i(long i, fvdat *d)
{
  d->a[i] = setloop(d->m[i]);
  if (d->fl && i > 1)
  {
    int c = cmpii(d->a[i], d->a[i-1]);
    if (c < 0)
    {
      d->a[i] = setloop(d->a[i-1]);
      c = 0;
    }
    if (c == 0 && d->fl == 2)
      d->a[i] = incloop(d->a[i]);
  }
  if (i+1 == d->n)
    while (gcmp(d->a[i], d->M[i]) <= 0)
    {
      pari_sp av = avma; lisseq_void(d->ch); avma = av;
      if (loop_break()) { d->n = 0; return; }
      d->a[i] = incloop(d->a[i]);
    }
  else
    while (gcmp(d->a[i], d->M[i]) <= 0)
    {
      pari_sp av = avma; fvloop_i(i+1, d); avma = av;
      if (!d->n) return;
      d->a[i] = incloop(d->a[i]);
    }
}

void
forvec(entree *ep, GEN x, char *c, long flag)
{
  pari_sp av = avma;
  long tx = typ(x);
  fvdat D, *d = &D;

  if (!is_vec_t(tx)) err(talker,"not a vector in forvec");
  if (flag<0 || flag>2) err(flagerr);
  d->n = lg(x);
  d->ch = c;
  d->a = (GEN*)cgetg(d->n,t_VEC); push_val(ep, (GEN)d->a);
  if (d->n == 1) lisseq_void(d->ch);
  else
  {
    long i, t = t_INT;
    d->fl = flag;
    d->m = (GEN*)cgetg(d->n,t_VEC);
    d->M = (GEN*)cgetg(d->n,t_VEC);
    for (i=1; i<d->n; i++)
    {
      GEN *e = (GEN*) x[i];
      tx = typ(e);
      if (! is_vec_t(tx) || lg(e)!=3)
	err(talker,"not a vector of two-component vectors in forvec");
      if (gcmp(e[1],e[2]) > 0) d->n = 0;
      if (typ(e[1]) != t_INT) t = t_REAL;
      /* in case x is an ep->value and lisexpr(d->ch) kills it, have to copy */
      d->m[i] = gcopy(e[1]);
      d->M[i] = gcopy(e[2]);
    }
    if (t == t_INT) fvloop_i(1, d); else fvloop(1, d);
  }
  pop_val(ep); avma = av;
}

/********************************************************************/
/**                                                                **/
/**                              SUMS                              **/
/**                                                                **/
/********************************************************************/

GEN
somme(entree *ep, GEN a, GEN b, char *ch, GEN x)
{
  pari_sp av, av0 = avma, lim;
  GEN p1;

  if (typ(a) != t_INT) err(talker,"non integral index in sum");
  if (!x) x = gzero;
  if (gcmp(b,a) < 0) return gcopy(x);

  b = gfloor(b);
  a = setloop(a);
  av=avma; lim = stack_lim(av,1);
  push_val(ep, a);
  for(;;)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"sum");
    x=gadd(x,p1); if (cmpii(a,b) >= 0) break;
    a = incloop(a);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"sum");
      x = gerepileupto(av,x);
    }
    ep->value = (void*) a;
  }
  pop_val(ep); return gerepileupto(av0,x);
}

GEN
suminf(entree *ep, GEN a, char *ch, long prec)
{
  long fl, G;
  pari_sp tetpil, av0 = avma, av, lim;
  GEN p1,x = realun(prec);

  if (typ(a) != t_INT) err(talker,"non integral index in suminf");
  a = setloop(a);
  av = avma; lim = stack_lim(av,1);
  push_val(ep, a);
  fl=0; G = bit_accuracy(prec) + 5;
  for(;;)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"suminf");
    x = gadd(x,p1); a = incloop(a);
    if (gcmp0(p1) || gexpo(p1) <= gexpo(x)-G)
      { if (++fl==3) break; }
    else
      fl=0;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"suminf");
      x = gerepileupto(av,x);
    }
    ep->value = (void*)a;
  }
  pop_val(ep); tetpil=avma;
  return gerepile(av0,tetpil,gsub(x,gun));
}

GEN
divsum(GEN num, entree *ep, char *ch)
{
  pari_sp av = avma;
  GEN z, y = gzero, t = divisors(num);
  long i, l = lg(t);

  push_val(ep, NULL);
  for (i=1; i<l; i++)
  {
    ep->value = (void*) t[i];
    z = lisseq(ch);
    if (did_break()) err(breaker,"divsum");
    y = gadd(y, z);
  }
  pop_val(ep); return gerepileupto(av,y);
}

/********************************************************************/
/**                                                                **/
/**                           PRODUCTS                             **/
/**                                                                **/
/********************************************************************/

GEN
produit(entree *ep, GEN a, GEN b, char *ch, GEN x)
{
  pari_sp av, av0 = avma, lim;
  GEN p1;

  if (typ(a) != t_INT) err(talker,"non integral index in sum");
  if (!x) x = gun;
  if (gcmp(b,a) < 0) return gcopy(x);

  b = gfloor(b);
  a = setloop(a);
  av=avma; lim = stack_lim(av,1);
  push_val(ep, a);
  for(;;)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"prod");
    x = gmul(x,p1); if (cmpii(a,b) >= 0) break;
    a = incloop(a);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"prod");
      x = gerepileupto(av,x);
    }
    ep->value = (void*) a;
  }
  pop_val(ep); return gerepileupto(av0,x);
}

GEN
prodinf0(entree *ep, GEN a, char *ch, long flag, long prec)
{
  switch(flag)
  {
    case 0: return prodinf(ep,a,ch,prec);
    case 1: return prodinf1(ep,a,ch,prec);
  }
  err(flagerr);
  return NULL; /* not reached */
}

GEN
prodinf(entree *ep, GEN a, char *ch, long prec)
{
  pari_sp av0 = avma, av, lim;
  long fl,G;
  GEN p1,x = realun(prec);

  if (typ(a) != t_INT) err(talker,"non integral index in prodinf");
  a = setloop(a);
  av = avma; lim = stack_lim(av,1);
  push_val(ep, a);
  fl=0; G = -bit_accuracy(prec)-5;
  for(;;)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"prodinf");
    x=gmul(x,p1); a = incloop(a);
    if (gexpo(gsubgs(p1,1)) <= G) { if (++fl==3) break; } else fl=0;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"prodinf");
      x = gerepileupto(av,x);
    }
    ep->value = (void*)a;
  }
  pop_val(ep); return gerepilecopy(av0,x);
}

GEN
prodinf1(entree *ep, GEN a, char *ch, long prec)
{
  pari_sp av0 = avma, av, lim;
  long fl,G;
  GEN p1,p2,x = realun(prec);

  if (typ(a) != t_INT) err(talker,"non integral index in prodinf1");
  a = setloop(a);
  av = avma; lim = stack_lim(av,1);
  push_val(ep, a);
  fl=0; G = -bit_accuracy(prec)-5;
  for(;;)
  {
    p2 = lisexpr(ch); if (did_break()) err(breaker,"prodinf1");
    p1 = gadd(p2,gun); x=gmul(x,p1); a = incloop(a);
    if (gcmp0(p1) || gexpo(p2) <= G) { if (++fl==3) break; } else fl=0;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"prodinf1");
      x = gerepileupto(av,x);
    }
    ep->value = (void*)a;
  }
  pop_val(ep); return gerepilecopy(av0,x);
}

GEN
prodeuler(entree *ep, GEN ga, GEN gb, char *ch, long prec)
{
  long p[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
  ulong a,b, *prime = (ulong*)p;
  pari_sp av, av0 = avma, lim;
  GEN p1,x = realun(prec);
  byteptr d;

  av = avma;
  d = prime_loop_init(ga,gb, &a,&b, prime);
  if (!d) { avma = av; return x; }

  av = avma; push_val(ep, (GEN)prime);
  lim = stack_lim(avma,1);
  while (prime[2] < b)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"prodeuler");
    x = gmul(x,p1);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"prodeuler");
      x = gerepilecopy(av, x);
    }
    if (ep->value == prime)
      NEXT_PRIME_VIADIFF(prime[2], d);
    else
      update_p(ep, &d, prime);
  }
  /* cf forprime */
  if (prime[2] == b)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"prodeuler");
    x = gmul(x,p1);
  }
  pop_val(ep); return gerepilecopy(av0,x);
}

GEN
direulerall(entree *ep, GEN ga, GEN gb, char *ch, GEN c)
{
  long pp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
  ulong a, b, i, k, n, p, *prime = (ulong*)pp;
  pari_sp av0 = avma, av, lim = stack_lim(av0, 1);
  long j, tx, lx;
  GEN x, y, s, polnum, polden;
  byteptr d;

  d = prime_loop_init(ga,gb, &a,&b, prime);
  n = c? itou(c): b;
  if (!d || b < 2 || (c && signe(c) < 0)) return _vec(gun);
  if (n < b) b = n;
  push_val(ep, (GEN)prime);

  y = cgetg(n+1,t_VEC); av = avma;
  x = cgetg(n+1,t_VEC); x[1]=un; for (i=2; i<=n; i++) x[i]=zero;
  p = prime[2];
  while (p <= b)
  {
    s = lisexpr(ch); if (did_break()) err(breaker,"direuler");
    polnum = numer(s);
    polden = denom(s);
    tx = typ(polnum);
    if (is_scalar_t(tx))
    {
      if (!gcmp1(polnum))
      {
        if (!gcmp_1(polnum))
          err(talker,"constant term not equal to 1 in direuler");
        polden = gneg(polden);
      }
    }
    else
    {
      ulong k1, q, qlim;
      if (tx != t_POL) err(typeer,"direuler");
      c = truecoeff(polnum,0);
      if (!gcmp1(c))
      {
        if (!gcmp_1(c))
          err(talker,"constant term not equal to 1 in direuler");
        polnum = gneg(polnum);
        polden = gneg(polden);
      }
      for (i=1; i<=n; i++) y[i]=x[i];
      lx=degpol(polnum);
      q = p; qlim = n/p; j=1;
      while (q<=n && j<=lx)
      {
	c=(GEN)polnum[j+2];
	if (!gcmp0(c))
	  for (k=1,k1=q; k1<=n; k1+=q,k++)
	    x[k1] = ladd((GEN)x[k1], gmul(c,(GEN)y[k]));
        if (q > qlim) break;
	q*=p; j++;
      }
    }
    tx = typ(polden);
    if (is_scalar_t(tx))
    {
      if (!gcmp1(polden))
	err(talker,"constant term not equal to 1 in direuler");
    }
    else
    {
      if (tx != t_POL) err(typeer,"direuler");
      c = truecoeff(polden,0);
      if (!gcmp1(c)) err(talker,"constant term not equal to 1 in direuler");
      lx=degpol(polden);
      for (i=p; i<=n; i+=p)
      {
	s=gzero; k=i; j=1;
	while (!(k%p) && j<=lx)
	{
	  c=(GEN)polden[j+2]; k/=p; j++;
	  if (!gcmp0(c)) s=gadd(s,gmul(c,(GEN)x[k]));
	}
	x[i]=lsub((GEN)x[i],s);
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"direuler");
      x = gerepilecopy(av, x);
    }
    NEXT_PRIME_VIADIFF(p, d);
    prime[2] = p;
  }
  pop_val(ep); return gerepilecopy(av0,x);
}

GEN
direuler(entree *ep, GEN a, GEN b, char *ch)
{
  return direulerall(ep,a,b,ch,NULL);
}

/********************************************************************/
/**                                                                **/
/**                       VECTORS & MATRICES                       **/
/**                                                                **/
/********************************************************************/

GEN
vecteur(GEN nmax, entree *ep, char *ch)
{
  GEN y,p1;
  long i,m;
  long c[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};

  if (typ(nmax)!=t_INT || signe(nmax) < 0)
    err(talker,"bad number of components in vector");
  m=itos(nmax); y=cgetg(m+1,t_VEC);
  if (!ep || !ch)
  {
    for (i=1; i<=m; i++) y[i] = zero;
    return y;
  }
  push_val(ep, c);
  for (i=1; i<=m; i++)
  {
    c[2]=i; p1 = lisseq(ch);
    if (did_break()) err(breaker,"vector");
    y[i] = isonstack(p1)? (long)p1 : (long)forcecopy(p1);
  }
  pop_val(ep); return y;
}

GEN
vecteursmall(GEN nmax, entree *ep, char *ch)
{
  GEN y,p1;
  long i,m;
  long c[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};

  if (typ(nmax)!=t_INT || signe(nmax) < 0)
    err(talker,"bad number of components in vector");
  m=itos(nmax); y=cgetg(m+1,t_VECSMALL);
  if (!ep || !ch)
  {
    for (i=1; i<=m; i++) y[i] = 0;
    return y;
  }
  push_val(ep, c);
  for (i=1; i<=m; i++)
  {
    c[2]=i; p1 = lisseq(ch);
    if (did_break()) err(breaker,"vector");
    y[i] = itos(p1);
  }
  pop_val(ep); return y;
}


GEN
vvecteur(GEN nmax, entree *ep, char *ch)
{
  GEN y = vecteur(nmax,ep,ch);
  settyp(y,t_COL); return y;
}

GEN
matrice(GEN nlig, GEN ncol,entree *ep1, entree *ep2, char *ch)
{
  GEN y,z,p1;
  long i,j,m,n,s;
  long c1[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 1};
  long c2[]={evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 1};

  s=signe(ncol);
  if (ep1 == ep2 && ep1) err(talker, "identical index variables in matrix");
  if (typ(ncol)!=t_INT || s<0) err(talker,"bad number of columns in matrix");
  if (!s) return cgetg(1,t_MAT);

  s=signe(nlig);
  if (typ(nlig)!=t_INT || s<0) err(talker,"bad number of rows in matrix");
  m=itos(ncol)+1;
  n=itos(nlig)+1; y=cgetg(m,t_MAT);
  if (!s)
  {
    for (i=1; i<m; i++) y[i]=lgetg(1,t_COL);
    return y;
  }
  if (!ep1 || !ep2 || !ch)
  {
    for (i=1; i<m; i++)
    {
      z=cgetg(n,t_COL); y[i]=(long)z;
      for (j=1; j<n; j++) z[j] = zero;
    }
    return y;
  }
  push_val(ep1, c1);
  push_val(ep2, c2);
  for (i=1; i<m; i++)
  {
    c2[2]=i; z=cgetg(n,t_COL); y[i]=(long)z;
    for (j=1; j<n; j++)
    {
      c1[2]=j; p1=lisseq(ch);
      if (did_break()) err(breaker,"matrix");
      z[j] = isonstack(p1)? (long)p1 : (long)forcecopy(p1);
    }
  }
  pop_val(ep2);
  pop_val(ep1); return y;
}

/********************************************************************/
/**                                                                **/
/**                         SUMMING SERIES                         **/
/**                                                                **/
/********************************************************************/

GEN
sumalt0(entree *ep, GEN a, char *ch, long flag, long prec)
{
  switch(flag)
  {
    case 0: return sumalt(ep,a,ch,prec);
    case 1: return sumalt2(ep,a,ch,prec);
    default: err(flagerr);
  }
  return NULL; /* not reached */
}

GEN
sumpos0(entree *ep, GEN a, char *ch, long flag, long prec)
{
  switch(flag)
  {
    case 0: return sumpos(ep,a,ch,prec);
    case 1: return sumpos2(ep,a,ch,prec);
    default: err(flagerr);
  }
  return NULL; /* not reached */
}

GEN
sumalt(entree *ep, GEN a, char *ch, long prec)
{
  long k, N;
  pari_sp av = avma, tetpil;
  GEN s,az,c,x,e1,d;

  if (typ(a) != t_INT) err(talker,"non integral index in sumalt");

  push_val(ep, a);
  e1 = addsr(3,gsqrt(stoi(8),prec));
  N = (long)(0.4*(bit_accuracy(prec) + 7));
  d = gpowgs(e1,N);
  d = shiftr(addrr(d, ginv(d)),-1);
  az = negi(gun); c = d;
  s = gzero;
  for (k=0; ; k++)
  {
    x = lisexpr(ch); if (did_break()) err(breaker,"sumalt");
    c = gadd(az,c); s = gadd(s,gmul(x,c));
    az = divii(mulii(mulss(N-k,N+k),shifti(az,1)),mulss(k+1,k+k+1));
    if (k==N-1) break;
    a = addsi(1,a); ep->value = (void*) a;
  }
  tetpil = avma; pop_val(ep);
  return gerepile(av,tetpil,gdiv(s,d));
}

GEN
sumalt2(entree *ep, GEN a, char *ch, long prec)
{
  long k, N;
  pari_sp av = avma, tetpil;
  GEN x,s,dn,pol;

  if (typ(a) != t_INT) err(talker,"non integral index in sumalt");

  push_val(ep, a);
  N = (long)(0.31*(bit_accuracy(prec) + 5));
  pol = polzagreel(N,N>>1,prec+1);
  dn = poleval(pol,gun);
  pol[2] = lsub((GEN)pol[2],dn);
  pol = gdiv(pol, gsub(polx[0],gun));
  N = degpol(pol);
  s = gzero;
  for (k=0; k<=N; k++)
  {
    x = lisexpr(ch); if (did_break()) err(breaker,"sumalt2");
    s = gadd(s, gmul(x,(GEN)pol[k+2]));
    if (k == N) break;
    a = addsi(1,a); ep->value = (void*) a;
  }
  tetpil = avma; pop_val(ep);
  return gerepile(av,tetpil, gdiv(s,dn));
}

GEN
sumpos(entree *ep, GEN a, char *ch, long prec)
{
  long k, kk, N, G;
  pari_sp av = avma, tetpil;
  GEN p1,r,q1,reel,s,az,c,x,e1,d, *stock;

  if (typ(a) != t_INT) err(talker,"non integral index in sumpos");

  push_val(ep, NULL);
  a = subis(a,1); reel = cgetr(prec);
  e1 = addsr(3,gsqrt(stoi(8),prec));
  N = (long)(0.4*(bit_accuracy(prec) + 7));
  d = gpowgs(e1,N); d = shiftr(addrr(d, ginv(d)),-1);
  az = negi(gun); c = d; s = gzero;

  G = -bit_accuracy(prec) - 5;
  stock = (GEN*)new_chunk(N+1); for (k=1; k<=N; k++) stock[k] = NULL;
  for (k=0; k<N; k++)
  {
    if (odd(k) && stock[k]) x = stock[k];
    else
    {
      x = gzero; r = stoi(2*k+2);
      for(kk=0;;kk++)
      {
        long ex;
	q1 = addii(r,a); ep->value = (void*) q1;
        p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos");
        gaffect(p1,reel); ex = expo(reel)+kk; setexpo(reel,ex);
	x = gadd(x,reel); if (kk && ex < G) break;
        r = shifti(r,1);
      }
      if (2*k < N) stock[2*k+1] = x;
      q1 = addsi(k+1,a); ep->value = (void*) q1;
      p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos");
      gaffect(p1,reel); x = gadd(reel, gmul2n(x,1));
    }
    c = gadd(az,c); p1 = k&1? gneg_i(c): c;
    s = gadd(s,gmul(x,p1));
    az = divii(mulii(mulss(N-k,N+k),shifti(az,1)),mulss(k+1,k+k+1));
  }
  tetpil=avma; pop_val(ep);
  return gerepile(av,tetpil,gdiv(s,d));
}

GEN
sumpos2(entree *ep, GEN a, char *ch, long prec)
{
  long k, kk, N, G;
  pari_sp av = avma, tetpil;
  GEN p1,r,q1,reel,s,pol,dn,x, *stock;

  if (typ(a) != t_INT) err(talker,"non integral index in sumpos2");

  push_val(ep, a);
  a = subis(a,1); reel = cgetr(prec);
  N = (long)(0.31*(bit_accuracy(prec) + 5));

  G = -bit_accuracy(prec) - 5;
  stock = (GEN*)new_chunk(N+1); for (k=1; k<=N; k++) stock[k] = NULL;
  for (k=1; k<=N; k++)
  {
    if (odd(k) || !stock[k])
    {
      x = gzero; r = stoi(2*k);
      for(kk=0;;kk++)
      {
        long ex;
	q1 = addii(r,a); ep->value = (void*) q1;
        p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos2");
        gaffect(p1,reel); ex = expo(reel)+kk; setexpo(reel,ex);
	x=gadd(x,reel); if (kk && ex < G) break;
        r = shifti(r,1);
      }
      if (2*k-1 < N) stock[2*k] = x;
      q1 = addsi(k,a); ep->value = (void*) q1;
      p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos2");
      gaffect(p1,reel); stock[k] = gadd(reel, gmul2n(x,1));
    }
  }
  pop_val(ep); s = gzero;
  pol = polzagreel(N,N>>1,prec+1);
  dn = poleval(pol,gun);
  pol[2] = lsub((GEN)pol[2],dn);
  pol = gdiv(pol, gsub(gun,polx[0]));
  for (k=1; k<=lgef(pol)-2; k++)
  {
    p1 = gmul((GEN)pol[k+1],stock[k]);
    if (odd(k)) p1 = gneg_i(p1);
    s = gadd(s,p1);
  }
  tetpil=avma; return gerepile(av,tetpil,gdiv(s,dn));
}

/********************************************************************/
/**                                                                **/
/**                NUMERICAL INTEGRATION (Romberg)                 **/
/**                                                                **/
/********************************************************************/
typedef struct {
  entree *ep;
  char *ch;
} exprdat;

typedef struct {
  GEN (*f)(GEN,void *);
  void *E;
} invfun;

/* we need to make a copy in any case, cf forpari */
static GEN
fix(GEN a, long prec)
{
  GEN p = cgetr(prec);
  gaffect(a,p); return p;
}

#if 0
GEN
int_loop(entree *ep, char *ch)
{
  pari_sp av = avma;
  intstruct T;

  T.in = NULL;
  for(;;)
  {
    GEN x = Next(&T);
    if (!x) return gerepileupto(av, T.out);
    ep->value = (void*)x;
    T.in = lisexpr(ch);
  }
}
#endif

/* f(x) */
static GEN
_gp_eval(GEN x, void *dat)
{
  exprdat *E = (exprdat*)dat;
  E->ep->value = x;
  return lisexpr(E->ch);
}
/* 1/x^2 f(1/x) */
static GEN
_invf(GEN x, void *dat)
{
  invfun *S = (invfun*)dat;
  GEN y = ginv(x);
  return gmul(S->f(y, S->E), gsqr(y));
}

#define swap(a,b) { GEN _x = a; a = b; b = _x; }
static GEN
interp(GEN h, GEN s, long j, long lim, long KLOC)
{
  pari_sp av = avma;
  long e1,e2;
  GEN dss, ss = polint_i(h+j-KLOC,s+j-KLOC,gzero,KLOC+1,&dss);

  e1 = gexpo(ss);
  e2 = gexpo(dss);
  if (e1-e2 <= lim && e1 >= -lim) { avma = av; return NULL; }
  if (gcmp0(imag_i(ss))) ss = real_i(ss);
  return ss;
}

static GEN
qrom3(void *dat, GEN (*eval)(GEN,void *), GEN a, GEN b, long prec)
{
  const long JMAX = 25, KLOC = 4;
  GEN ss,s,h,p1,p2,qlint,del,x,sum;
  long j, j1, it, sig;
  pari_sp av;

  a = fix(a,prec);
  b = fix(b,prec);
  qlint = subrr(b,a); sig = signe(qlint);
  if (!sig)  return gzero;
  if (sig < 0) { setsigne(qlint,1); swap(a,b); }

  s = new_chunk(JMAX+KLOC-1);
  h = new_chunk(JMAX+KLOC-1);
  h[0] = (long)realun(prec);

  p1 = eval(a, dat); if (p1 == a) p1 = rcopy(p1);
  p2 = eval(b, dat);
  s[0] = lmul2n(gmul(qlint,gadd(p1,p2)),-1);
  for (it=1,j=1; j<JMAX; j++, it<<=1)
  {
    h[j] = lshiftr((GEN)h[j-1],-2);
    av = avma; del = divrs(qlint,it);
    x = addrr(a, shiftr(del,-1));
    for (sum = gzero, j1 = 1; j1 <= it; j1++, x = addrr(x,del))
      sum = gadd(sum, eval(x, dat));
    sum = gmul(sum,del); p1 = gadd((GEN)s[j-1], sum);
    s[j] = lpileupto(av, gmul2n(p1,-1));

    if (j >= KLOC && (ss = interp(h, s, j, bit_accuracy(prec)-j-6, KLOC)))
      return gmulsg(sig,ss);
  }
  return NULL;
}

static GEN
qrom2(void *dat, GEN (*eval)(GEN,void *), GEN a, GEN b, long prec)
{
  const long JMAX = 16, KLOC = 4;
  GEN ss,s,h,p1,qlint,del,ddel,x,sum;
  long j, j1, it, sig;
  pari_sp av;

  a = fix(a, prec);
  b = fix(b, prec);
  qlint = subrr(b,a); sig = signe(qlint);
  if (!sig)  return gzero;
  if (sig < 0) { setsigne(qlint,1); swap(a,b); }

  s = new_chunk(JMAX+KLOC-1);
  h = new_chunk(JMAX+KLOC-1);
  h[0] = (long)realun(prec);

  p1 = shiftr(addrr(a,b),-1);
  s[0] = lmul(qlint, eval(p1, dat));
  for (it=1, j=1; j<JMAX; j++, it*=3)
  {
    h[j] = ldivrs((GEN)h[j-1],9);
    av = avma; del = divrs(qlint,3*it); ddel = shiftr(del,1);
    x = addrr(a, shiftr(del,-1));
    for (sum = gzero, j1 = 1; j1 <= it; j1++)
    {
      sum = gadd(sum, eval(x, dat)); x = addrr(x,ddel);
      sum = gadd(sum, eval(x, dat)); x = addrr(x,del);
    }
    sum = gmul(sum,del); p1 = gdivgs((GEN)s[j-1],3);
    s[j] = lpileupto(av, gadd(p1,sum));

    if (j >= KLOC && (ss = interp(h, s, j, bit_accuracy(prec)-(3*j/2)-6, KLOC)))
      return gmulsg(sig, ss);
  }
  return NULL;
}

/* integrate after change of variables x --> 1/x */
static GEN
qromi(void *E, GEN (*eval)(GEN, void*), GEN a, GEN b, long prec)
{
  GEN A = ginv(b), B = ginv(a);
  invfun S;
  S.f = eval;
  S.E = E; return qrom2(&S, &_invf, A, B, prec);
}

/* a < b, assume b "small" (< 100 say) */
static GEN
rom_bsmall(void *E, GEN (*eval)(GEN, void*), GEN a, GEN b, long prec)
{
  if (gcmpgs(a,-100) >= 0) return qrom2(E,eval,a,b,prec);
  if (b == gun || gcmpgs(b, -1) >= 0)
  { /* a < -100, b >= -1 */
    GEN _1 = negi(gun); /* split at -1 */
    return gadd(qromi(E,eval,a,_1,prec),
                qrom2(E,eval,_1,b,prec));
  }
  /* a < -100, b < -1 */
  return qromi(E,eval,a,b,prec);
}

static GEN
rombint(void *E, GEN (*eval)(GEN, void*), GEN a, GEN b, long prec)
{
  long l = gcmp(b,a);
  GEN z;

  if (!l) return gzero;
  if (l < 0) swap(a,b);
  if (gcmpgs(b,100) >= 0)
  {
    if (gcmpgs(a,1) >= 0)
      z = qromi(E,eval,a,b,prec);
    else /* split at 1 */
      z = gadd(rom_bsmall(E,eval,a,gun,prec), qromi(E,eval,gun,b,prec));
  }
  else
    z = rom_bsmall(E,eval,a,b,prec);
  if (l < 0) z = gneg(z);
  return z;
}

GEN
intnum(void *E, GEN (*eval)(GEN,void*), GEN a, GEN b, long flag, long prec)
{
  pari_sp av = avma;
  GEN z;
  switch(flag)
  {
    case 0: z = qrom3  (E,eval,a,b,prec); break;
    case 1: z = rombint(E,eval,a,b,prec); break;
    case 2: z = qromi  (E,eval,a,b,prec); break;
    case 3: z = qrom2  (E,eval,a,b,prec); break;
    default: err(flagerr); z = NULL;
  }
  if (!z) err(intger2);
  return gerepileupto(av, z);
}

GEN
intnum0(entree *ep, GEN a, GEN b, char *ch, long flag, long prec)
{
  exprdat E;
  GEN z;

  E.ch = ch;
  E.ep = ep; push_val(ep, NULL);
  z = intnum(&E, &_gp_eval, a,b, flag, prec);
  pop_val(ep); return z;
}
/********************************************************************/
/**                                                                **/
/**                  ZAGIER POLYNOMIALS (for sumalt)               **/
/**                                                                **/
/********************************************************************/

GEN
polzag(long n, long m)
{
  pari_sp av = avma;
  long k, d = n - m;
  GEN A, Bx, g, s;

  if (d <= 0 || m < 0) return gzero;
  A  = coefs_to_pol(2, stoi(-2), gun); /* 1 - 2x */
  Bx = coefs_to_pol(3, stoi(-2), gdeux, gzero); /* 2x - 2x^2 */
  g = gmul(poleval(derivpol(tchebi(d,0)), A), gpowgs(Bx, (m+1)>>1));
  for (k = m; k >= 0; k--)
    g = (k&1)? derivpol(g): gadd(gmul(A,g), gmul(Bx,derivpol(g)));
  s = mulsi(d, mulsi(d, mpfact(m+1)));
  return gerepileupto(av, gdiv(g,s));
} 

#ifdef _MSC_VER /* Bill Daly: work around a MSVC bug */
#pragma optimize("g",off)
#endif
GEN
polzagreel(long n, long m, long prec)
{
  long r, j, k, k2, d = n - m, d2 = d<<1;
  pari_sp av = avma;
  GEN Bx, g, h, v, b, s;

  if (d <= 0 || m < 0) return gzero;
  Bx = coefs_to_pol(3, gun, gun, gzero); /* x + x^2 */
  v = cgetg(d+1,t_VEC);
  g = cgetg(d+1,t_VEC);
  v[d] = un; b = stor(d2, prec);
  g[d] = (long)b;
  for (k = 1; k < d; k++)
  {
    v[d-k] = un;
    for (j=1; j<k; j++)
      v[d-k+j] = laddii((GEN)v[d-k+j], (GEN)v[d-k+j+1]);
    /* v[d-k+j] = binom(k, j), j = 0..k */
    k2 = k+k; b = divri(mulri(b,mulss(d2-k2+1,d2-k2)), mulss(k2,k2+1));
    for (j=1; j<=k; j++)
      g[d-k+j] = lmpadd((GEN)g[d-k+j], mulri(b,(GEN)v[d-k+j]));
    g[d-k] = (long)b;
  }
  r = (m+1)>>1;
  g = gmul(vec_to_pol(g,0), gpowgs(Bx,r));
  for (j=0; j<=r; j++)
  {
    if (j) g = derivpol(g);
    if (j || !(m&1))
    {
      h = cgetg(n+3,t_POL);
      h[1] = evalsigne(1)|evallgef(n+3);
      h[2] = g[2];
      for (k=1; k<n; k++)
	h[k+2] = ladd(gmulsg(k+k+1,(GEN)g[k+2]), gmulsg(k<<1,(GEN)g[k+1]));
      h[n+2] = lmulsg(n<<1, (GEN)g[n+1]);
      g = h;
    }
  }
  g = m? gmul2n(g,(m-1)>>1): gmul2n(g,-1);
  s = mulsi(d, mpfact(m+1));
  return gerepileupto(av, gdiv(g,s));
}
#ifdef _MSC_VER
#pragma optimize("g",on)
#endif

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

  a = fix(a,prec);
  b = fix(b,prec); sig=cmprr(b,a);
  if (!sig) { avma = av; return gzero; }
  if (sig < 0) { c=a; a=b; b=c; } else c = b;

  fa = eval(a, E);
  fb = eval(b, E);
  if (gsigne(fa)*gsigne(fb) > 0) err(talker,"roots must be bracketed in solve");
  itmax = (prec<<(TWOPOTBITS_IN_LONG+1)) + 1;
  tol = real2n(5-bit_accuracy(prec), 3);
  fc=fb;
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
    if (cmprr(absr(xm),tol1) <= 0 || gcmp0(fb)) break; /* SUCCESS */

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
  if (iter > itmax) err(talker,"too many iterations in solve");
  return gerepileuptoleaf(av, rcopy(b));
}

GEN
zbrent0(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  exprdat E;
  GEN z;

  E.ch = ch;
  E.ep = ep; push_val(ep, NULL);
  z = zbrent(&E, &_gp_eval, a,b, prec);
  pop_val(ep); return z;
}
