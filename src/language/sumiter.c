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

/********************************************************************/
/**                                                                **/
/**                        ITERATIONS                              **/
/**                                                                **/
/********************************************************************/

void
forpari(entree *ep, GEN a, GEN b, char *ch)
{
  long av,av0 = avma, lim;

  b = gcopy(b); av=avma; lim = stack_lim(av,1);
 /* gcopy nedeed in case b gets overwritten in ch, as in
  * b=10; for(a=1,b, print(a);b=1)
  */
  push_val(ep, a);
  while (gcmp(a,b) <= 0)
  {
    long av1=avma; (void)lisseq(ch); avma=av1;
    if (loop_break()) break;
    a = (GEN) ep->value; a = gadd(a,gun);
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
  long ss, av,av0 = avma, lim, i;
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
    long av1=avma; (void)lisseq(ch); avma=av1;
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
static long
sinitp(long a, long c, byteptr *ptr)
{
  byteptr p = *ptr;
  if (a <= 0) a = 2;
  if (maxprime() < (ulong)a) err(primer1);
  while (a > c) c += *p++;
  *ptr = p; return c;
}

/* value changed during the loop, replace by the first prime whose
   value is strictly larger than new value */
static void
update_p(entree *ep, byteptr *ptr, long prime[])
{
  GEN z = (GEN)ep->value;
  long a, c;

  if (typ(z) == t_INT) a = 1; else { z = gceil(z); a = 0; }
  if (is_bigint(z)) { prime[2] = -1; /* = infinity */ return; }
  a += itos(z); c = prime[2];
  if (c < a)
    prime[2] = sinitp(a, c, ptr); /* increased */
  else if (c > a)
  { /* lowered, reset p */
    *ptr = diffptr;
    prime[2] = sinitp(a, 0, ptr);
  }
  changevalue_p(ep, prime); 
}

static byteptr
prime_loop_init(GEN ga, GEN gb, long *a, long *b, long prime[])
{
  byteptr p = diffptr;
  ulong P;

  ga = gceil(ga); gb = gfloor(gb);
  if (typ(ga) != t_INT || typ(gb) != t_INT)
    err(typeer,"prime_loop_init");
  if (is_bigint(ga) || is_bigint(gb))
  {
    if (cmpii(ga, gb) > 0) return NULL;
    err(primer1);
  }
  P = maxprime();
  *a = itos(ga); if (*a <= 0) *a = 1;
  *b = itos(gb); if (*a > *b) return NULL;
  if ((ulong)*a <= P) prime[2] = sinitp(*a, 0, &p);
  if ((ulong)*b > P) err(primer1);
  return p;
}

void
forprime(entree *ep, GEN ga, GEN gb, char *ch)
{
  long prime[] = {evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 0};
  long av = avma, a,b;
  byteptr p;

  p = prime_loop_init(ga,gb, &a,&b, prime);
  if (!p) { avma = av; return; }

  avma = av; push_val(ep, prime);
  while ((ulong)prime[2] < (ulong)b)
  {
    (void)lisseq(ch); if (loop_break()) break;
    if (ep->value == prime)
      prime[2] += *p++;
    else
      update_p(ep, &p, prime);
    avma = av;
  }
  /* if b = P --> *p = 0 now and the loop wouldn't end if it read 'while
   * (prime[2] <= b)' */
  if (prime[2] == b) { (void)lisseq(ch); (void)loop_break(); avma = av; }
  pop_val(ep);
}

void
fordiv(GEN a, entree *ep, char *ch)
{
  long i,av2,l, av = avma;
  GEN t = divisors(a);

  push_val(ep, NULL); l=lg(t); av2 = avma;
  for (i=1; i<l; i++)
  {
    ep->value = (void*) t[i]; 
    (void)lisseq(ch); if (loop_break()) break;
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
static GEN *fv_a, *fv_m, *fv_M;
static long fv_n, fv_fl;
static char *fv_ch;

/* general case */
static void
fvloop(long i)
{
  fv_a[i] = fv_m[i];
  if (fv_fl && i > 1)
  {
    GEN p1 = gsub(fv_a[i], fv_a[i-1]);
    if (gsigne(p1) < 0)
      fv_a[i] = gadd(fv_a[i], gceil(gneg_i(p1)));
    if (fv_fl == 2 && gegal(fv_a[i], fv_a[i-1]))
      fv_a[i] = gadd(fv_a[i], gun);
  }
  if (i+1 == fv_n)
    while (gcmp(fv_a[i], fv_M[i]) <= 0)
    {
      long av = avma; (void)lisseq(fv_ch); avma = av;
      if (loop_break()) { fv_n = 0; return; }
      fv_a[i] = gadd(fv_a[i], gun);
    }
  else
    while (gcmp(fv_a[i], fv_M[i]) <= 0)
    {
      long av = avma; fvloop(i+1); avma = av;
      if (!fv_n) return;
      fv_a[i] = gadd(fv_a[i], gun);
    }
}

/* we run through integers */
static void
fvloop_i(long i)
{
  fv_a[i] = setloop(fv_m[i]);
  if (fv_fl && i > 1)
  {
    int c = cmpii(fv_a[i], fv_a[i-1]);
    if (c < 0)
    {
      fv_a[i] = setloop(fv_a[i-1]);
      c = 0;
    }
    if (c == 0 && fv_fl == 2)
      fv_a[i] = incloop(fv_a[i]);
  }
  if (i+1 == fv_n)
    while (gcmp(fv_a[i], fv_M[i]) <= 0)
    {
      long av = avma; (void)lisseq(fv_ch); avma = av;
      if (loop_break()) { fv_n = 0; return; }
      fv_a[i] = incloop(fv_a[i]);
    }
  else
    while (gcmp(fv_a[i], fv_M[i]) <= 0)
    {
      long av = avma; fvloop_i(i+1); avma = av;
      if (!fv_n) return;
      fv_a[i] = incloop(fv_a[i]);
    }
}

void
forvec(entree *ep, GEN x, char *c, long flag)
{
  long i, av = avma, tx = typ(x), n = fv_n, fl = fv_fl;
  GEN *a = fv_a, *M = fv_M, *m = fv_m;
  char *ch = fv_ch;
  void (*fv_fun)(long) = fvloop_i;

  if (!is_vec_t(tx)) err(talker,"not a vector in forvec");
  if (fl<0 || fl>2) err(flagerr);
  fv_n = lg(x);
  fv_ch = c;
  fv_fl = flag;
  fv_a = (GEN*)cgetg(fv_n,t_VEC); push_val(ep, (GEN)fv_a);
  fv_m = (GEN*)cgetg(fv_n,t_VEC);
  fv_M = (GEN*)cgetg(fv_n,t_VEC);
  if (fv_n == 1) lisseq(fv_ch);
  else
  {
    for (i=1; i<fv_n; i++)
    {
      GEN *c = (GEN*) x[i];
      tx = typ(c);
      if (! is_vec_t(tx) || lg(c)!=3)
	err(talker,"not a vector of two-component vectors in forvec");
      if (gcmp(c[1],c[2]) > 0) fv_n = 0;
      /* in case x is an ep->value and c destroys it, we have to copy */
      if (typ(c[1]) != t_INT) fv_fun = fvloop;
      fv_m[i] = gcopy(c[1]);
      fv_M[i] = gcopy(c[2]);
    }
    fv_fun(1);
  }
  pop_val(ep);
  fv_n = n;
  fv_ch = ch;
  fv_fl = fl;
  fv_a = a;
  fv_m = m;
  fv_M = M; avma = av;
}

/********************************************************************/
/**                                                                **/
/**                              SUMS                              **/
/**                                                                **/
/********************************************************************/

GEN
somme(entree *ep, GEN a, GEN b, char *ch, GEN x)
{
  long av,av0 = avma, lim;
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
  long fl,G,tetpil, av0 = avma, av,lim;
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
  long av=avma;
  GEN z, y = gzero;

  push_val(ep, NULL);
#if 0
  {
    long d,n,d2;
    GEN p1 = icopy(gun);
    n=itos(num); /* provisoire */
    ep->value = (void*)p1;
    for (d=d2=1; d2 < n; d++, d2 += d+d-1)
      if (n%d == 0)
      {
        p1[2]=d; y=gadd(y, lisexpr(ch));
        if (did_break()) err(breaker,"divsum");
        p1[2]=n/d; z = lisexpr(ch);
        if (did_break()) err(breaker,"divsum");
        y=gadd(y,z);
      }
    if (d2 == n)
    {
      p1[2]=d; z = lisexpr(ch);
      if (did_break()) err(breaker,"divsum");
      y=gadd(y,z);
    }
  }
#else
  {
    GEN t = divisors(num);
    long i, l=lg(t);
    for (i=1; i<l; i++)
    {
      ep->value = (void*) t[i]; 
      z = lisseq(ch);
      if (did_break()) err(breaker,"divsum");
      y = gadd(y, z);
    }
  }
#endif
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
  long av,av0 = avma, lim;
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
  long fl,G,tetpil, av0 = avma, av,lim;
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
  pop_val(ep); tetpil=avma;
  return gerepile(av0,tetpil,gcopy(x));
}

GEN
prodinf1(entree *ep, GEN a, char *ch, long prec)
{
  long fl,G,tetpil, av0 = avma, av,lim;
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
  pop_val(ep); tetpil=avma;
  return gerepile(av0,tetpil,gcopy(x));
}

GEN
prodeuler(entree *ep, GEN ga, GEN gb, char *ch, long prec)
{
  long prime[] = {evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 0};
  long a,b,tetpil, av,av0 = avma, lim;
  GEN p1,x = realun(prec);
  byteptr p;
  
  av = avma;
  p = prime_loop_init(ga,gb, &a,&b, prime);
  if (!p) { avma = av; return x; }

  av = avma; push_val(ep, prime);
  lim = stack_lim(avma,1);
  while ((ulong)prime[2] < (ulong)b)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"prodeuler");
    x = gmul(x,p1);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) err(warnmem,"prodeuler");
      x = gerepileupto(av, gcopy(x));
    }
    if (ep->value == prime)
      prime[2] += *p++;
    else
      update_p(ep, &p, prime);
  }
  /* cf forprime */
  if (prime[2] == b)
  {
    p1 = lisexpr(ch); if (did_break()) err(breaker,"prodeuler");
    x = gmul(x,p1);
  }
  pop_val(ep); tetpil=avma;
  return gerepile(av0,tetpil,gcopy(x));
}

GEN
direulerall(entree *ep, GEN ga, GEN gb, char *ch, GEN c)
{
  long prime[] = {evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 0};
  long av0 = avma,av,tetpil,lim = (av0+bot)>>1, p,n,i,j,k,tx,lx,a,b;
  GEN x,y,s,polnum,polden;
  byteptr d;

  d = prime_loop_init(ga,gb, &a,&b, prime);
  n = c? itos(c): b;
  if (!d || b < 2 || n <= 0) { x=cgetg(2,t_VEC); x[1]=un; return x; }
  if (n < b) b = n;
  push_val(ep, prime);

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
      ulong k1,q, qlim;
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
      lx=lgef(polnum)-3;
      q=p; qlim = n/p; j=1;
      while (q<=(ulong)n && j<=lx)
      {
	c=(GEN)polnum[j+2];
	if (!gcmp0(c))
	  for (k=1,k1=q; k1<=(ulong)n; k1+=q,k++)
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
      lx=lgef(polden)-3;
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
      x = gerepileupto(av, gcopy(x));
    }
    p += *d++; if (!*d) err(primer1);
    prime[2] = p;
  }
  pop_val(ep); tetpil=avma;
  return gerepile(av0,tetpil,gcopy(x));
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
  long c[]={evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 0};

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
  long c1[]={evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 1};
  long c2[]={evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3), 1};

  s=signe(ncol);
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
/**                    SOMMATION DE SERIES                         **/
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
  long av = avma, tetpil,k,N;
  GEN s,az,c,x,e1,d;

  if (typ(a) != t_INT) err(talker,"non integral index in sumalt");

  push_val(ep, a);
  e1=addsr(3,gsqrt(stoi(8),prec));
  N=(long)(0.4*(bit_accuracy(prec) + 7));
  d=gpuigs(e1,N); d=shiftr(addrr(d,divsr(1,d)),-1);
  az=negi(gun); c=d; s=gzero;
  for (k=0; ; k++)
  {
    x = lisexpr(ch); if (did_break()) err(breaker,"sumalt");
    c = gadd(az,c); s = gadd(s,gmul(x,c));
    az = divii(mulii(mulss(N-k,N+k),shifti(az,1)),mulss(k+1,k+k+1));
    if (k==N-1) break;
    a = addsi(1,a); ep->value = (void*) a;
  }
  tetpil=avma; pop_val(ep);
  return gerepile(av,tetpil,gdiv(s,d));
}

GEN
sumalt2(entree *ep, GEN a, char *ch, long prec)
{
  long av = avma, tetpil,k,N;
  GEN x,s,dn,pol;

  if (typ(a) != t_INT) err(talker,"non integral index in sumalt");

  push_val(ep, a);
  N=(long)(0.31*(bit_accuracy(prec) + 5));
  s=gzero; pol=polzagreel(N,N>>1,prec+1); dn=poleval(pol,gun);
  pol[2]=lsub((GEN)pol[2],dn); pol=gdiv(pol,gsub(polx[0],gun));
  N=lgef(pol)-2;
  for (k=0; k<N; k++)
  {
    x = lisexpr(ch); if (did_break()) err(breaker,"sumalt2");
    s=gadd(s,gmul(x,(GEN)pol[k+2]));
    if (k==N-1) break;
    a = addsi(1,a); ep->value = (void*) a;
  }
  tetpil=avma; pop_val(ep);
  return gerepile(av,tetpil,gdiv(s,dn));
}

GEN
sumpos(entree *ep, GEN a, char *ch, long prec)
{
  long av = avma,tetpil,k,kk,N,G;
  GEN p1,r,q1,reel,s,az,c,x,e1,d, *stock;

  if (typ(a) != t_INT) err(talker,"non integral index in sumpos");

  push_val(ep, NULL);
  a=subis(a,1); reel=cgetr(prec);
  e1=addsr(3,gsqrt(stoi(8),prec));
  N=(long)(0.4*(bit_accuracy(prec) + 7));
  d=gpuigs(e1,N); d=shiftr(addrr(d,divsr(1,d)),-1);
  az=negi(gun); c=d; s=gzero;
  G = -bit_accuracy(prec) - 5;
  stock=(GEN*)new_chunk(N+1); for (k=1; k<=N; k++) stock[k]=NULL;
  for (k=0; k<N; k++)
  {
    if (k&1 && stock[k]) x=stock[k];
    else
    {
      x=gzero; r=stoi(2*k+2);
      for(kk=0;;kk++)
      {
        long ex;
	q1 = addii(r,a); ep->value = (void*) q1;
        p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos");
        gaffect(p1,reel); ex = expo(reel)+kk; setexpo(reel,ex);
	x = gadd(x,reel); if (kk && ex < G) break;
        r=shifti(r,1);
      }
      if (2*k<N) stock[2*k+1]=x;
      q1 = addsi(k+1,a); ep->value = (void*) q1;
      p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos");
      gaffect(p1,reel); x = gadd(reel, gmul2n(x,1));
    }
    c=gadd(az,c); p1 = k&1? gneg_i(c): c;
    s = gadd(s,gmul(x,p1));
    az = divii(mulii(mulss(N-k,N+k),shifti(az,1)),mulss(k+1,k+k+1));
  }
  tetpil=avma; pop_val(ep);
  return gerepile(av,tetpil,gdiv(s,d));
}

GEN
sumpos2(entree *ep, GEN a, char *ch, long prec)
{
  long av = avma,tetpil,k,kk,N,G;
  GEN p1,r,q1,reel,s,pol,dn,x, *stock;

  if (typ(a) != t_INT) err(talker,"non integral index in sumpos2");

  push_val(ep, a);
  a=subis(a,1); reel=cgetr(prec);
  N=(long)(0.31*(bit_accuracy(prec) + 5));
  G = -bit_accuracy(prec) - 5;
  stock=(GEN*)new_chunk(N+1); for (k=1; k<=N; k++) stock[k]=NULL;
  for (k=1; k<=N; k++)
  {
    if (odd(k) || !stock[k])
    {
      x=gzero; r=stoi(2*k);
      for(kk=0;;kk++)
      {
        long ex;
	q1 = addii(r,a); ep->value = (void*) q1;
        p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos2");
        gaffect(p1,reel); ex = expo(reel)+kk; setexpo(reel,ex);
	x=gadd(x,reel); if (kk && ex < G) break;
        r=shifti(r,1);
      }
      if (2*k-1<N) stock[2*k]=x;
      q1 = addsi(k,a); ep->value = (void*) q1;
      p1 = lisexpr(ch); if (did_break()) err(breaker,"sumpos2");
      gaffect(p1,reel); stock[k] = gadd(reel, gmul2n(x,1));
    }
  }
  pop_val(ep); s = gzero;
  pol=polzagreel(N,N>>1,prec+1); dn=poleval(pol,gun);
  pol[2]=lsub((GEN)pol[2],dn); pol=gdiv(pol,gsub(gun,polx[0]));
  for (k=1; k<=lgef(pol)-2; k++)
  {
    p1 = gmul((GEN)pol[k+1],stock[k]);
    if (k&1) p1 = gneg_i(p1);
    s = gadd(s,p1);
  }
  tetpil=avma; return gerepile(av,tetpil,gdiv(s,dn));
}

/********************************************************************/
/**                                                                **/
/**                NUMERICAL INTEGRATION (Romberg)                 **/
/**                                                                **/
/********************************************************************/
GEN
intnum0(entree *ep, GEN a, GEN b, char *ch, long flag, long prec)
{
  switch(flag)
  {
    case 0: return qromb  (ep,a,b,ch,prec);
    case 1: return rombint(ep,a,b,ch,prec);
    case 2: return qromi  (ep,a,b,ch,prec);
    case 3: return qromo  (ep,a,b,ch,prec);
    default: err(flagerr);
  }
  return NULL; /* not reached */
}

#define JMAX 25
#define JMAXP JMAX+3
#define KLOC 4

/* we need to make a copy in any case, cf forpari */
static GEN
fix(GEN a, long prec)
{
  GEN p = cgetr(prec);
  gaffect(a,p); return p;
}

extern GEN polint_i(GEN xa, GEN ya, GEN x, long n, GEN *ptdy);

GEN
qromb(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  GEN ss,dss,s,h,p1,p2,qlint,del,x,sum;
  long av = avma, av1, tetpil,j,j1,j2,lim,it,sig;

  a = fix(a,prec);
  b = fix(b,prec);
  qlint=subrr(b,a); sig=signe(qlint);
  if (!sig)  { avma=av; return gzero; }
  if (sig<0) { setsigne(qlint,1); s=a; a=b; b=s; }

  s=new_chunk(JMAXP);
  h=new_chunk(JMAXP);
  h[0] = (long)realun(prec);

  push_val(ep, a);
  p1=lisexpr(ch); if (p1 == a) p1=rcopy(p1);
  ep->value = (void*)b;
  p2=lisexpr(ch);
  s[0]=lmul2n(gmul(qlint,gadd(p1,p2)),-1);
  for (it=1,j=1; j<JMAX; j++,it=it<<1)
  {
    h[j]=lshiftr((GEN)h[j-1],-2);
    av1=avma; del=divrs(qlint,it); x=addrr(a,shiftr(del,-1));
    for (sum=gzero,j1=1; j1<=it; j1++,x=addrr(x,del))
    {
      ep->value = (void*) x; sum=gadd(sum,lisexpr(ch));
    }
    sum = gmul(sum,del); p1 = gadd((GEN)s[j-1],sum);
    tetpil = avma;
    s[j]=lpile(av1,tetpil,gmul2n(p1,-1));

    if (j>=KLOC)
    {
      tetpil=avma; ss=polint_i(h+j-KLOC,s+j-KLOC,gzero,KLOC+1,&dss);
      j1=gexpo(ss); j2=gexpo(dss); lim=bit_accuracy(prec)-j-6;
      if (j1-j2 > lim || j1 < -lim)
      {
        pop_val(ep); if (gcmp0(gimag(ss))) ss=greal(ss);
	tetpil=avma; return gerepile(av,tetpil,gmulsg(sig,ss));
      }
      avma=tetpil;
    }
  }
  err(intger2); return NULL; /* not reached */
}

GEN
qromo(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  GEN ss,dss,s,h,p1,qlint,del,ddel,x,sum;
  long av = avma,av1,tetpil,j,j1,j2,lim,it,sig;

  a = fix(a, prec);
  b = fix(b, prec);
  qlint=subrr(b,a); sig=signe(qlint);
  if (!sig)  { avma=av; return gzero; }
  if (sig<0) { setsigne(qlint,1); s=a; a=b; b=s; }

  s=new_chunk(JMAXP);
  h=new_chunk(JMAXP);
  h[0] = (long)realun(prec);

  p1 = shiftr(addrr(a,b),-1); push_val(ep, p1);
  p1=lisexpr(ch); s[0]=lmul(qlint,p1);

  for (it=1, j=1; j<JMAX; j++, it*=3)
  {
    h[j] = ldivrs((GEN)h[j-1],9);
    av1=avma; del=divrs(qlint,3*it); ddel=shiftr(del,1);
    x=addrr(a,shiftr(del,-1)); sum=gzero;
    for (j1=1; j1<=it; j1++)
    {
      ep->value = (void*)x; sum=gadd(sum,lisexpr(ch)); x=addrr(x,ddel);
      ep->value = (void*)x; sum=gadd(sum,lisexpr(ch)); x=addrr(x,del);
    }
    sum = gmul(sum,del); p1 = gdivgs((GEN)s[j-1],3);
    tetpil = avma; s[j]=lpile(av1,tetpil,gadd(p1,sum));

    if (j>=KLOC)
    {
      tetpil=avma; ss=polint_i(h+j-KLOC,s+j-KLOC,gzero,KLOC+1,&dss);
      j1=gexpo(ss); j2=gexpo(dss); lim=bit_accuracy(prec)-(3*j/2)-6;
      if ( j1-j2 > lim || j1 < -lim)
      {
        pop_val(ep); if (gcmp0(gimag(ss))) ss=greal(ss);
	tetpil=avma; return gerepile(av,tetpil,gmulsg(sig,ss));
      }
      avma=tetpil;
    }
  }
  err(intger2); return NULL; /* not reached */
}

#undef JMAX
#undef JMAXP
#define JMAX 16
#define JMAXP JMAX+3

GEN
qromi(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  GEN ss,dss,s,h,q1,p1,p,qlint,del,ddel,x,sum;
  long av = avma, av1,tetpil,j,j1,j2,lim,it,sig;

  p=cgetr(prec); gaffect(ginv(a),p); a=p;
  p=cgetr(prec); gaffect(ginv(b),p); b=p;
  qlint=subrr(b,a); sig= -signe(qlint);
  if (!sig)  { avma=av; return gzero; }
  if (sig>0) { setsigne(qlint,1); s=a; a=b; b=s; }

  s=new_chunk(JMAXP);
  h=new_chunk(JMAXP);
  h[0] = (long)realun(prec);

  x=divsr(2,addrr(a,b)); push_val(ep, x);
  p1=gmul(lisexpr(ch),mulrr(x,x));
  s[0]=lmul(qlint,p1);
  for (it=1,j=1; j<JMAX; j++, it*=3)
  {
    h[j] = ldivrs((GEN)h[j-1],9);
    av1=avma; del=divrs(qlint,3*it); ddel=shiftr(del,1);
    x=addrr(a,shiftr(del,-1)); sum=gzero;
    for (j1=1; j1<=it; j1++)
    {
      q1 = ginv(x); ep->value = (void*)q1;
      p1=gmul(lisexpr(ch), gsqr(q1));
      sum=gadd(sum,p1); x=addrr(x,ddel);

      q1 = ginv(x); ep->value = (void*)q1;
      p1=gmul(lisexpr(ch), gsqr(q1));
      sum=gadd(sum,p1); x=addrr(x,del);
    }
    sum = gmul(sum,del); p1 = gdivgs((GEN)s[j-1],3);
    tetpil=avma;
    s[j]=lpile(av1,tetpil,gadd(p1,sum));

    if (j>=KLOC)
    {
      tetpil=avma; ss=polint_i(h+j-KLOC,s+j-KLOC,gzero,KLOC+1,&dss);
      j1=gexpo(ss); j2=gexpo(dss); lim=bit_accuracy(prec)-(3*j/2)-6;
      if (j1-j2 > lim || j1 < -lim)
      {
        pop_val(ep); if (gcmp0(gimag(ss))) ss=greal(ss);
	tetpil=avma; return gerepile(av,tetpil,gmulsg(sig,ss));
      }
    }
  }
  err(intger2); return NULL; /* not reached */
}

GEN
rombint(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  GEN aa,bb,mun,p1,p2,p3;
  long l,av,tetpil;

  l=gcmp(b,a); if (!l) return gzero;
  if (l<0) { bb=a; aa=b; } else { bb=b; aa=a; }
  av=avma; mun = negi(gun);
  if (gcmpgs(bb,100)>=0)
  {
    if (gcmpgs(aa,1)>=0) return qromi(ep,a,b,ch,prec);
    p1=qromi(ep,gun,bb,ch,prec);
    if (gcmpgs(aa,-100)>=0)
    {
      p2=qromo(ep,aa,gun,ch,prec); tetpil=avma;
      return gerepile(av,tetpil,gmulsg(l,gadd(p1,p2)));
    }
    p2=qromo(ep,mun,gun,ch,prec); p3=gadd(p2,qromi(ep,aa,mun,ch,prec));
    tetpil=avma; return gerepile(av,tetpil,gmulsg(l,gadd(p1,p3)));
  }
  if (gcmpgs(aa,-100)>=0) return qromo(ep,a,b,ch,prec);
  if (gcmpgs(bb,-1)>=0)
  {
    p1=qromi(ep,aa,mun,ch,prec); p2=qromo(ep,mun,bb,ch,prec); tetpil=avma;
    return gerepile(av,tetpil,gmulsg(l,gadd(p1,p2)));
  }
  return qromi(ep,a,b,ch,prec);
}

/********************************************************************/
/**                                                                **/
/**                  ZAGIER POLYNOMIALS (for sumiter)              **/
/**                                                                **/
/********************************************************************/

GEN
polzag(long n, long m)
{
  long d1,d,r,k,av=avma,tetpil;
  GEN p1,p2,pol1,g,s;

  if (m>=n || m<0)
    err(talker,"first index must be greater than second in polzag");
  d1=n-m; d=d1<<1; d1--; p1=gsub(gun,gmul2n(polx[0],1));
  pol1=gsub(gun,polx[0]); p2=gmul(polx[0],pol1); r=(m+1)>>1;
  g=gzero;
  for (k=0; k<=d1; k++)
  {
    s=binome(stoi(d),(k<<1)+1); if (k&1) s=negi(s);
    g=gadd(g,gmul(s,gmul(gpuigs(polx[0],k),gpuigs(pol1,d1-k))));
  }
  g=gmul(g,gpuigs(p2,r));
  if (!(m&1)) g=gadd(gmul(p1,g),gmul2n(gmul(p2,derivpol(g)),1));
  for (k=1; k<=r; k++)
  {
    g=derivpol(g); g=gadd(gmul(p1,g),gmul2n(gmul(p2,derivpol(g)),1));
  }
  g = m ? gmul2n(g,(m-1)>>1):gmul2n(g,-1);
  s=mulsi(n-m,mpfact(m+1));
  tetpil=avma; return gerepile(av,tetpil,gdiv(g,s));
}

#ifdef _MSC_VER /* Bill Daly: work around a MSVC bug */
#pragma optimize("g",off)
#endif
GEN
polzagreel(long n, long m, long prec)
{
  long d1,d,r,j,k,k2,av=avma,tetpil;
  GEN p2,pol1,g,h,v,b,gend,s;

  if (m>=n || m<0)
    err(talker,"first index must be greater than second in polzag");
  d1=n-m; d=d1<<1; d1--; pol1=gadd(gun,polx[0]);
  p2=gmul(polx[0],pol1); r=(m+1)>>1; gend=stoi(d);
  v=cgetg(d1+2,t_VEC); g=cgetg(d1+2,t_VEC);
  v[d1+1]=un; b=mulri(realun(prec),gend); g[d1+1]=(long)b;
  for (k=1; k<=d1; k++)
  {
    v[d1-k+1]=un;
    for (j=1; j<k; j++)
      v[d1-k+j+1]=(long)addii((GEN)v[d1-k+j+1],(GEN)v[d1-k+j+2]);
    k2=k+k; b=divri(mulri(b,mulss(d-k2+1,d-k2)),mulss(k2,k2+1));
    for (j=1; j<=k; j++)
      g[d1-k+j+1]=(long)mpadd((GEN)g[d1-k+j+1],mulri(b,(GEN)v[d1-k+j+1]));
    g[d1-k+1]=(long)b;
  }
  h=cgetg(d1+3,t_POL); h[1]=evalsigne(1)+evallgef(d1+3);
  for (k=0; k<=d1; k++) h[k+2]=g[k+1];
  g=gmul(h,gpuigs(p2,r));
  for (j=0; j<=r; j++)
  {
    if (j) g=derivpol(g);
    if (j || !(m&1))
    {
      h=cgetg(n+3,t_POL); h[1]=evalsigne(1)+evallgef(n+3);
      h[2]=g[2];
      for (k=1; k<n; k++)
	h[k+2]=ladd(gmulsg(k+k+1,(GEN)g[k+2]),gmulsg(k<<1,(GEN)g[k+1]));
      h[n+2]=lmulsg(n<<1,(GEN)g[n+1]); g=h;
    }
  }
  g = m ?gmul2n(g,(m-1)>>1):gmul2n(g,-1);
  s=mulsi(n-m,mpfact(m+1));
  tetpil=avma; return gerepile(av,tetpil,gdiv(g,s));
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
zbrent(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  long av = avma,sig,iter,itmax;
  GEN c,d,e,tol,tol1,min1,min2,fa,fb,fc,p,q,r,s,xm;

  a = fix(a,prec);
  b = fix(b,prec); sig=cmprr(b,a);
  if (!sig) { avma = av; return gzero; }
  if (sig < 0) { c=a; a=b; b=c; } else c = b;

  push_val(ep, a);      fa = lisexpr(ch);
  ep->value = (void*)b; fb = lisexpr(ch);
  if (gsigne(fa)*gsigne(fb) > 0)
    err(talker,"roots must be bracketed in solve");
  itmax = (prec<<(TWOPOTBITS_IN_LONG+1)) + 1;
  tol = realun(3); setexpo(tol, 5-bit_accuracy(prec));
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
    else
    {
      if (gsigne(xm) > 0)
        b = addrr(b,tol1);
      else
        b = subrr(b,tol1);
    }
    ep->value = (void*)b; fb = lisexpr(ch);
  }
  if (iter > itmax) err(talker,"too many iterations in solve");
  pop_val(ep);
  return gerepileuptoleaf(av, rcopy(b));
}
