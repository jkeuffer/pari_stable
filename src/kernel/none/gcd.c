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

/* assume y > x > 0. return y mod x */
static ulong
resiu(GEN y, ulong x)
{
  long i, ly = lgefint(y);
  LOCAL_HIREMAINDER;

  hiremainder = 0;
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  return hiremainder;
}

/* Assume x>y>0, both of them odd. return x-y if x=y mod 4, x+y otherwise */
void
gcd_plus_minus(GEN x, GEN y, GEN res)
{
  pari_sp av = avma;
  long lx = lgefint(x)-1;
  long ly = lgefint(y)-1, lt,m,i;
  GEN t;

  if ((x[lx]^y[ly]) & 3) /* x != y mod 4*/
    t = addiispec(x+2,y+2,lx-1,ly-1);
  else
    t = subiispec(x+2,y+2,lx-1,ly-1);

  lt = lgefint(t)-1; while (!t[lt]) lt--;
  m = vals(t[lt]); lt++;
  if (m == 0) /* 2^32 | t */
  {
    for (i = 2; i < lt; i++) res[i] = t[i];
  }
  else if (t[2] >> m)
  {
    shift_right(res,t, 2,lt, 0,m);
  }
  else
  {
    lt--; t++;
    shift_right(res,t, 2,lt, t[1],m);
  }
  res[1] = evalsigne(1)|evallgefint(lt);
  avma = av;
}

/* uses modified right-shift binary algorithm now --GN 1998Jul23 */
GEN
gcdii(GEN a, GEN b)
{
  long v, w;
  pari_sp av;
  GEN t, p1;

  switch (absi_cmp(a,b))
  {
    case 0: return absi(a);
    case -1: t=b; b=a; a=t;
  }
  if (!signe(b)) return absi(a);
  /* here |a|>|b|>0. Try single precision first */
  if (lgefint(a)==3)
    return gcduu((ulong)a[2], (ulong)b[2]);
  if (lgefint(b)==3)
  {
    ulong u = resiu(a,(ulong)b[2]);
    if (!u) return absi(b);
    return gcduu((ulong)b[2], u);
  }

  /* larger than gcd: "avma=av" gerepile (erasing t) is valid */
  av = avma; (void)new_chunk(lgefint(b)); /* HACK */
  t = resii(a,b);
  if (!signe(t)) { avma=av; return absi(b); }

  a = b; b = t;
  v = vali(a); a = shifti(a,-v); setsigne(a,1);
  w = vali(b); b = shifti(b,-w); setsigne(b,1);
  if (w < v) v = w;
  switch(absi_cmp(a,b))
  {
    case  0: avma=av; a=shifti(a,v); return a;
    case -1: p1=b; b=a; a=p1;
  }
  if (is_pm1(b)) { avma=av; return shifti(gun,v); }

  /* we have three consecutive memory locations: a,b,t.
   * All computations are done in place */

  /* a and b are odd now, and a>b>1 */
  while (lgefint(a) > 3)
  {
    /* if a=b mod 4 set t=a-b, otherwise t=a+b, then strip powers of 2 */
    /* so that t <= (a+b)/4 < a/2 */
    gcd_plus_minus(a,b, t);
    if (is_pm1(t)) { avma=av; return shifti(gun,v); }
    switch(absi_cmp(t,b))
    {
      case -1: p1 = a; a = b; b = t; t = p1; break;
      case  1: p1 = a; a = t; t = p1; break;
      case  0: avma = av; b=shifti(b,v); return b;
    }
  }
  {
    long r[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
    r[2] = (long) ugcd((ulong)b[2], (ulong)a[2]);
    avma = av; return shifti(r,v);
  }
}

/*==================================
 * invmod(a,b,res)
 *==================================
 *    If a is invertible, return 1, and set res  = a^{ -1 }
 *    Otherwise, return 0, and set res = gcd(a,b)
 *
 * This is sufficiently different from bezout() to be implemented separately
 * instead of having a bunch of extra conditionals in a single function body
 * to meet both purposes.
 */

int
invmod(GEN a, GEN b, GEN *res)
{
  GEN v,v1,d,d1,q,r;
  pari_sp av, av1, lim;
  long s;
  ulong g;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */
  int lhmres;			/* Lehmer stage return value */

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  if (!signe(b)) { *res=absi(a); return 0; }
  av = avma;
  if (lgefint(b) == 3) /* single-word affair */
  {
    d1 = modiu(a, (ulong)(b[2]));
    if (d1 == gzero)
    {
      if (b[2] == 1L)
        { *res = gzero; return 1; }
      else
        { *res = absi(b); return 0; }
    }
    g = xgcduu((ulong)(b[2]), (ulong)(d1[2]), 1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    fprintferr(" <- %lu,%lu\n", (ulong)(b[2]), (ulong)(d1[2]));
    fprintferr(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    avma = av;
    if (g != 1UL) { *res = utoi(g); return 0; }
    xv = xv1 % (ulong)(b[2]); if (s < 0) xv = ((ulong)(b[2])) - xv;
    *res = utoi(xv); return 1;
  }

  (void)new_chunk(lgefint(b));
  d = absi(b); d1 = modii(a,d);

  v=gzero; v1=gun;	/* general case */
#ifdef DEBUG_LEHMER
  fprintferr("INVERT: -------------------------\n");
  output(d1);
#endif
  av1 = avma; lim = stack_lim(av,1);

  while (lgefint(d) > 3 && signe(d1))
  {
#ifdef DEBUG_LEHMER
    fprintferr("Calling Lehmer:\n");
#endif
    lhmres = lgcdii((ulong*)d, (ulong*)d1, &xu, &xu1, &xv, &xv1, MAXULONG);
    if (lhmres != 0)		/* check progress */
    {				/* apply matrix */
#ifdef DEBUG_LEHMER
      fprintferr("Lehmer returned %d [%lu,%lu;%lu,%lu].\n",
	      lhmres, xu, xu1, xv, xv1);
#endif
      if ((lhmres == 1) || (lhmres == -1))
      {
	if (xv1 == 1)
	{
	  r = subii(d,d1); d=d1; d1=r;
	  a = subii(v,v1); v=v1; v1=a;
	}
	else
	{
	  r = subii(d, mului(xv1,d1)); d=d1; d1=r;
	  a = subii(v, mului(xv1,v1)); v=v1; v1=a;
	}
      }
      else
      {
	r  = subii(muliu(d,xu),  muliu(d1,xv));
	a  = subii(muliu(v,xu),  muliu(v1,xv));
	d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
	v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1)
	{
          setsigne(d,-signe(d));
          setsigne(v,-signe(v));
        }
        else
	{
          if (signe(d1)) { setsigne(d1,-signe(d1)); }
          setsigne(v1,-signe(v1));
        }
      }
    }
#ifdef DEBUG_LEHMER
    else
      fprintferr("Lehmer returned 0.\n");
    output(d); output(d1); output(v); output(v1);
    sleep(1);
#endif

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      fprintferr("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&d; gptr[1]=&d1; gptr[2]=&v; gptr[3]=&v1;
      if(DEBUGMEM>1) err(warnmem,"invmod");
      gerepilemany(av1,gptr,4);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu((ulong)(d[2]), (ulong)(d1[2]), 1, &xu, &xu1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    output(d);output(d1);output(v);output(v1);
    fprintferr(" <- %lu,%lu\n", (ulong)(d[2]), (ulong)(d1[2]));
    fprintferr(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    if (g != 1UL) { avma = av; *res = utoi(g); return 0; }
    /* (From the xgcduu() blurb:)
     * For finishing the multiword modinv, we now have to multiply the
     * returned matrix  (with properly adjusted signs)  onto the values
     * v' and v1' previously obtained from the multiword division steps.
     * Actually, it is sufficient to take the scalar product of [v',v1']
     * with [u1,-v1], and change the sign if s==1.
     */
    v = subii(muliu(v,xu1),muliu(v1,xv1));
    if (s > 0) setsigne(v,-signe(v));
    avma = av; *res = modii(v,b);
#ifdef DEBUG_LEHMER
    output(*res); fprintfderr("============================Done.\n");
    sleep(1);
#endif
    return 1;
  }
  /* get here when the final sprint was skipped (d1 was zero already) */
  avma = av;
  if (!egalii(d,gun)) { *res = icopy(d); return 0; }
  *res = modii(v,b);
#ifdef DEBUG_LEHMER
  output(*res); fprintferr("============================Done.\n");
  sleep(1);
#endif
  return 1;
}

/*==================================
 * bezout(a,b,pu,pv)
 *==================================
 *    Return g = gcd(a,b) >= 0, and assign GENs u,v through pointers pu,pv
 *    such that g = u*a + v*b.
 * Special cases:
 *    a == b == 0 ==> pick u=1, v=0
 *    a != 0 == b ==> keep v=0
 *    a == 0 != b ==> keep u=0
 *    |a| == |b| != 0 ==> keep u=0, set v=+-1
 * Assignments through pu,pv will be suppressed when the corresponding
 * pointer is NULL  (but the computations will happen nonetheless).
 */

GEN
bezout(GEN a, GEN b, GEN *pu, GEN *pv)
{
  GEN t,u,u1,v,v1,d,d1,q,r;
  GEN *pt;
  pari_sp av, av1, lim;
  long s;
  int sa, sb;
  ulong g;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */
  int lhmres;			/* Lehmer stage return value */

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  s = absi_cmp(a,b);
  if (s < 0)
  {
    t=b; b=a; a=t;
    pt=pu; pu=pv; pv=pt;
  }
  /* now |a| >= |b| */

  sa = signe(a); sb = signe(b);
  if (!sb)
  {
    if (pv != NULL) *pv = gzero;
    switch(sa)
    {
    case  0:
      if (pu != NULL) *pu = gun; return gzero;
    case  1:
      if (pu != NULL) *pu = gun; return icopy(a);
    case -1:
      if (pu != NULL) *pu = negi(gun); return(negi(a));
    }
  }
  if (s == 0)			/* |a| == |b| != 0 */
  {
    if (pu != NULL) *pu = gzero;
    if (sb > 0)
    {
      if (pv != NULL) *pv = gun; return icopy(b);
    }
    else
    {
      if (pv != NULL) *pv = negi(gun); return(negi(b));
    }
  }
  /* now |a| > |b| > 0 */

  if (lgefint(a) == 3)		/* single-word affair */
  {
    g = xxgcduu((ulong)(a[2]), (ulong)(b[2]), 0, &xu, &xu1, &xv, &xv1, &s);
    sa = s > 0 ? sa : -sa;
    sb = s > 0 ? -sb : sb;
    if (pu != NULL)
    {
      if (xu == 0) *pu = gzero; /* can happen when b divides a */
      else if (xu == 1) *pu = sa < 0 ? negi(gun) : gun;
      else if (xu == 2) *pu = sa < 0 ? negi(gdeux) : gdeux;
      else
      {
	*pu = cgeti(3);
	(*pu)[1] = evalsigne(sa)|evallgefint(3);
	(*pu)[2] = xu;
      }
    }
    if (pv != NULL)
    {
      if (xv == 1) *pv = sb < 0 ? negi(gun) : gun;
      else if (xv == 2) *pv = sb < 0 ? negi(gdeux) : gdeux;
      else
      {
	*pv = cgeti(3);
	(*pv)[1] = evalsigne(sb)|evallgefint(3);
	(*pv)[2] = xv;
      }
    }
    if (g == 1) return gun;
    else if (g == 2) return gdeux;
    else
    {
      r = cgeti(3);
      r[1] = evalsigne(1)|evallgefint(3);
      r[2] = g;
      return r;
    }
  }

  /* general case */
  av = avma;
  (void)new_chunk(lgefint(b) + (lgefint(a)<<1)); /* room for u,v,gcd */
  /* if a is significantly larger than b, calling lgcdii() is not the best
   * way to start -- reduce a mod b first
   */
  if (lgefint(a) > lgefint(b))
  {
    d = absi(b), q = dvmdii(absi(a), d, &d1);
    if (!signe(d1))		/* a == qb */
    {
      avma = av;
      if (pu != NULL) *pu = gzero;
      if (pv != NULL) *pv = sb < 0 ? negi(gun) : gun;
      return (icopy(d));
    }
    else
    {
      u = gzero;
      u1 = v = gun;
      v1 = negi(q);
    }
    /* if this results in lgefint(d) == 3, will fall past main loop */
  }
  else
  {
    d = absi(a); d1 = absi(b);
    u = v1 = gun; u1 = v = gzero;
  }
  av1 = avma; lim = stack_lim(av, 1);

  /* main loop is almost identical to that of invmod() */
  while (lgefint(d) > 3 && signe(d1))
  {
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, MAXULONG);
    if (lhmres != 0)		/* check progress */
    {				/* apply matrix */
      if ((lhmres == 1) || (lhmres == -1))
      {
	if (xv1 == 1)
	{
	  r = subii(d,d1); d=d1; d1=r;
	  a = subii(u,u1); u=u1; u1=a;
	  a = subii(v,v1); v=v1; v1=a;
	}
	else
	{
	  r = subii(d, mului(xv1,d1)); d=d1; d1=r;
	  a = subii(u, mului(xv1,u1)); u=u1; u1=a;
	  a = subii(v, mului(xv1,v1)); v=v1; v1=a;
	}
      }
      else
      {
	r  = subii(muliu(d,xu),  muliu(d1,xv));
	d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
	a  = subii(muliu(u,xu),  muliu(u1,xv));
	u1 = subii(muliu(u,xu1), muliu(u1,xv1)); u = a;
	a  = subii(muliu(v,xu),  muliu(v1,xv));
	v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1)
	{
          setsigne(d,-signe(d));
          setsigne(u,-signe(u));
          setsigne(v,-signe(v));
        }
        else
	{
          if (signe(d1)) { setsigne(d1,-signe(d1)); }
          setsigne(u1,-signe(u1));
          setsigne(v1,-signe(v1));
        }
      }
    }
    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      fprintferr("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(u,mulii(q,u1));
      u=u1; u1=a;
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[6]; gptr[0]=&d; gptr[1]=&d1; gptr[2]=&u; gptr[3]=&u1;
      gptr[4]=&v; gptr[5]=&v1;
      if(DEBUGMEM>1) err(warnmem,"bezout");
      gerepilemany(av1,gptr,6);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu((ulong)(d[2]), (ulong)(d1[2]), 0, &xu, &xu1, &xv, &xv1, &s);
    u = subii(muliu(u,xu), muliu(u1, xv));
    v = subii(muliu(v,xu), muliu(v1, xv));
    if (s < 0) { sa = -sa; sb = -sb; }
    avma = av;
    if (pu != NULL) *pu = sa < 0 ? negi(u) : icopy(u);
    if (pv != NULL) *pv = sb < 0 ? negi(v) : icopy(v);
    if (g == 1) return gun;
    else if (g == 2) return gdeux;
    else
    {
      r = cgeti(3);
      r[1] = evalsigne(1)|evallgefint(3);
      r[2] = g;
      return r;
    }
  }
  /* get here when the final sprint was skipped (d1 was zero already).
   * Now the matrix is final, and d contains the gcd.
   */
  avma = av;
  if (pu != NULL) *pu = sa < 0 ? negi(u) : icopy(u);
  if (pv != NULL) *pv = sb < 0 ? negi(v) : icopy(v);
  return icopy(d);
}

