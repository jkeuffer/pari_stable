/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (second part)                             **/
/**                                                                   **/
/***********************************************************************/
/* $Id$ */
#include "pari.h"

GEN
polsym(GEN x, long n)
{
  long av1,av2,dx=lgef(x)-3,i,k;
  GEN s,y,x_lead;

  if (n<0) err(impl,"polsym of a negative n");
  if (typ(x) != t_POL) err(typeer,"polsym");
  if (!signe(x)) err(zeropoler,"polsym");
  y=cgetg(n+2,t_COL); y[1]=lstoi(dx);
  x_lead=(GEN)x[dx+2]; if (gcmp1(x_lead)) x_lead=NULL;
  for (k=1; k<=n; k++)
  {
    av1=avma; s = (dx>=k)? gmulsg(k,(GEN)x[dx+2-k]): gzero;
    for (i=1; i<k && i<=dx; i++)
      s = gadd(s,gmul((GEN)y[k-i+1],(GEN)x[dx+2-i]));
    if (x_lead) s = gdiv(s,x_lead);
    av2=avma; y[k+1]=lpile(av1,av2,gneg(s));
  }
  return y;
}

static int (*polcmp_coeff_cmp)(GEN,GEN);

/* assume x and y are polynomials in the same variable whose coeffs can be
 * compared (used to sort polynomial factorizations)
 */
static int
polcmp(GEN x, GEN y)
{
  long i, lx = lgef(x), ly = lgef(y);
  int fl;
#if 0 /* for efficiency */
  if (typ(x) != t_POL || typ(y) != t_POL)
    err(talker,"not a polynomial in polcmp");
#endif
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if ((fl = polcmp_coeff_cmp((GEN)x[i], (GEN)y[i]))) return fl;
  return 0;
}

/* sort polynomial factorization so that factors appear by decreasing
 * degree, sorting coefficients according to cmp. In place */
GEN
sort_factor(GEN y, int (*cmp)(GEN,GEN))
{
  int (*old)(GEN,GEN) = polcmp_coeff_cmp;
  polcmp_coeff_cmp = cmp;
  (void)sort_factor_gen(y,polcmp);
  polcmp_coeff_cmp = old; return y;
}

/* sort generic factorisation */
GEN
sort_factor_gen(GEN y, int (*cmp)(GEN,GEN))
{
  long n,i, av = avma;
  GEN a,b,A,B,w;
  a = (GEN)y[1]; n = lg(a); A = new_chunk(n);
  b = (GEN)y[2];            B = new_chunk(n);
  w = gen_sort(a, cmp_IND | cmp_C, cmp);
  for (i=1; i<n; i++) { A[i] = a[w[i]]; B[i] = b[w[i]]; }
  for (i=1; i<n; i++) { a[i] = A[i]; b[i] = B[i]; }
  avma = av; return y;
}

/* for internal use */
GEN
centermod_i(GEN x, GEN p, GEN ps2)
{
  long av,i,lx;
  GEN y,p1;

  if (!ps2) ps2 = shifti(p,-1);
  switch(typ(x))
  {
    case t_INT:
      y=modii(x,p);
      if (cmpii(y,ps2)>0) return subii(y,p);
      return y;

    case t_POL: lx=lgef(x);
      y=cgetg(lx,t_POL); y[1]=x[1];
      for (i=2; i<lx; i++)
      {
	av=avma; p1=modii((GEN)x[i],p);
	if (cmpii(p1,ps2)>0) p1=subii(p1,p);
	y[i]=lpileupto(av,p1);
      }
      return y;

    case t_COL: lx=lg(x);
      y=cgetg(lx,t_COL);
      for (i=1; i<lx; i++)
      {
	p1=modii((GEN)x[i],p);
	if (cmpii(p1,ps2)>0) p1=subii(p1,p);
	y[i]=(long)p1;
      }
      return y;
  }
  return x;
}

GEN
centermod(GEN x, GEN p) { return centermod_i(x,p,NULL); }

static GEN
decpol(GEN x, long klim)
{
  short int pos[200];
  long av=avma,av1,k,kin,i,j,i1,i2,fl,d,nbfact;
  GEN res,p1,p2;

  kin=1; res=cgetg(lgef(x)-2,t_VEC); nbfact=0;
  p1=roots(x,DEFAULTPREC); d=lg(p1)-1; if (!klim) klim=d;
  do
  {
    fl=1;
    for (k=kin; k+k <= d && k<=klim; k++)
    {
      for (i=0; i<=k; i++) pos[i]=i;
      do
      {
	av1=avma; p2=gzero; j=0;
	for (i1=1; i1<=k; i1++) p2=gadd(p2,(GEN)p1[pos[i1]]);
	if (gexpo(gimag(p2))<-20 && gexpo(gsub(p2,ground(p2)))<-20)
	{
	  p2=gun;
	  for (i1=1; i1<=k; i1++)
	    p2=gmul(p2,gsub(polx[0],(GEN)p1[pos[i1]]));
          p2 = ground(p2);
	  if (gcmp0(gimag(p2)) && gcmp0(gmod(x,p2)))
	  {
	    res[++nbfact]=(long)p2; x=gdiv(x,p2);
            kin=k; p2=cgetg(d-k+1,t_COL);
            for (i=i1=i2=1; i<=d; i++)
	    {
	      if (i1<=k && i==pos[i1]) i1++;
	      else p2[i2++]=p1[i];
	    }
	    p1=p2; d-=k; fl=0; break;
	  }
	}
	avma=av1; pos[k]++;
	while (pos[k-j] > d-j) { j++; pos[k-j]++; }
	for (i=k-j+1; i<=k; i++) pos[i]=i+pos[k-j]-k+j;
      }
      while (j<k);
      if (!fl) break;
    }
    if (lgef(x)<=3) break;
  }
  while (!fl || (k+k <= d && k<=klim));
  if (lgef(x)>3) res[++nbfact]=(long)x;
  setlg(res,nbfact+1);
  return gerepileupto(av,greal(res));
}

/* Note that PARI's idea of the maximum possible coefficient involves the
 * limit on the degree (klim).  Consider revising this.  If I don't respect
 * the degree limit when testing potential factors, there's the possibility
 * that I might identify a high degree factor that isn't irreducible, because
 * it's lower degree divisors were missed because they had a coefficient
 * outside the Borne limit for klim, but the higher degree factor had it's
 * coefficients within Borne.  This would still have the property that any
 * factors of degree <= klim were guaranteed irr, but higher degrees
 * (> 2*klim) might not be irr.
 */

/* assume same variables, y normalized, non constant */
static GEN
polidivis(GEN x, GEN y, GEN bound)
{
  long dx,dy,dz,i,j,av, vx = varn(x);
  GEN z,p1,y_lead;

  dy=lgef(y)-3;
  dx=lgef(x)-3;
  dz=dx-dy; if (dz<0) return NULL;
  z=cgetg(dz+3,t_POL);
  x += 2; y += 2; z += 2;
  y_lead = (GEN)y[dy];
  if (gcmp1(y_lead)) y_lead = NULL;

  p1 = (GEN)x[dx];
  z[dz]=y_lead? ldivii(p1,y_lead): licopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    if (y_lead) { p1 = gdiv(p1,y_lead); if (typ(p1)!=t_INT) return NULL; }
    if (absi_cmp(p1, bound) > 0) return NULL;
    p1 = gerepileupto(av,p1);
    z[i-dy] = (long)p1;
  }
  av = avma;
  for (;; i--)
  {
    p1 = (GEN)x[i];
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    if (!gcmp0(p1)) return NULL;
    avma = av;
    if (!i) break;
  }
  z -= 2;
  z[1]=evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  return z;
}

static long
min_deg(long jmax,ulong tabbit[])
{
  long j, k = 1, j1 = 2;

  for (j=jmax; j>=0; j--)
  {
    for (  ; k<=15; k++)
    {
      if (tabbit[j]&j1) return ((jmax-j)<<4)+k;
      j1<<=1;
    }
    k = 0; j1 = 1;
  }
  return (jmax<<4)+15;
}

/* tabkbit is a bit vector (only lowest 32 bits of each word are used
 * on 64bit architecture): reading from right to left, bit i+1 is set iff
 * degree i is attainable from the factorisation mod p.
 *   
 * record N modular factors of degree d. */
static void
record_factors(long N, long d, long jmax, ulong *tabkbit, ulong *tmp)
{
  long n,j, a = d>>4, b = d&15; /* d = 16 a + b */
  ulong *tmp2 = tmp - a;

  for (n = 1; n <= N; n++)
  {
    ulong pro, rem = 0;
    for (j=jmax; j>=a; j--)
    {
      pro = tabkbit[j] << b;
      tmp2[j] = (pro&0xffff) + rem; rem = pro >> 16;
    }
    for (j=jmax-a; j>=0; j--) tabkbit[j] |= tmp[j];
  }
}

/* lift factorisation mod p: C = lc(C) \prod Q_k  to  mod p^e = pev */
GEN
hensel_lift_fact(GEN pol, GEN Q, GEN p, GEN pev, long e)
{
  long i,j, nf = lg(Q);
  GEN C = pol, res = cgetg(nf, t_VEC), listb = cgetg(nf, t_VEC);
  GEN lc = leading_term(pol);
  long nb, mask;
  nb = hensel_lift_accel(e,&mask)-1;
  if (DEBUGLEVEL > 4) (void)timer2();
  listb[1] = lmodii(lc, p);
  for (i=2; i < nf; i++)
    listb[i] = (long)Fp_pol_red(gmul((GEN)listb[i-1], (GEN)Q[i-1]), p);
  for (i=nf-1; i>1; i--)
  {
    GEN a,b,u,v,a2,b2,s,t,pe,pe2,z,g, pem1;
    long ltop = avma, lbot;

    a = (GEN)Q[i];     /* lead coeff(a) = 1 */
    b = (GEN)listb[i]; /* lc(C) \prod_{k<i} Q_k */
    g = (GEN)Fp_pol_extgcd(a,b,p,&u,&v)[2]; /* deg g = 0 */
    if (!gcmp1(g))
    {
      g = mpinvmod(g, p);
      u = gmul(u, g);
      v = gmul(v, g);
    }
    for(pe=p,pem1=gun,j=0;;j++)
    {
      if (j != nb )
      {
	pem1 = (mask&(1<<j))?sqri(pem1):mulii(pem1, pe);
	pe2  =  mulii(pem1, p);
      }
      else pe2=pev;
      g = gadd(C, gneg_i(gmul(a,b)));

      g = Fp_pol_red(g, pe2); g = gdivexact(g, pe);
      z = Fp_pol_red(gmul(v,g), pe);
      t = Fp_poldivres(z,a,pe, &s);
      t = gadd(gmul(u,g), gmul(t,b));
      t = Fp_pol_red(t, pe);
      t = gmul(t,pe);
      s = gmul(s,pe);
      lbot = avma;
      b2 = gadd(b, t);
      a2 = gadd(a, s); /* already reduced mod pe2 */
      if (j == nb) break;

      g = gadd(gun, gneg_i(gadd(gmul(u,a2),gmul(v,b2))));

      g = Fp_pol_red(g, pe2); g = gdivexact(g, pe);
      z = Fp_pol_red(gmul(v,g), pe);
      t = Fp_poldivres(z,a,pe, &s);
      t = gadd(gmul(u,g), gmul(t,b));
      t = Fp_pol_red(t, pe);
      u = gadd(u, gmul(t,pe));
      v = gadd(v, gmul(s,pe));
      pe = pe2; a = a2; b = b2;
    }
    { GEN *gptr[2]; gptr[0]=&a2; gptr[1]=&b2;
      gerepilemanysp(ltop, lbot, gptr, 2);
    }
    res[i] = (long)a2; C = b2;
    if (DEBUGLEVEL > 4)
      fprintferr("...lifting factor of degree %3ld. Time = %ld\n",
                 lgef(a)-3,timer2());
  }
  if (!gcmp1(lc))
  {
    GEN g = mpinvmod(lc, pev);
    C = Fp_pol_red(gmul(C, g), pev);
  }
  res[1] = (long)C; return res;
}

/* front-end for hensel_lift_factor:
   lift the factorization of pol mod p given by fct to p^exp (if possible) */
GEN 
polhensellift(GEN pol, GEN fct, GEN p, long exp)
{
  GEN p1, p2;
  long av = avma, j, l;

  /* we check the arguments */
  if (typ(pol) != t_POL) 
    err(talker, "not a polynomial in polhensellift");
  if ((typ(fct) != t_COL && typ(fct) != t_VEC) || (lg(fct) < 3))
    err(talker, "not a factorization in polhensellift");
  if (typ(p) != t_INT || !isprime(p))
    err(talker, "not a prime number in polhensellift");
  if (exp < 1) 
    err(talker, "not a positive exponent in polhensellift");

  p1 = lift(fct); /* make sure the coeffs are integers and not intmods */
  l = lg(p1) - 1;

  /* then we check that pol \equiv \prod f ; f \in fct mod p */
  p2 = (GEN)p1[1];
  for (j = 2; j <= l; j++) p2 = Fp_mul(p2, (GEN)p1[j], p);
  if (!gcmp0(Fp_sub(pol, p2, p)))
    err(talker, "not a correct factorization in polhensellift");

  /* finally we check that the elements of fct are coprime mod p */
  if (gcmp0(discsr(Fp_pol(pol, p))))
    err(talker, "factors are not coprime in polhensellift");

  return gerepileupto(av, gcopy(hensel_lift_fact(pol, p1, p, 
						 gpowgs(p, exp), exp)));
}

#if 0
/* lift factorisation mod p: C = lc(C) \prod Q_k  to  mod p^e = pev */
GEN
hensel_lift_fact_linear(GEN pol, GEN Q, GEN p, GEN pev, long e)
{
  long i,j, nf = lg(Q);
  GEN C = pol, res = cgetg(nf, t_VEC), listb = cgetg(nf, t_VEC);
  GEN lc = leading_term(pol), q = p;

  if (DEBUGLEVEL > 4) (void)timer2();
  if (!is_bigint(p) && is_bigint(pev))
  {
    long c = 1; pp = itos(p);
    for(;;)
    {
      GEN q2 = mulsi(pp,q);
      if (2 * expi(q2) + 6 >= BITS_IN_LONG) break;
      q = q2; c++;
    }
    e = (e/c) + 1;
  }
  listb[1] = lmodii(lc, p);
  for (i=2; i < nf; i++)
    listb[i] = (long)Fp_pol_red(gmul((GEN)listb[i-1], (GEN)Q[i-1]), p);
  for (i=nf-1; i>1; i--)
  {
    GEN a,b,u,v,a2,b2,s,t,pe,pe2,z,g, pem1;
    long ltop = avma, lbot;

    a = (GEN)Q[i];     /* lead coeff(a) = 1 */
    b = (GEN)listb[i]; /* lc(C) \prod_{k<i} Q_k */
    g = (GEN)Fp_pol_extgcd(a,b,p,&u,&v)[2]; /* deg g = 0 */
    if (!gcmp1(g))
    {
      g = mpinvmod(g, p);
      u = gmul(u, g);
      v = gmul(v, g);
    }
    for(pe=p,pem1=gun,j=0;;j++)
    {
      if (j != nb )
      {
	pem1 = (mask&(1<<j))?sqri(pem1):mulii(pem1, pe);
	pe2  =  mulii(pem1, p);
      }
      else pe2=pev;
      g = gadd(C, gneg_i(gmul(a,b)));

      g = Fp_pol_red(g, pe2); g = gdivexact(g, pe);
      z = Fp_pol_red(gmul(v,g), pe);
      t = Fp_poldivres(z,a,pe, &s);
      t = gadd(gmul(u,g), gmul(t,b));
      t = Fp_pol_red(t, pe);
      t = gmul(t,pe);
      s = gmul(s,pe);
      lbot = avma;
      b2 = gadd(b, t);
      a2 = gadd(a, s); /* already reduced mod pe2 */
      if (j == nb) break;

      g = gadd(gun, gneg_i(gadd(gmul(u,a2),gmul(v,b2))));

      g = Fp_pol_red(g, pe2); g = gdivexact(g, pe);
      z = Fp_pol_red(gmul(v,g), pe);
      t = Fp_poldivres(z,a,pe, &s);
      t = gadd(gmul(u,g), gmul(t,b));
      t = Fp_pol_red(t, pe);
      u = gadd(u, gmul(t,pe));
      v = gadd(v, gmul(s,pe));
      pe = pe2; a = a2; b = b2;
    }
    { GEN *gptr[2]; gptr[0]=&a2; gptr[1]=&b2;
      gerepilemanysp(ltop, lbot, gptr, 2);
    }
    res[i] = (long)a2; C = b2;
    if (DEBUGLEVEL > 4)
      fprintferr("...lifting factor of degree %3ld. Time = %ld\n",
                 lgef(a)-3,timer2());
  }
  if (!gcmp1(lc))
  {
    GEN g = mpinvmod(lc, pev);
    C = Fp_pol_red(gmul(C, g), pev);
  }
  res[1] = (long)C; return res;
}
#endif

/* cf Beauzamy et al: upper bound for
 *      lc(x) * [2^(5/8) / pi^(3/8)] e^(1/4n) 2^(n/2) sqrt([x]_2)/ n^(3/8)
 * where [x]_2 = sqrt(\sum_i=0^n x[i]^2 / binomial(n,i)). One factor has 
 * all coeffs less than then bound */
static GEN
two_factor_bound(GEN x)
{
  long av = avma, i,j, n = lgef(x) - 3;
  GEN *invbin, c, r = cgetr(3), z;

  x += 2; invbin = (GEN*)new_chunk(n+1);
  z = realun(3); /* invbin[i] = 1 / binomial(n, i) */
  for (i=0,j=n; j >= i; i++,j--)
  {
    invbin[i] = invbin[j] = z;
    z = divrs(mulrs(z, i+1), n-i);
  }
  z = invbin[0]; /* = 1 */
  for (i=0; i<=n; i++)
  {
    c = (GEN)x[i]; if (!signe(c)) continue;
    affir(c, r);
    z = addrr(z, mulrr(gsqr(r), invbin[i]));
  }
  z = shiftr(mpsqrt(z), n);
  z = divrr(z, dbltor(pow((double)n, 0.75)));
  z = grndtoi(mpsqrt(z), &i);
  z = mulii(z, absi((GEN)x[n]));
  return gerepileuptoint(av, shifti(z, 1));
}

static GEN
uniform_Mignotte_bound(GEN x)
{
  long e, n = lgef(x)-3;
  GEN p1, N2 = mpsqrt(fastnorml2(x,DEFAULTPREC));

  p1 = grndtoi(gmul2n(N2, n), &e);
  if (e>=0) p1 = addii(p1, shifti(gun, e));
  return p1;
}

/* all factors have coeffs less than the bound */
static GEN
all_factor_bound(GEN x)
{
  long i, n = lgef(x) - 3;
  GEN t, z = gzero;
  for (i=2; i<=n+2; i++) z = addii(z,sqri((GEN)x[i]));
  t = absi((GEN)x[n+2]);
  z = addii(t, addsi(1, racine(z)));
  z = mulii(z, binome(stoi(n-1), n>>1));
  return shifti(mulii(t,z),1);
}

/* recombination of modular factors: naive algorithm */

/* target = polynomial we want to factor
 * famod = array of modular factors.  Each has LC 1.1 based indexing. Product
 * should be congruent to target/lc(target) modulo pe.
 * Combine up to maxK modular factors, degree <= klim and divisible by hint
 * If lmod != NULL, put the list of modular factors correponding to each
 * factor found (the factor may be reducible if pe was chosen small than the
 * rigorous bound [for efficiency])
 */
static GEN
cmbf(GEN target, GEN famod, GEN pe, long maxK, long klim,long hint)
{
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1;
  GEN lc, lctarget, pes2 = shifti(pe,-1);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN deg      = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN listmod  = cgetg(lfamod+1, t_COL);
  GEN fa       = cgetg(lfamod+1, t_COL);
  GEN res = cgetg(3, t_VEC);
  GEN bound = all_factor_bound(target);

  if (!maxK) maxK = lfamod-1;

  lc = absi(leading_term(target));
  lctarget = gmul(lc,target);

  for (i=1; i <= lfamod; i++) deg[i] = lgef(famod[i]) - 3;
  degsofar[0] = 0; /* sentinel */

  /* ind runs through strictly increasing sequences of length K,
   * 1 <= ind[i] <= lfamod */
nextK:
  if (K > maxK) goto END;
  if (DEBUGLEVEL > 4)
    fprintferr("\n### K = %d, %Z combinations\n", K,binome(stoi(lfamod), K));
  setlg(ind, K+1); ind[1] = 1;
  i = 1; curdeg = deg[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++) 
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += deg[ind[j+1]];
    }
    if (curdeg <= klim && curdeg % hint == 0) /* trial divide */
    {
      GEN y, q, cont, list;
      long av = avma;

      y = lc; /* check trailing coeff first */
      for (i=1; i<=K; i++)
        y = centermod_i(mulii(y, gmael(famod,ind[i],2)), pe, pes2);
      if (!signe(y) || resii((GEN)lctarget[2], y) != gzero)
      {
        if (DEBUGLEVEL>6) fprintferr(".");
        avma = av; goto NEXT;
      }
      y = lc; /* full computation */
      for (i=1; i<=K; i++)
        y = centermod_i(gmul(y, (GEN)famod[ind[i]]), pe, pes2);

      /* y is the candidate factor */
      if (! (q = polidivis(lctarget,y,bound)) )
      {
        if (DEBUGLEVEL>6) fprintferr("*");
        avma = av; goto NEXT;
      }
      /* found a factor */
      cont = content(y);
      if (signe(leading_term(y)) < 0) cont = negi(cont);
      y = gdiv(y, cont);

      list = cgetg(K+1, t_VEC);
      listmod[cnt] = (long)list;
      for (i=1; i<=K; i++) list[i] = famod[ind[i]];

      fa[cnt++] = (long)y;
      /* fix up target */
      target = gdiv(q, leading_term(y));
      for (i=j=k=1; i <= lfamod; i++)
      { /* remove used factors */
        if (j <= K && i == ind[j]) j++;
        else 
        {
          famod[k] = famod[i];
          deg[k] = deg[i]; k++;
        }
      }
      lfamod -= K;
      if (lfamod <= K) goto END; /* = K in fact */
      i = 1; curdeg = deg[ind[1]];
      bound = all_factor_bound(target);
      lc = absi(leading_term(target));
      lctarget = gmul(lc,target);
      if (DEBUGLEVEL > 2)
      { 
        fprintferr("\n"); msgtimer("to find factor %Z",y);
        fprintferr("remaining modular factor(s): %ld\n", lfamod);
      }
      continue;
    }

NEXT:
    for (i = K+1;;)
    {
      if (--i == 0) { K++; goto nextK; }
      if (++ind[i] <= lfamod - K + i)
      {
        curdeg = degsofar[i-1] + deg[ind[i]];
        if (curdeg <= klim) break;
      }
    }
  }
END:
  if (lgef(target) > 3)
  { /* leftover factor */
    if (signe(leading_term(target)) < 0) target = gneg_i(target);

    setlg(famod, lfamod+1);
    listmod[cnt] = (long)dummycopy(famod);
    fa[cnt++] = (long)target;
  }
  if (DEBUGLEVEL>6) fprintferr("\n");
  setlg(listmod, cnt); setlg(fa, cnt);
  res[1] = (long)fa;
  res[2] = (long)listmod; return res;
}

void
factor_quad(GEN x, GEN res, long *ptcnt)
{
  GEN a = (GEN)x[4], b = (GEN)x[3], c = (GEN)x[2], d, u, z1, z2, t;
  GEN D = subii(sqri(b), shifti(mulii(a,c), 2));
  long v, cnt = *ptcnt;

  if (!carrecomplet(D, &d)) { res[cnt++] = (long)x; *ptcnt = cnt; return; }

  t = shifti(negi(addii(b, d)), -1);
  z1 = gdiv(t, a); u = denom(z1);
  z2 = gdiv(addii(t, d), a);
  v = varn(x);
  res[cnt++] = lmul(u, gsub(polx[v], z1)); u = divii(a, u);
  res[cnt++] = lmul(u, gsub(polx[v], z2)); *ptcnt = cnt;
}

static long
get_e(GEN B, GEN p, GEN *ptpe)
{
  GEN pe;
  long e;
  for (e=1,pe=p; cmpii(pe, B) < 0; e++) pe = mulii(pe,p);
  *ptpe =  pe; return e;
}

void
refine_factors(GEN LL, GEN prime, long klim, long hint, long e, GEN res,
               long *pcnt, int check_last)
{
  GEN L = (GEN)LL[1], listmod = (GEN)LL[2];
  long i, cnt = *pcnt, last = lg(L)-1;

  for (i=1; i <= last; i++)
  {
    GEN famod = (GEN)listmod[i];
    GEN x = (GEN)L[i];
    long dx = lgef(x)-3;

    if (lg(famod) == 2) res[cnt++] = (long)x;
    else if (dx == 2) factor_quad(x, res, &cnt);
    else
    {
      GEN L2, pe, B = two_factor_bound(x);
      long e2, klim2 = min(klim, dx>>1);

      e2 = get_e(B, prime, &pe);
      if (DEBUGLEVEL > 4)
        fprintferr("Fact. %ld, two-factor bound: %Z\n",i, B);
      if (e2 <= e && (!check_last || i < last)) res[cnt++] = (long)x;
      else
      {
        if (e2 != e) famod = hensel_lift_fact(x,famod,prime,pe,e2);

        L2 = cmbf(x, famod, pe, 0, klim2, hint);
        if (DEBUGLEVEL > 4 && lg(L2[1]) > 2)
          fprintferr("split in %ld\n",lg(L2[1])-1);
        refine_factors(L2, prime, klim, hint, e2, res, &cnt, 0);
      }
    }
  }
  *pcnt = cnt;
}

/* recombination of modular factors: Hoeij's algorithm */

/* compute Newton sums of P (i-th powers of roots, i=1..n)
 * If N != NULL, assume p-adic roots and compute mod N [assume integer coeffs]
 * If y0!= NULL, precomputed i-th powers, i=1..m, m = length(y0) */
GEN
polsym_gen(GEN P, GEN y0, long n, GEN N)
{
  long av1,av2,dP=lgef(P)-3,i,k,m;
  GEN s,y,P_lead;

  if (n<0) err(impl,"polsym of a negative n");
  if (typ(P) != t_POL) err(typeer,"polsym");
  if (!signe(P)) err(zeropoler,"polsym");
  y = cgetg(n+2,t_COL);
  if (y0)
  {
    if (typ(y0) != t_COL) err(typeer,"polsym_gen");
    m = lg(y0)-1;
    for (i=1; i<=m; i++) y[i] = lcopy((GEN)y0[i]);
  }
  else
  {
    m = 1;
    y[1] = lstoi(dP);
  }
  P += 2; /* strip codewords */

  P_lead=(GEN)P[dP]; if (gcmp1(P_lead)) P_lead=NULL;
  if (N && P_lead)
    if (!invmod(P_lead,N,&P_lead))
      err(talker,"polsyn: non-invertible leading coeff: %Z", P_lead);
  for (k=m; k<=n; k++)
  {
    av1=avma; s = (dP>=k)? gmulsg(k,(GEN)P[dP-k]): gzero;
    for (i=1; i<k && i<=dP; i++)
      s = gadd(s, gmul((GEN)y[k-i+1],(GEN)P[dP-i]));
    if (N)
    {
      s = modii(s, N);
      if (P_lead) { s = mulii(s,P_lead); s = modii(s,N); }
    }
    else
      if (P_lead) s = gdiv(s,P_lead);
    av2=avma; y[k+1]=lpile(av1,av2,gneg(s));
  }
  return y;
}

/* return integer y such that all roots of P are less than y */
static GEN
root_bound(GEN P)
{
  GEN P0 = dummycopy(P), lP = absi(leading_term(P)), x,y,z;
  long k,d = lgef(P)-3;

  setlgef(P0, d+2); /* P = lP x^d + P0 */
  P = P0+2; /* strip codewords */
  for (k=0; k<d; k++) P[k] = labsi((GEN)P[k]);

  x = y = gun;
  for (k=0; ; k++)
  {
    if (cmpii(poleval(P0,y), mulii(lP, gpowgs(y, d))) < 0) break;
    x = y; y = shifti(y,1);
  }
  for(;;)
  {
    z = shifti(addii(x,y), -1);
    if (egalii(x,z)) break;
    if (cmpii(poleval(P0,z), mulii(lP, gpowgs(z, d))) < 0)
      y = z;
    else 
      x = z;
  }
  return y;
}

extern GEN gscal(GEN x,GEN y);
extern GEN sqscal(GEN x);

/* return Gram-Schmidt orthogonal basis (f) associated to (e), B is the
 * vector of the (f_i . f_i)*/
GEN
gram_schmidt(GEN e, GEN *ptB)
{
  long i,j,lx = lg(e);
  GEN f = dummycopy(e), B, iB;

  B = cgetg(lx, t_VEC);
  iB= cgetg(lx, t_VEC);

  for (i=1;i<lx;i++)
  {
    GEN p1 = NULL;
    B[i] = (long)sqscal((GEN)f[i]);
    iB[i]= linv((GEN)B[i]);
    for (j=1; j<i; j++)
    {
      GEN mu = gmul(gscal((GEN)e[i],(GEN)f[j]), (GEN)iB[j]);
      GEN p2 = gmul(mu, (GEN)f[j]);
      p1 = p1? gadd(p1,p2): p2;
    }
    p1 = p1? gsub((GEN)e[i], p1): (GEN)e[i];
    f[i] = (long)p1;
  }
  *ptB = B; return f;
}

extern GEN lincomb_integral(GEN u, GEN v, GEN X, GEN Y);

/* gauss pivot on integer matrix x. Check that each line contains a single
 * non zero entry, equal to \pm 1 */
GEN 
special_pivot(GEN x)
{
  long i,j,k,lx = lg(x), hx = lg(x[1]);
  GEN p,p1,p2, c = cgetg(lx, t_VECSMALL);

  for (i=1; i<lx; i++) c[i] = 0;

  x = dummycopy(x);
  for (i=1; i<lx; i++)
  {
    p1 = (GEN)x[i]; p = NULL;
    for (j=1; j<hx; j++)
    {
      long a = absi_cmp((GEN)p1[j], gun);
      if (a == 0) { p = (GEN)p1[j]; c[i] = j; break; }
    }
    if (!p) return NULL;

    p = negi(p);
    for (k=i+1; k<lx; k++)
    {
      p2 = (GEN)x[k];
      if (!signe(p2[j])) continue;
      x[k] = (long)lincomb_integral(gun, mulii(p, (GEN)p2[j]), p2, p1);
    }
  }
  for (i=1; i<lx; i++)
    if (!c[i]) return NULL;
  for (i=1; i<hx; i++)
  {
    for (j=1; j<lx; j++)
      if (signe(gcoeff(x,i,j))) break;
    if (j==lx) return NULL;
  }

  for (i=lx-1; i>0; i--)
  {
    p1 = (GEN)x[i];
    for (j=1; j<hx; j++)
    {
      long a = absi_cmp((GEN)p1[j], gun);
      if (a > 0) return NULL;
    }
    j = c[i]; p = negi((GEN)p1[j]);
    for (k=1; k<i; k++)
    {
      p2 = (GEN)x[k];
      if (!signe(p2[j])) continue;
      x[k] = (long)lincomb_integral(gun, mulii(p, (GEN)p2[j]), p2, p1);
    }
  }
  for (i=1; i<hx; i++)
  {
    long fl = 0;
    for (j=1; j<lx; j++)
    {
      long a = absi_cmp(gcoeff(x,i,j), gun);
      if (a > 0) continue;
      if (a == 0)
      {
        if (fl) return NULL;
        fl = 1;
      }
    }
  }
  return x;
}

/* Assume P is monic squarefree in Z[X], factor it.
 * famod = array of (lifted) modular factors mod p^a
 *
 * previously recombined all set of factors with less than rec elts
 */
GEN
LLL_cmbf(GEN P, GEN famod, GEN p, GEN pa, GEN bound, long a, long rec)
{
  long i,j,C,r,tmax,n0,n,s,dP = lgef(P)-3;
  double logp = log(gtodouble(p));
  double b0 = log((double)dP*2) / logp;
  double k = gtodouble(glog(root_bound(P), DEFAULTPREC)) / logp;
  GEN y, T, T2, TT, BL, m, mGram, u, norm, target, M, piv, list;

  n0 = n = r = lg(famod) - 1;
  s = 2;
  BL = idmat(n0);
  list = cgetg(n0+1, t_COL);
  TT = cgetg(n0+1, t_VEC);
  T  = cgetg(n0+1, t_MAT);
  for (i=1; i<=n; i++)
  {
    TT[i] = 0;
    T [i] = lgetg(s+1, t_COL);
  }
  for(tmax = 0;; tmax += s) 
  {
    long b = (long)ceil(b0 + (tmax+s)*k), goodb;
    GEN pas2, pa_b, pb_as2, pbs2, pb, BE;

    if (a <= b)
    {
      a = ceil(b + 3*s*k) + 1;
      pa = gpowgs(p,a);
      famod = hensel_lift_fact(P,famod,p,pa,a);
    }
    goodb = (long) a - 0.12 * n0 * n0 / logp;
    if ((a - goodb)*logp < 64*LOG2) goodb = (long) a - 64*LOG2/logp;
    if (goodb > b) b = goodb;
    pa_b = gpowgs(p, a-b); pb_as2 = shifti(pa_b,-1);
    pb   = gpowgs(p, b);   pbs2    = shifti(pb,-1);
    C = (long)(sqrt((double)s*n)/ 2);
    M = dbltor((C*C*n + s*n*n/4.) * 1.00001);

    if (DEBUGLEVEL>3)
      fprintferr("LLL_cmbf: %ld potential factors (tmax = %ld)\n", r, tmax);
    for (i=1; i<=n0; i++)
    {
      GEN p1 = (GEN)T[i];
      GEN p2 = polsym_gen((GEN)famod[i], (GEN)TT[i], tmax+s, pa);
      TT[i] = (long)p2;
      p2 += 1+tmax; /* ignore traces number 0...tmax */
      for (j=1; j<=s; j++) p1[j] = p2[j];
    }
    T2 = gmul(T, BL);
    for (i=1; i<=r; i++)
    {
      GEN p1 = (GEN)T2[i];
      for (j=1; j<=s; j++)
      {
        GEN r3, p3 = dvmdii(modii((GEN)p1[j], pa), pb, &r3);
        if (cmpii(r3,  pbs2) > 0) p3 = addis(p3,1);
        if (cmpii(p3,pb_as2) > 0) p3 = subii(p3,pa_b);
        p1[j] = (long)p3;
      }
    }
    if (gcmp0(T2)) continue;

    BE = cgetg(s+1, t_MAT);
    for (i=1; i<=s; i++)
    {
      GEN p1 = cgetg(r+s+1,t_COL);
      for (j=1; j<=r+s; j++) p1[j] = zero;
      p1[i+r] = (long)pa_b;
      BE[i] = (long)p1;
    }
    m = gscalmat(stoi(C), r);
    for (i=1; i<=r; i++)
      m[i] = (long)concatsp((GEN)m[i], (GEN)T2[i]);
    m = concatsp(m, BE);
    mGram = gram_matrix(m);
    u = lllgramintern(mGram, 4, 0, 0);
    m = gmul(m,u);
    (void)gram_schmidt(gmul(m, realun(DEFAULTPREC)), &norm);
    for (i=r+s; i>0; i--)
      if (cmprr((GEN)norm[i], M) < 0) break;
    if (i > r) continue;

    n = r; r = i;
    if (r == 1) { list[1] = (long)P; setlg(list,2); return list; }

    setlg(u, r+1);
    for (i=1; i<=r; i++) setlg(u[i], n+1);
    BL = gmul(BL, u);
    if (r*rec >= n0) continue;

    {
      long av = avma;
      piv = special_pivot(BL);
      if (!piv) { avma = av; continue; }
    }

    pas2 = shifti(pa,-1); target = P;
    for (i=1; i<=r; i++)
    {
      GEN q, p1 = (GEN)piv[i];

      y = gun;
      for (j=1; j<=n0; j++)
        if (signe(p1[j]))
          y = centermod_i(gmul(y, (GEN)famod[j]), pa, pas2);

      /* y is the candidate factor */
      if (! (q = polidivis(target,y,bound)) ) break;
      if (signe(leading_term(y)) < 0) y = gneg(y);
      target = gdiv(q, leading_term(y));
      list[i] = (long)y;
    }
    if (i > r) { setlg(list,r+1); return list; }
  }
}

extern GEN primitive_pol_to_monic(GEN pol, GEN *ptlead);

/* P(hx), in place. Assume P in Z[X], h in Z */
void
rescale_pol_i(GEN P, GEN h)
{
  GEN hi = gun;
  long i, l = lgef(P);
  for (i=3; i<l; i++)
  {
    hi = mulii(hi,h); P[i] = lmulii((GEN)P[i], hi);
  }
}

/* use van Hoeij's knapsack algorithm */
static GEN
combine_factors(GEN a, GEN famod, GEN p, long klim, long hint)
{
  GEN B = uniform_Mignotte_bound(a), res,y,lt,L,pe,listmod,p1;
  long i,e,l, maxK = 3, nft = lg(famod)-1;

  e = get_e(B, p, &pe);

  if (DEBUGLEVEL > 4) fprintferr("Mignotte bound: %Z\n", B);
  famod = hensel_lift_fact(a,famod,p,pe,e);
  if (nft < 11) maxK = 0;
  else
  {
    lt = leading_term(a);
    if (!is_pm1(lt) && nft < 13) maxK = 0;
  }
  L = cmbf(a, famod, pe, maxK, klim, hint);

  res     = (GEN)L[1];
  listmod = (GEN)L[2]; l = lg(listmod);
  famod = (GEN)listmod[l-1];
  if (maxK && lg(famod)-1 > maxK)
  {
    a = (GEN)res[l-1];
    lt = leading_term(a);
    if (signe(lt) < 0) { a = gneg_i(a); lt = leading_term(a); }
    if (DEBUGLEVEL > 4) fprintferr("last factor still to be checked\n");
    if (gcmp1(lt))
      lt = NULL;
    else
    {
      if (DEBUGLEVEL > 4) fprintferr("making it monic\n");
      a = primitive_pol_to_monic(a, &lt);
      B = uniform_Mignotte_bound(a);
      e = get_e(B, p, &pe);
      famod = hensel_lift_fact(a,famod,p,pe,e);
    }
    setlg(res, l-1); /* remove last elt (possibly unfactored) */
    L = LLL_cmbf(a, famod, p, pe, B, e, maxK);
    if (lt)
    {
      for (i=1; i<lg(L); i++)
      {
        y = (GEN)L[i]; rescale_pol_i(y, lt);
        p1 = content(y); if (!is_pm1(p1)) y = gdiv(y, p1);
        L[i] = (long)y;
      }
    }
    res = concatsp(res, L);
  }
  return res;
}

#if 0
/* naive recombination */
static GEN
combine_factors_old(GEN a, GEN famod, GEN p, long klim, long hint)
{
  GEN B = stoi(EXP220), L,pe,res;
  long e, nft = lg(famod)-1, cnt = 1, maxK = nft / 6, check_last = 0;

  res = cgetg(nft+1, t_VEC);
  e = get_e(B, p, &pe);
  if (maxK > 8) maxK = 8;
  if (maxK < 4) maxK = 0;

  if (DEBUGLEVEL > 4) fprintferr("(first) bound: %Z\n", B);
  famod = hensel_lift_fact(a,famod,p,pe,e);
  L = cmbf(a, famod, pe, maxK, klim, hint);
  if (maxK)
  {
    GEN listmod = (GEN)L[2];
    long l = lg(listmod);
    if (lg(listmod[l-1])-1 > maxK) check_last = 1;
    if (DEBUGLEVEL > 4) fprintferr("last factor still to be checked\n");
  }
  refine_factors(L, p, klim, hint, e, res, &cnt, check_last);
  setlg(res, cnt); return res;
}
#endif

extern long split_berlekamp(GEN Q, GEN *t, GEN pp, GEN pps2);

/* assume degree(a) > 0, a(0) != 0, and a squarefree */
static GEN
squff(GEN a, long klim, long hint)
{
  GEN res,Q,prime,primes2,famod,p1,y,g,z,w,*tabd,*tabdnew;
  long av=avma,va=varn(a),da=lgef(a)-3;
  long chosenp,p,nfacp,lbit,i,j,d,e,np,nmax,lgg,nf,nft;
  ulong *tabbit, *tabkbit, *tmp;
  byteptr pt=diffptr;
  const int NOMBDEP = 5;

  if (hint < 0) return decpol(a,klim);
  if (!hint) hint = 1;
  if (DEBUGLEVEL > 2) timer2();
  lbit=(da>>4)+1; nmax=da+1; i=da>>1;
  if (!klim || klim>i) klim=i;
  chosenp = 0;
  tabd = NULL;
  tabdnew = (GEN*)new_chunk(nmax);
  tabbit  = (ulong*)new_chunk(lbit);
  tabkbit = (ulong*)new_chunk(lbit);
  tmp     = (ulong*)new_chunk(lbit);
  prime = icopy(gun);
  for (p = np = 0; np < NOMBDEP; )
  {
    GEN minuspolx;
    p += *pt++; if (!*pt) err(primer1);
    if (!smodis((GEN)a[da+2],p)) continue;
    prime[2] = p; z = Fp_pol(a, prime);
    if (gcmp0(discsr(z))) continue;
    z = lift_intern(z);

    for (j=0; j<lbit-1; j++) tabkbit[j] = 0;
    tabkbit[j] = 1;
    d=0; e=da; nfacp=0;
    w = polx[va]; minuspolx = gneg(w);
    while (d < (e>>1))
    {
      d++; w = Fp_pow_mod_pol(w, prime, z, prime);
      g = Fp_pol_gcd(z, gadd(w, minuspolx), prime);
      tabdnew[d]=g; lgg=lgef(g)-3;
      if (lgg > 0)
      {
	z = Fp_poldivres(z, g, prime, NULL);
        e = lgef(z)-3;
        w = Fp_poldivres(w, z, prime, ONLY_REM);
        lgg /= d; nfacp += lgg;
        if (DEBUGLEVEL>5)
          fprintferr("   %3ld %s of degree %3ld\n",
                     lgg, lgg==1?"factor": "factors",d);
	record_factors(lgg, d, lbit-1, tabkbit, tmp);
      }
    }
    if (e > 0)
    {
      if (DEBUGLEVEL>5) fprintferr("   %3ld factor of degree %3ld\n",1,e);
      tabdnew[e] = z; nfacp++;
      record_factors(1, e, lbit-1, tabkbit, tmp);
    }
    if (np)
      for (j=0; j<lbit; j++) tabbit[j] &= tabkbit[j];
    else
      for (j=0; j<lbit; j++) tabbit[j] = tabkbit[j];
    if (DEBUGLEVEL > 4)
      fprintferr("...tried prime %3ld (%-3ld %s). Time = %ld\n",
                  p,nfacp,nfacp==1?"factor": "factors",timer2());
    if (min_deg(lbit-1,tabbit) > klim)
    {
      avma = av; y = cgetg(2,t_COL);
      y[1] = lcopy(a); return y;
    }
    if (nfacp < nmax)
    {
      nmax=nfacp; tabd=tabdnew; chosenp=p;
      for (j=d+1; j<e; j++) tabd[j]=polun[va];
      tabdnew = (GEN*)new_chunk(da);
    }
    np++;
  }
  prime[2]=chosenp; primes2 = shifti(prime, -1);
  nf=nmax; nft=1;
  y=cgetg(nf+1,t_COL); famod=cgetg(nf+1,t_COL);
  Q = cgetg(da+1,t_MAT);
  for (i=1; i<=da; i++) Q[i] = lgetg(da+1, t_COL);
  p1 = (GEN)Q[1]; for (i=1; i<=da; i++) p1[i] = zero;
  for (d=1; nft<=nf; d++)
  {
    g=tabd[d]; lgg=lgef(g)-3;
    if (lgg)
    {
      long n = lgg/d;
      famod[nft] = (long)normalize_mod_p(g, prime);
      if (n > 1) (void)split_berlekamp(Q, (GEN*)(famod+nft),prime,primes2);
      nft += n;
    }
  }
  if (DEBUGLEVEL > 4) msgtimer("splitting mod p = %ld",chosenp);
#if 0
  res = combine_factors_old(a, famod, prime, klim, hint);
#else
  res = combine_factors(a, famod, prime, klim, hint);
#endif
  return gerepileupto(av, gcopy(res));
}

GEN
deflate(GEN x0, long *m)
{
  long d = 0, i, id, lx = lgef(x0)-2;
  GEN x = x0 + 2;

  for (i=1; i<lx; i++)
    if (!gcmp0((GEN)x[i])) { d = cgcd(d,i); if (d == 1) break; }
  *m = d;
  if (d > 1)
  {
    GEN z, y;
    long ly = (lx-1)/d + 3;
    y = cgetg(ly, t_POL);
    y[1] = evalsigne(1)|evallgef(ly)|evalvarn(varn(x0));
    z = y + 2; ly -= 2;
    for (i=id=0; i<ly; i++,id+=d) z[i] = x[id];
    x0 = y;
  }
  return x0;
}

GEN
inflate(GEN x0, long d)
{
  long i, id, ly, lx = lgef(x0)-2;
  GEN x = x0 + 2, z, y;
  ly = (lx-1)*d + 3;
  y = cgetg(ly, t_POL);
  y[1] = evalsigne(1)|evallgef(ly)|evalvarn(varn(x0));
  z = y + 2; ly -= 2;
  for (i=0; i<ly; i++) z[i] = zero;
  for (i=id=0; i<lx; i++,id+=d) z[id] = x[i];
  return y;
}

GEN
squff2(GEN x, long klim, long hint)
{
  GEN L;
  long m;
  x = deflate(x, &m);
  L = squff(x, klim, hint);
  if (m > 1)
  {
    GEN e, v, fa = decomp(stoi(m));
    long i,j,k, l;

    e = (GEN)fa[2]; k = 0;
    fa= (GEN)fa[1]; l = lg(fa);
    for (i=1; i<l; i++)
    {
      e[i] = itos((GEN)e[i]);
      k += e[i];
    }
    v = cgetg(k+1, t_VECSMALL); k = 1;
    for (i=1; i<l; i++)
      for (j=1; j<=e[i]; j++) v[k++] = itos((GEN)fa[i]);
    for (k--; k; k--)
    {
      GEN L2 = cgetg(1,t_VEC);
      for (i=1; i < lg(L); i++)
        L2 = concatsp(L2, squff(inflate((GEN)L[i], v[k]), klim,hint));
      L = L2;
    }
  }
  return L;
}

/* klim=0 habituellement, sauf si l'on ne veut chercher que les facteurs
 * de degre <= klim
 */
GEN
factpol(GEN x, long klim, long hint)
{
  GEN fa,p1,d,t,v,w, y = cgetg(3,t_MAT);
  long av=avma,av2,lx,vx,i,j,k,ex,nbfac,zval;

  if (typ(x)!=t_POL) err(notpoler,"factpol");
  if (!signe(x)) err(zeropoler,"factpol");

  ex = nbfac = 0;
  p1 = x+2; while (gcmp0((GEN)*p1)) p1++;
  zval = p1 - (x + 2);
  lx = lgef(x) - zval;
  vx = varn(x);
  if (zval)
  {
    x = cgetg(lx, t_POL); p1 -= 2;
    for (i=2; i<lx; i++) x[i] = p1[i];
    x[1] = evalsigne(1)|evalvarn(vx)|evallgef(lx);
    nbfac++;
  }
  /* now x(0) != 0 */
  if (lx==3) { fa = NULL;/* for lint */ goto END; }
  p1 = cgetg(1,t_VEC); fa=cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) fa[i] = (long)p1;
  d=content(x); if (gsigne(leading_term(x)) < 0) d = gneg_i(d);
  if (!gcmp1(d)) x=gdiv(x,d);
  if (lx==4) { nbfac++; ex++; fa[1] = (long)concatsp(p1,x); goto END; }

  w=derivpol(x); t=modulargcd(x,w);
  if (!gcmp1(t)) { x=gdeuc(x,t); w=gdeuc(w,t); }
  k=1;
  while (k)
  {
    ex++; w=gadd(w, gneg_i(derivpol(x))); k=signe(w);
    if (k) { t=modulargcd(x,w); x=gdeuc(x,t); w=gdeuc(w,t); } else t=x;
    if (lgef(t) > 3)
    {
      fa[ex] = (long)squff2(t,klim,hint);
      nbfac += lg(fa[ex])-1;
    }
  }
END: av2=avma;
  v=cgetg(nbfac+1,t_COL); y[1]=(long)v;
  w=cgetg(nbfac+1,t_COL); y[2]=(long)w;
  if (zval) { v[1]=lpolx[vx]; w[1]=lstoi(zval); k=1; } else k=0;
  for (i=1; i<=ex; i++)
    for (j=1; j<lg(fa[i]); j++)
    {
      k++; v[k]=lcopy(gmael(fa,i,j)); w[k]=lstoi(i);
    }
  gerepilemanyvec(av,av2,y+1,2);
  return sort_factor(y, cmpii);
}

GEN
factpol2(GEN x, long klim)
{
  return factpol(x,klim,-1);
}

/***********************************************************************/
/**                                                                   **/
/**                          FACTORISATION                            **/
/**                                                                   **/
/***********************************************************************/
#define LT 17
#define assign_or_fail(x,y) {\
  if (y==NULL) y=x; else if (!gegal(x,y)) return 0;\
}
#define tsh 6
#define typs(x,y) ((x << tsh) | y)
#define typ1(x) (x >> tsh)
#define typ2(x) (x & ((1<<tsh)-1))

static long
poltype(GEN x, GEN *ptp, GEN *ptpol, long *ptpa)
{
  long t[LT]; /* code pour 0,1,2,3,61,62,63,67,7,81,82,83,86,87,91,93,97 */
  long tx = typ(x),lx,i,j,s,pa=BIGINT;
  GEN pcx=NULL, p=NULL,pol=NULL,p1,p2;

  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD) return 0;
    x = scalarpol(x,0);
  }
  for (i=2; i<LT; i++) t[i]=0; /* t[0..1] unused */
  lx = lgef(x);
  for (i=2; i<lx; i++)
  {
    p1=(GEN)x[i];
    switch(typ(p1))
    {
      case t_INT: case t_FRAC: case t_FRACN:
        break;
      case t_REAL:
        s = precision(p1); if (s < pa) pa = s;
        t[2]=1; break;
      case t_INTMOD:
	assign_or_fail((GEN)p1[1],p);
        t[3]=1; break;
      case t_COMPLEX:
        if (!pcx)
        {
          pcx = cgetg(5,t_POL); /* x^2 + 1 */
          pcx[1] = evalsigne(1)|evalvarn(0)|m_evallgef(5),
          pcx[2]=pcx[4]=un; pcx[3]=zero;
        }
	for (j=1; j<=2; j++)
	{
	  p2 = (GEN)p1[j];
	  switch(typ(p2))
	  {
	    case t_INT: case t_FRAC: case t_FRACN:
	      assign_or_fail(pcx,pol);
	      t[4]=1; break;
	    case t_REAL:
              s = precision(p2); if (s < pa) pa = s;
	      t[5]=1; break;
	    case t_INTMOD:
	      assign_or_fail((GEN)p2[1],p);
	      assign_or_fail(pcx,pol);
	      t[6]=1; break;
	    case t_PADIC:
	      s = precp(p2) + valp(p2); if (s < pa) pa = s;
	      assign_or_fail((GEN)p2[2],p);
	      assign_or_fail(pcx,pol);
	      t[7]=1; break;
	    default: return 0;
	  }
	}
	break;
      case t_PADIC:
        s = precp(p1) + valp(p1); if (s < pa) pa = s;
	assign_or_fail((GEN)p1[2],p);
        t[8]=1; break;
      case t_QUAD:
	for (j=2; j<=3; j++)
	{
	  p2 = (GEN)p1[j];
	  switch(typ(p2))
	  {
	    case t_INT: case t_FRAC: case t_FRACN:
	      assign_or_fail((GEN)p1[1],pol);
	      t[9]=1; break;
	    case t_REAL:
	      s = precision(p2); if (s < pa) pa = s;
	      if (gsigne(discsr((GEN)p1[1]))>0) t[10]=1; else t[12]=1;
	      break;
	    case t_INTMOD:
	      assign_or_fail((GEN)p2[1],p);
	      assign_or_fail((GEN)p1[1],pol);
	      t[11]=1; break;
	    case t_PADIC:
	      s = precp(p2) + valp(p2); if (s < pa) pa = s;
	      assign_or_fail((GEN)p2[2],p);
	      assign_or_fail((GEN)p1[1],pol);
	      t[13]=1; break;
	    default: return 0;
	  }
	}
	break;
      case t_POLMOD:
	assign_or_fail((GEN)p1[1],pol);
	for (j=1; j<=2; j++)
	{
	  GEN pbis = NULL, polbis = NULL;
	  long pabis;
	  switch(poltype((GEN)p1[j],&pbis,&polbis,&pabis))
	  {
	    case t_INT: t[14]=1; break;
	    case t_INTMOD: t[15]=1; break;
	    case t_PADIC: t[16]=1; if (pabis<pa) pa=pabis; break;
	    default: return 0;
	  }
	  if (pbis) assign_or_fail(pbis,p);
	  if (polbis) assign_or_fail(polbis,pol);
	}
	break;
      default: return 0;
    }
  }
  if (t[5]||t[12])
  {
    if (t[3]||t[6]||t[7]||t[8]||t[11]||t[13]||t[14]||t[15]||t[16]) return 0;
    *ptpa=pa; return t_COMPLEX;
  }
  if (t[2]||t[10])
  {
    if (t[3]||t[6]||t[7]||t[8]||t[11]||t[13]||t[14]||t[15]||t[16]) return 0;
    *ptpa=pa; return t[4]?t_COMPLEX:t_REAL;
  }
  if (t[6]||t[11]||t[15])
  {
    *ptpol=pol; *ptp=p;
    i = t[15]? t_POLMOD: (t[11]? t_QUAD: t_COMPLEX);
    return typs(i, t_INTMOD);
  }
  if (t[7]||t[13]||t[16])
  {
    *ptpol=pol; *ptp=p; *ptpa=pa;
    i = t[16]? t_POLMOD: (t[13]? t_QUAD: t_COMPLEX);
    return typs(i, t_PADIC);
  }
  if (t[4]||t[9]||t[14])
  {
    *ptpol=pol;
    i = t[14]? t_POLMOD: (t[9]? t_QUAD: t_COMPLEX);
    return typs(i, t_INT);
  }
  if (t[3]) { *ptp=p; return t_INTMOD; }
  if (t[8]) { *ptp=p; *ptpa=pa; return t_PADIC; }
  return t_INT;
}
#undef LT

GEN
factor0(GEN x,long flag)
{
  long tx=typ(x);

  if (flag<0) return factor(x);
  if (is_matvec_t(tx)) return gboundfact(x,flag);
  if (tx==t_INT || tx==t_FRAC || tx==t_FRACN) return boundfact(x,flag);
  err(talker,"partial factorization is not meaningful here");
  return NULL; /* not reached */
}

static GEN
poldeg1(long v, GEN x0, GEN x1)
{
  GEN x = cgetg(4,t_POL);
  x[1] = evalsigne(1) | evalvarn(v) | evallgef(4);
  x[2] = (long)x0; x[3] = (long)x1; return normalizepol(x);
}

/* assume f and g coprime integer factorizations */
GEN
merge_factor_i(GEN f, GEN g)
{
  GEN h = cgetg(3,t_MAT);
  if (lg(f) == 1) return g;
  if (lg(g) == 1) return f;
  h[1] = (long)concatsp((GEN)f[1], (GEN)g[1]);
  h[2] = (long)concatsp((GEN)f[2], (GEN)g[2]);
  return sort_factor_gen(h, cmpii);
}

GEN
factor(GEN x)
{
  long tx=typ(x),lx,av,tetpil,i,j,pa,v,r1;
  GEN  y,p,p1,p2,p3,p4,p5,pol;

  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i]=(long)factor((GEN)x[i]);
    return y;
  }
  if (gcmp0(x))
  {
    y=cgetg(3,t_MAT);
    p1=cgetg(2,t_COL); y[1]=(long)p1; p1[1]=lcopy(x);
    p2=cgetg(2,t_COL); y[2]=(long)p2; p2[1]=un;
    return y;
  }
  av = avma;
  switch(tx)
  {
    case t_INT: return decomp(x);

    case t_FRACN:
      x = gred(x); /* fall through */
    case t_FRAC:
      p1 = decomp((GEN)x[1]);
      p2 = decomp((GEN)x[2]); p2[2] = (long)gneg_i((GEN)p2[2]);
      return gerepileupto(av, gcopy(merge_factor_i(p1,p2)));

    case t_POL:
      tx=poltype(x,&p,&pol,&pa);
      switch(tx)
      {
        case 0: err(impl,"factor for general polynomials");
	case t_INT: return factpol(x,0,1);
	case t_INTMOD: return factmod(x,p);

	case t_COMPLEX: y=cgetg(3,t_MAT); lx=lgef(x)-2; v=varn(x);
	  p1=roots(x,pa); tetpil=avma;
          p2=cgetg(lx,t_COL);
	  for (i=1; i<lx; i++)
            p2[i] = (long)poldeg1(v, gneg((GEN)p1[i]), gun);
	  y[1]=lpile(av,tetpil,p2);
	  p3=cgetg(lx,t_COL); for (i=1; i<lx; i++) p3[i] = un;
          y[2]=(long)p3; return y;

	case t_REAL: y=cgetg(3,t_MAT); lx=lgef(x)-2; v=varn(x);
	  av=avma; p1=roots(x,pa); tetpil=avma;
	  for(r1=1; r1<lx; r1++)
            if (signe(gmael(p1,r1,2))) break;
	  lx=(r1+lx)>>1; p2=cgetg(lx,t_COL);
	  for(i=1; i<r1; i++)
            p2[i] = (long)poldeg1(v, negr(gmael(p1,i,1)), gun);
	  for(   ; i<lx; i++)
	  {
	    GEN a = (GEN) p1[2*i-r1];
	    p = cgetg(5, t_POL); p2[i] = (long)p;
	    p[1] = evalsigne(1) | evalvarn(v) | evallgef(5);
	    p[2] = lnorm(a);
	    p[3] = lmul2n((GEN)a[1],1); setsigne(p[3],-signe(p[3]));
	    p[4] = un;
	  }
	  y[1]=lpile(av,tetpil,p2);
	  p3=cgetg(lx,t_COL); for (i=1; i<lx; i++) p3[i] = un;
          y[2]=(long)p3; return y;

	case t_PADIC: return factorpadic4(x,p,pa);

        default:
        {
          long killv;
	  x = dummycopy(x); lx=lgef(x);
          pol = dummycopy(pol);
          v = manage_var(4,NULL);
          for(i=2; i<lx; i++)
          {
            p1=(GEN)x[i];
            switch(typ(p1))
            {
              case t_QUAD: p1++;
              case t_COMPLEX:
                p2 = cgetg(3, t_POLMOD); x[i] = (long) p2;
                p2[1] = (long)pol;
                p2[2] = (long)poldeg1(v, (GEN)p1[1],(GEN)p1[2]);
            }
          }
          killv = (avma != (long)pol);
          if (killv) setvarn(pol, fetch_var());
          switch (typ2(tx))
          {
            case t_INT: p1 = polfnf(x,pol); break;
            case t_INTMOD: p1 = factmod9(x,p,pol); break;
	    default: err(impl,"factor of general polynomial");
              return NULL; /* not reached */
          }
          switch (typ1(tx))
          {
            case t_POLMOD:
              if (killv) delete_var();
              return gerepileupto(av,p1);
            case t_COMPLEX: p5 = gi; break;
            case t_QUAD: p5=cgetg(4,t_QUAD);
              p5[1]=(long)pol; p5[2]=zero; p5[3]=un;
              break;
	    default: err(impl,"factor of general polynomial");
              return NULL; /* not reached */
          }
          p2=(GEN)p1[1];
          for(i=1; i<lg(p2); i++)
          {
            p3=(GEN)p2[i];
            for(j=2; j<lgef(p3); j++)
            {
              p4=(GEN)p3[j];
              if(typ(p4)==t_POLMOD) p3[j]=lsubst((GEN)p4[2],v,p5);
            }
          }
          if (killv) delete_var();
          tetpil=avma; y=cgetg(3,t_MAT);
          y[1]=lcopy(p2);y[2]=lcopy((GEN)p1[2]);
          return gerepile(av,tetpil,y);
        }
      }

    case t_RFRACN:
      x=gred_rfrac(x); /* fall through */
    case t_RFRAC:
      p1=factor((GEN)x[1]);
      p2=factor((GEN)x[2]); p3=gneg_i((GEN)p2[2]);
      tetpil=avma; y=cgetg(3,t_MAT);
      y[1]=lconcat((GEN)p1[1],(GEN)p2[1]);
      y[2]=lconcat((GEN)p1[2],p3);
      return gerepile(av,tetpil,y);
  }
  err(talker,"can't factor %Z",x);
  return NULL; /* not reached */
}
#undef typ1
#undef typ2
#undef typs
#undef tsh

GEN
divide_conquer_prod(GEN x, GEN (*mul)(GEN,GEN))
{
  long i,k,lx = lg(x);

  if (lx == 1) return gun;
  if (lx == 2) return gcopy((GEN)x[1]);
  x = dummycopy(x); k = lx;
  while (k > 2)
  {
    if (DEBUGLEVEL>7)
      fprintferr("prod: remaining objects %ld\n",k-1);
    lx = k; k = 1;
    for (i=1; i<lx-1; i+=2)
      x[k++] = (long)mul((GEN)x[i],(GEN)x[i+1]);
    if (i < lx) x[k++] = x[i];
  }
  return (GEN)x[1];
}

static GEN static_nf;

static GEN
myidealmulred(GEN x, GEN y) { return idealmulred(static_nf, x, y, 0); }

static GEN
myidealpowred(GEN x, GEN n) { return idealpowred(static_nf, x, n, 0); }

static GEN
myidealmul(GEN x, GEN y) { return idealmul(static_nf, x, y); }

static GEN
myidealpow(GEN x, GEN n) { return idealpow(static_nf, x, n); }

GEN
factorback_i(GEN fa, GEN nf, int red)
{
  long av=avma,k,l,lx;
  GEN ex, x;
  GEN (*_mul)(GEN,GEN);
  GEN (*_pow)(GEN,GEN);

  if (typ(fa)!=t_MAT || lg(fa)!=3)
    err(talker,"not a factorisation in factorback");
  ex=(GEN)fa[2]; fa=(GEN)fa[1];
  lx = lg(fa); if (lx == 1) return gun;
  x = cgetg(lx,t_VEC);
  if (nf)
  {
    static_nf = nf;
    if (red)
    {
      _mul = &myidealmulred;
      _pow = &myidealpowred;
    }
    else
    {
      _mul = &myidealmul;
      _pow = &myidealpow;
    }
  }
  else
  {
    _mul = &gmul;
    _pow = &powgi;
  }
  for (l=1,k=1; k<lx; k++)
    if (signe(ex[k]))
      x[l++] = (long)_pow((GEN)fa[k],(GEN)ex[k]);
  setlg(x,l);
  return gerepileupto(av, divide_conquer_prod(x, _mul));
}

GEN
factorback(GEN fa, GEN nf)
{
  return factorback_i(fa,nf,0);
}

GEN
gisirreducible(GEN x)
{
  long av=avma, tx = typ(x),l,i;
  GEN y;

  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i]=(long)gisirreducible((GEN)x[i]);
    return y;
  }
  if (is_intreal_t(tx) || is_frac_t(tx)) return gzero;
  if (tx!=t_POL) err(notpoler,"gisirreducible");
  l=lgef(x); if (l<=3) return gzero;
  y=factor(x); avma=av;
  return (lgef(gcoeff(y,1,1))==l)?gun:gzero;
}

/*******************************************************************/
/*                                                                 */
/*                         PGCD GENERAL                            */
/*                                                                 */
/*******************************************************************/

GEN
gcd0(GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 0: return ggcd(x,y);
    case 1: return modulargcd(x,y);
    case 2: return srgcd(x,y);
    default: err(flagerr,"gcd");
  }
  return NULL; /* not reached */
}

/* x is a COMPLEX or a QUAD */
static GEN
triv_cont_gcd(GEN x, GEN y)
{
  long av = avma, tetpil;
  GEN p1 = (typ(x)==t_COMPLEX)? ggcd((GEN)x[1],(GEN)x[2])
                              : ggcd((GEN)x[2],(GEN)x[3]);
  tetpil=avma; return gerepile(av,tetpil,ggcd(p1,y));
}

static GEN
cont_gcd(GEN x, GEN y)
{
  long av = avma, tetpil;
  GEN p1 = content(x);

  tetpil=avma; return gerepile(av,tetpil,ggcd(p1,y));
}

/* y is a PADIC, x a rational number or an INTMOD */
static GEN
padic_gcd(GEN x, GEN y)
{
  long v = ggval(x,(GEN)y[2]), w = valp(y);
  if (w < v) v = w;
  return gpuigs((GEN)y[2], v);
}

#define fix_frac(z) if (signe(z[2])<0)\
{\
  setsigne(z[1],-signe(z[1]));\
  setsigne(z[2],1);\
}

GEN
ggcd(GEN x, GEN y)
{
  long l,av,tetpil,i,vx,vy, tx = typ(x), ty = typ(y);
  GEN p1,z;

  if (tx>ty) { p1=x; x=y; y=p1; l=tx; tx=ty; ty=l; }
  if (is_matvec_t(ty))
  {
    l=lg(y); z=cgetg(l,ty);
    for (i=1; i<l; i++) z[i]=lgcd(x,(GEN)y[i]);
    return z;
  }
  if (is_noncalc_t(tx) || is_noncalc_t(ty)) err(operf,"g",tx,ty);
  if (gcmp0(x)) return gcopy(y);
  if (gcmp0(y)) return gcopy(x);
  if (is_const_t(tx))
  {
    if (ty == t_FRACN)
    {
      if (tx==t_INTMOD)
      {
        av=avma; y = gred(y); tetpil=avma;
        return gerepile(av,tetpil,ggcd(x,y));
      }
      ty = t_FRAC;
    }
    if (tx == t_FRACN) tx = t_FRAC;
    if (ty == tx) switch(tx)
    {
      case t_INT:
        return mppgcd(x,y);

      case t_INTMOD: z=cgetg(3,t_INTMOD);
        if (egalii((GEN)x[1],(GEN)y[1]))
          { copyifstack(x[1],z[1]); }
        else
          z[1]=lmppgcd((GEN)x[1],(GEN)y[1]);
        if (gcmp1((GEN)z[1])) z[2]=zero;
        else
        {
          av=avma; p1=mppgcd((GEN)z[1],(GEN)x[2]);
          if (!gcmp1(p1))
          {
            tetpil=avma;
            p1=gerepile(av,tetpil,mppgcd(p1,(GEN)y[2]));
          }
          z[2]=(long)p1;
        }
        return z;

      case t_FRAC: z=cgetg(3,t_FRAC);
        z[1] = (long)mppgcd((GEN)x[1], (GEN)y[1]);
        z[2] = (long)mpppcm((GEN)x[2], (GEN)y[2]);
        return z;

      case t_COMPLEX:
        av=avma; p1=gdiv(x,y);
        if (gcmp0((GEN)p1[2]))
        {
          p1=(GEN)p1[1];
          switch(typ(p1))
          {
            case t_INT:
              avma=av; return gcopy(y);
            case t_FRAC: case t_FRACN:
              tetpil=avma; return gerepile(av,tetpil,gdiv(y,(GEN)p1[2]));
            default: avma=av; return gun;
          }
        }
        avma=av;
        if (typ(p1[1])==t_INT && typ(p1[2])==t_INT) return gcopy(y);
        p1=gdiv(y,x); avma=av;
        if (typ(p1[1])==t_INT && typ(p1[2])==t_INT) return gcopy(x);
        return triv_cont_gcd(y,x);

      case t_PADIC:
        if (!egalii((GEN)x[2],(GEN)y[2])) return gun;
        return gpuigs((GEN)y[2],min(valp(y),valp(x)));

      case t_QUAD:
        av=avma; p1=gdiv(x,y);
        if (gcmp0((GEN)p1[3]))
        {
          p1=(GEN)p1[2];
          if (typ(p1)==t_INT) { avma=av; return gcopy(y); }
          tetpil=avma; return gerepile(av,tetpil, gdiv(y,(GEN)p1[2]));
        }
        avma=av;
        if (typ(p1[2])==t_INT && typ(p1[3])==t_INT) return gcopy(y);
        p1=gdiv(y,x); avma=av;
        if (typ(p1[2])==t_INT && typ(p1[3])==t_INT) return gcopy(x);
        return triv_cont_gcd(y,x);

      default: return gun; /* t_REAL */
    }
    if (is_const_t(ty)) switch(tx)
    {
      case t_INT:
        switch(ty)
        {
          case t_INTMOD: z=cgetg(3,t_INTMOD);
            copyifstack(y[1],z[1]); av=avma;
            p1=mppgcd((GEN)y[1],(GEN)y[2]);
            if (!gcmp1(p1))
              { tetpil=avma; p1=gerepile(av,tetpil,mppgcd(x,p1)); }
            z[2]=(long)p1; return z;

          case t_FRAC: z=cgetg(3,t_FRAC);
            z[1]=lmppgcd(x,(GEN)y[1]);
            z[2]=licopy((GEN)y[2]); return z;

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);

          default: /* t_REAL */
            return gun;
        }

      case t_INTMOD:
        switch(ty)
        {
          case t_FRAC:
            av=avma; p1=mppgcd((GEN)x[1],(GEN)y[2]); tetpil=avma;
            if (!gcmp1(p1)) err(operi,"g",tx,ty);
            return gerepile(av,tetpil, ggcd((GEN)y[1],x));

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);
        }

      case t_FRAC:
        switch(ty)
        {
          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);
        }

      case t_COMPLEX: /* ty = PADIC or QUAD */
        return triv_cont_gcd(x,y);

      case t_PADIC: /* ty = QUAD */
        return triv_cont_gcd(y,x);

      default: /* tx = t_REAL */
        return gun;
    }
    return cont_gcd(y,x);
  }

  vx=gvar9(x); vy=gvar9(y);
  if (vy<vx) return cont_gcd(y,x);
  if (vx<vy) return cont_gcd(x,y);
  switch(tx)
  {
    case t_POLMOD:
      switch(ty)
      {
	case t_POLMOD: z=cgetg(3,t_POLMOD);
          if (gegal((GEN)x[1],(GEN)y[1]))
	    { copyifstack(x[1],z[1]); }
          else
            z[1] = lgcd((GEN)x[1],(GEN)y[1]);
	  if (lgef(z[1])<=3) z[2]=zero;
	  else
	  {
	    av=avma; p1=ggcd((GEN)z[1],(GEN)x[2]);
	    if (lgef(p1)>3)
	    {
	      tetpil=avma;
              p1=gerepile(av,tetpil,ggcd(p1,(GEN)y[2]));
	    }
	    z[2]=(long)p1;
	  }
	  return z;

	case t_POL: z=cgetg(3,t_POLMOD);
          copyifstack(x[1],z[1]); av=avma;
          p1=ggcd((GEN)x[1],(GEN)x[2]);
	  if (lgef(p1)>3)
            { tetpil=avma; p1=gerepile(av,tetpil,ggcd(y,p1)); }
	  z[2]=(long)p1; return z;

	case t_RFRAC:
	  av=avma; p1=ggcd((GEN)x[1],(GEN)y[2]); tetpil=avma;
          if (!gcmp1(p1)) err(operi,"g",tx,ty);
	  return gerepile(av,tetpil,ggcd((GEN)y[1],x));

	case t_RFRACN:
	  av=avma; p1=gred_rfrac(y); tetpil=avma;
	  return gerepile(av,tetpil,ggcd(p1,x));
      }
      break;

    case t_POL:
      switch(ty)
      {
	case t_POL:
	  return srgcd(x,y);

	case t_SER:
	  return gpuigs(polx[vx],min(valp(y),gval(x,vx)));

	case t_RFRAC: case t_RFRACN: av=avma; z=cgetg(3,ty);
          z[1]=lgcd(x,(GEN)y[1]);
          z[2]=lcopy((GEN)y[2]); return z;
      }
      break;

    case t_SER:
      switch(ty)
      {
	case t_SER:
	  return gpuigs(polx[vx],min(valp(x),valp(y)));

	case t_RFRAC: case t_RFRACN:
	  return gpuigs(polx[vx],min(valp(x),gval(y,vx)));
      }
      break;

    case t_RFRAC: case t_RFRACN: z=cgetg(3,ty);
      if (!is_rfrac_t(ty)) err(operf,"g",tx,ty);
      p1 = gdiv((GEN)y[2], ggcd((GEN)x[2], (GEN)y[2]));
      tetpil = avma;
      z[2] = lpile((long)z,tetpil,gmul(p1, (GEN)x[2]));
      z[1] = lgcd((GEN)x[1], (GEN)y[1]); return z;
  }
  err(operf,"g",tx,ty);
  return NULL; /* not reached */
}

GEN
glcm(GEN x, GEN y)
{
  long av,tx,ty,i,l;
  GEN p1,p2,z;

  ty = typ(y);
  if (is_matvec_t(ty))
  {
    l=lg(y); z=cgetg(l,ty);
    for (i=1; i<l; i++) z[i]=(long)glcm(x,(GEN)y[i]);
    return z;
  }
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    l=lg(x); z=cgetg(l,tx);
    for (i=1; i<l; i++) z[i]=(long)glcm((GEN)x[i],y);
    return z;
  }
  if (tx==t_INT && ty==t_INT) return mpppcm(x,y);
  if (gcmp0(x)) return gzero;

  av = avma;
  p1 = ggcd(x,y); if (!gcmp1(p1)) y = gdiv(y,p1);
  p2 = gmul(x,y);
  switch(typ(p2))
  {
    case t_INT: if (signe(p2)<0) setsigne(p2,1);
      break;
    case t_POL:
      if (lgef(p2) <= 2) break;
      p1=leading_term(p2);
      if (typ(p1)==t_INT && signe(p1)<0) p2=gneg(p2);
  }
  return gerepileupto(av,p2);
}

static GEN
polgcdnun(GEN x, GEN y)
{
  long av1, av = avma, lim = stack_lim(av,1);
  GEN p1, yorig = y;

  for(;;)
  {
    av1 = avma; p1 = gres(x,y);
    if (gcmp0(p1))
    {
      avma = av1;
      return (y==yorig)? gcopy(y): gerepileupto(av,y);
    }
    x = y; y = p1;
    if (low_stack(lim,stack_lim(av,1)))
    {
      GEN *gptr[2]; x = gcopy(x); gptr[0]=&x; gptr[1]=&y;
      if(DEBUGMEM>1) err(warnmem,"polgcdnun");
      gerepilemanysp(av,av1,gptr,2);
    }
  }
}

/* return 1 if coeff explosion is not possible */
static int
issimplefield(GEN x)
{
  long lx,i;
  switch(typ(x))
  {
    case t_REAL: case t_INTMOD: case t_PADIC: case t_SER:
      return 1;
    case t_POL:
      lx=lgef(x);
      for (i=2; i<lx; i++)
	if (issimplefield((GEN)x[i])) return 1;
      return 0;
    case t_COMPLEX: case t_POLMOD:
      return issimplefield((GEN)x[1]) || issimplefield((GEN)x[2]);
  }
  return 0;
}

static int
isrational(GEN x)
{
  long i;
  for (i=lgef(x)-1; i>1; i--)
    switch(typ(x[i]))
    {
      case t_INT:
      case t_FRAC: break;
      default: return 0;
    }
  return 1;
}

static int
isinexactfield(GEN x)
{
  long lx,i;
  switch(typ(x))
  {
    case t_REAL: case t_PADIC: case t_SER:
      return 1;
    case t_POL:
      lx=lgef(x); if (lx == 2) return 0;/*true 0 polynomial*/
      for (i=2; i<lx; i++)
	if (isinexactfield((GEN)x[i])) return 1;
      return 0;
    case t_COMPLEX: case t_POLMOD:
      return isinexactfield((GEN)x[1]) || isinexactfield((GEN)x[2]);
  }
  return 0;
}

static GEN
gcdmonome(GEN x, GEN y)
{
  long tetpil,av=avma, lx=lgef(x), v=varn(x), e=gval(y,v);
  GEN p1,p2;

  if (lx-3<e) e=lx-3;
  p1=ggcd(leading_term(x),content(y)); p2=gpuigs(polx[v],e);
  tetpil=avma; return gerepile(av,tetpil,gmul(p1,p2));
}

/***********************************************************************/
/**                                                                   **/
/**                         BEZOUT GENERAL                            **/
/**                                                                   **/
/***********************************************************************/

static GEN
polinvinexact(GEN x, GEN y)
{
  long i,dx=lgef(x)-3,dy=lgef(y)-3,lz=dx+dy, av=avma, tetpil;
  GEN v,z;

  if (dx < 0 || dy < 0) err(talker,"non-invertible polynomial in polinvmod");
  z=cgetg(dy+2,t_POL); z[1]=y[1];
  v=cgetg(lz+1,t_COL);
  for (i=1; i<lz; i++) v[i]=zero;
  v[lz]=un; v=gauss(sylvestermatrix(y,x),v);
  for (i=2; i<dy+2; i++) z[i]=v[lz-i+2];
  z = normalizepol_i(z, dy+2); tetpil = avma;
  return gerepile(av,tetpil,gcopy(z));
}

static GEN
polinvmod(GEN x, GEN y)
{
  long av,av1,tx,vx=varn(x),vy=varn(y);
  GEN u,v,d,p1;

  while (vx!=vy)
  {
    if (vx > vy)
    {
      d=cgetg(3,t_RFRAC);
      d[1]=(long)polun[vx];
      d[2]=lcopy(x); return d;
    }
    if (lgef(x)!=3) err(talker,"non-invertible polynomial in polinvmod");
    x=(GEN)x[2]; vx=gvar(x);
  }
  tx=typ(x);
  if (tx==t_POL)
  {
    if (isinexactfield(x) || isinexactfield(y))
      return polinvinexact(x,y);

    av=avma; d=subresext(x,y,&u,&v);
    if (gcmp0(d)) err(talker,"non-invertible polynomial in polinvmod");
    if (typ(d)==t_POL && varn(d)==vx)
    {
      if (lgef(d)>3) err(talker,"non-invertible polynomial in polinvmod");
      d=(GEN)d[2];
    }
    av1=avma; return gerepile(av,av1,gdiv(u,d));
  }
  if (!is_rfrac_t(tx)) err(typeer,"polinvmod");
  av=avma; p1=gmul((GEN)x[1],polinvmod((GEN)x[2],y));
  av1=avma; return gerepile(av,av1,gmod(p1,y));
}

GEN
gbezout(GEN x, GEN y, GEN *u, GEN *v)
{
  long tx=typ(x),ty=typ(y);

  if (tx==t_INT && ty==t_INT) return bezout(x,y,u,v);
  if (!is_extscalar_t(tx) || !is_extscalar_t(ty)) err(typeer,"gbezout");
  return bezoutpol(x,y,u,v);
}

GEN
vecbezout(GEN x, GEN y)
{
  GEN z=cgetg(4,t_VEC);
  z[3]=(long)gbezout(x,y,(GEN*)(z+1),(GEN*)(z+2));
  return z;
}

GEN
vecbezoutres(GEN x, GEN y)
{
  GEN z=cgetg(4,t_VEC);
  z[3]=(long)subresext(x,y,(GEN*)(z+1),(GEN*)(z+2));
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                    CONTENU ET PARTIE PRIMITIVE                  */
/*                                                                 */
/*******************************************************************/

GEN
content(GEN x)
{
  long av,tetpil,lx,i,tx=typ(x);
  GEN p1,p2;

  if (is_scalar_t(tx))
    return tx==t_POLMOD? content((GEN)x[2]): gcopy(x);
  av = avma;
  switch(tx)
  {
    case t_RFRAC: case t_RFRACN:
      p1=content((GEN)x[1]);
      p2=content((GEN)x[2]); tetpil=avma;
      return gerepile(av,tetpil,gdiv(p1,p2));

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); if (lx==1) return gun;
      p1=content((GEN)x[1]);
      for (i=2; i<lx; i++) p1 = ggcd(p1,content((GEN)x[i]));
      return gerepileupto(av,p1);

    case t_POL:
      if (!signe(x)) return gzero;
      lx = lgef(x); break;
    case t_SER:
      if (!signe(x)) return gzero;
      lx = lg(x); break;
    case t_QFR: case t_QFI:
      lx = 4; break;

    default: err(typeer,"content");
      return NULL; /* not reached */
  }
  for (i=lontyp[tx]; i<lx; i++)
    if (typ(x[i]) != t_INT) break;
  lx--; p1=(GEN)x[lx];
  if (i > lx)
  { /* integer coeffs */
    while (lx>lontyp[tx])
    {
      lx--; p1=mppgcd(p1,(GEN)x[lx]);
      if (is_pm1(p1)) { avma=av; return gun; }
    }
  }
  else
  {
    while (lx>lontyp[tx])
    {
      lx--; p1=ggcd(p1,(GEN)x[lx]);
    }
    if (isinexactreal(p1)) { avma=av; return gun; }
  }
  return av==avma? gcopy(p1): gerepileupto(av,p1);
}

/*******************************************************************/
/*                                                                 */
/*                         SOUS RESULTANT                          */
/*                                                                 */
/*******************************************************************/
/* for internal use */
GEN
gdivexact(GEN x, GEN y)
{
  long i,lx;
  GEN z;
  if (gcmp1(y)) return x;
  switch(typ(x))
  {
    case t_INT:
      if (typ(y)==t_INT) return divii(x,y);
      if (!signe(x)) return gzero;
      break;
    case t_INTMOD:
    case t_POLMOD: return gmul(x,ginv(y));
    case t_POL:
      switch(typ(y))
      {
        case t_INTMOD:
        case t_POLMOD: return gmul(x,ginv(y));
        case t_POL:
          if (varn(x)==varn(y)) return poldivres(x,y, ONLY_DIVIDES_EXACT);
      }
      lx = lgef(x); z = cgetg(lx,t_POL);
      for (i=2; i<lx; i++) z[i]=(long)gdivexact((GEN)x[i],y);
      z[1]=x[1]; return z;
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx, typ(x));
      for (i=1; i<lx; i++) z[i]=(long)gdivexact((GEN)x[i],y);
      return z;
  }
  if (DEBUGLEVEL) err(warner,"missing case in gdivexact");
  return gdiv(x,y);
}

static GEN
init_resultant(GEN x, GEN y)
{
  long tx,ty;
  if (gcmp0(x) || gcmp0(y)) return gzero;
  tx = typ(x); ty = typ(y);
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return gpuigs(y,lgef(x)-3);
    if (ty==t_POL) return gpuigs(x,lgef(y)-3);
    return gun;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"subresall");
  if (varn(x)==varn(y)) return NULL;
  return (varn(x)<varn(y))? gpuigs(y,lgef(x)-3): gpuigs(x,lgef(y)-3);
}

/* return coefficients s.t x = x_0 X^n + ... + x_n */
static GEN 
revpol(GEN x)
{
  long i,n = lgef(x)-3;
  GEN y = cgetg(n+3,t_POL);
  y[1] = x[1]; x += 2; y += 2;
  for (i=0; i<=n; i++) y[i] = x[n-i];
  return y;
}

/* assume dx >= dy, y non constant */
GEN
pseudorem(GEN x, GEN y)
{
  long av = avma, av2,lim, vx = varn(x),dx,dy,dz,i,lx, p;

  if (!signe(y)) err(talker,"euclidean division by zero (pseudorem)");
  (void)new_chunk(2);
  dx=lgef(x)-3; x = revpol(x);
  dy=lgef(y)-3; y = revpol(y); dz=dx-dy; p = dz+1;
  av2 = avma; lim = stack_lim(av2,1);
  for (;;)
  {
    x[0] = lneg((GEN)x[0]); p--;
    for (i=1; i<=dy; i++)
      x[i] = ladd(gmul((GEN)y[0], (GEN)x[i]), gmul((GEN)x[0],(GEN)y[i]));
    for (   ; i<=dx; i++)
      x[i] = lmul((GEN)y[0], (GEN)x[i]);
    do { x++; dx--; } while (dx >= 0 && gcmp0((GEN)x[0]));
    if (dx < dy) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pseudorem dx = %ld >= %ld",dx,dy);
      gerepilemanycoeffs(av2,x,dx+1);
    }
  }
  if (dx < 0) return zeropol(vx);
  lx = dx+3; x -= 2;
  x[0]=evaltyp(t_POL) | evallg(lx);
  x[1]=evalsigne(1) | evalvarn(vx) | evallgef(lx);
  x = revpol(x) - 2;
  return gerepileupto(av, gmul(x, gpowgs((GEN)y[0], p)));
}

/* Si sol != NULL:
 *   met dans *sol le dernier polynome non nul de la polynomial remainder
 *   sequence si elle a ete effectuee, 0 sinon
 */
GEN
subresall(GEN u, GEN v, GEN *sol)
{
  long degq,av,av2,lim,tetpil,dx,dy,du,dv,dr,signh;
  GEN g,h,r,p1,p2,p3,p4;

  if (sol) *sol=gzero;
  if ((r = init_resultant(u,v))) return r;

  if (isinexactfield(u) || isinexactfield(v)) return resultant2(u,v);
  dx=lgef(u); dy=lgef(v); signh=1;
  if (dx<dy)
  {
    p1=u; u=v; v=p1; du=dx; dx=dy; dy=du;
    if ((dx&1) == 0 && (dy&1) == 0) signh = -signh;
  }
  if (dy==3) return gpowgs((GEN)v[2],dx-3);
  av=avma;
  p3=content(u); if (gcmp1(p3)) p3=NULL; else u=gdiv(u,p3);
  p4=content(v); if (gcmp1(p4)) p4=NULL; else v=gdiv(v,p4);
  g=gun; h=gun; av2 = avma; lim = stack_lim(av2,1);
  for(;;)
  {
    r = pseudorem(u,v); dr = lgef(r);
    if (dr==2)
    {
      if (sol) {avma = (long)(r+2); *sol=gerepileupto(av,v);} else avma = av;
      return gzero;
    }
    du=lgef(u); dv=lgef(v);
    degq=du-dv; u=v;
    p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq),p1);
        h = gdivexact(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    if ((du&1) == 0 && (dv&1) == 0) signh = -signh;
    v = gdivexact(r,p1);
    if (dr==3) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      if(DEBUGMEM>1) err(warnmem,"subresall, dr = %ld",dr);
      gerepilemany(av2,gptr,4);
    }
  }
  if (dv==4) { tetpil=avma; p2=gcopy((GEN)v[2]); }
  else
  {
    if (dv == 3) err(bugparier,"subres");
    p1=gpuigs((GEN)v[2],dv-3); p2=gpuigs(h,dv-4);
    tetpil=avma; p2=gdiv(p1,p2);
  }
  if (p3) { p1=gpuigs(p3,dy-3); tetpil=avma; p2=gmul(p2,p1); }
  if (p4) { p1=gpuigs(p4,dx-3); tetpil=avma; p2=gmul(p2,p1); }
  if (signh<0) { tetpil=avma; p2=gneg(p2); }
  {
    GEN *gptr[2]; gptr[0]=&p2; if (sol) { *sol=gcopy(u); gptr[1]=sol; }
    gerepilemanysp(av,tetpil,gptr,sol?2:1);
    return p2;
  }
}

static GEN
scalar_res(GEN x, GEN y, GEN *U, GEN *V)
{
  long dx=lgef(x)-4;
  *V=gpuigs(y,dx); *U=gzero; return gmul(y,*V);
}

/* calcule U et V tel que Ux+By=resultant(x,y) */
GEN
subresext(GEN x, GEN y, GEN *U, GEN *V)
{
  long degq,av,tetpil,tx,ty,dx,dy,du,dv,dr,signh;
  GEN z,g,h,r,p1,p2,p3,p4,u,v,lpu,um1,uze, *gptr[2];

  if (gcmp0(x) || gcmp0(y)) { *U = *V = gzero; return gzero; }
  tx=typ(x); ty=typ(y);
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return scalar_res(x,y,U,V);
    if (ty==t_POL) return scalar_res(y,x,V,U);
    *U=ginv(x); *V=gzero; return gun;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"subresext");
  if (varn(x)!=varn(y))
    return (varn(x)<varn(y))? scalar_res(x,y,U,V)
                            : scalar_res(y,x,V,U);
  dx=lgef(x); dy=lgef(y); signh=1;
  if (dx<dy)
  {
    GEN *W = U; U=V; V=W;
    du=dx; dx=dy; dy=du; p1=x; x=y; y=p1;
    if ((dx&1) == 0 && (dy&1) == 0) signh = -signh;
  }
  if (dy==3)
  {
    *V=gpuigs((GEN)y[2],dx-4);
    *U=gzero; return gmul(*V,(GEN)y[2]);
  }
  av=avma;
  p3=content(x); if (gcmp1(p3)) {p3 = NULL; u=x; } else u=gdiv(x,p3);
  p4=content(y); if (gcmp1(p4)) {p4 = NULL; v=y; } else v=gdiv(y,p4);
  g=gun; h=gun; um1=gun; uze=gzero;
  for(;;)
  {
    du=lgef(u); dv=lgef(v); degq=du-dv;
    lpu=gpuigs((GEN)v[dv-1],degq+1);
    p1=gmul(lpu,u); p2=poldivres(p1,v,&r);
    dr=lgef(r); if (dr==2) { *U=gzero; *V=gzero; avma=av; return gzero; }

    p1=gsub(gmul(lpu,um1),gmul(p2,uze));
    um1=uze; uze=p1; u=v;
    p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1: p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq),p1);
        h = gdivexact(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    if ((du & 1) == 0 && (dv & 1) == 0) signh= -signh;
    v=gdivexact(r,p1); uze=gdivexact(uze,p1);
    if (dr==3) break;
  }

  p2=(dv==4)?gun:gpuigs(gdiv((GEN)v[2],h),dv-4);
  if (p3) p2 = gmul(p2,gpuigs(p3,dy-3));
  if (p4) p2 = gmul(p2,gpuigs(p4,dx-3));
  if (signh<0) p2=gneg_i(p2);
  p3 = p3? gdiv(p2,p3): p2;

  tetpil=avma; z=gmul((GEN)v[2],p2); uze=gmul(uze,p3);
  gptr[0]=&z; gptr[1]=&uze; gerepilemanysp(av,tetpil,gptr,2);

  av=avma; p1 = gadd(z, gneg(gmul(uze,x))); tetpil = avma;
  if (!poldivis(p1,y,&p1)) err(bugparier,"subresext");
  *U=uze; *V=gerepile(av,tetpil,p1); return z;
}

static GEN
scalar_bezout(GEN x, GEN y, GEN *U, GEN *V)
{
  *U=gzero; *V=ginv(y); return polun[varn(x)];
}

static GEN
zero_bezout(GEN y, GEN *U, GEN *V)
{
  GEN x=content(y);
  *U=gzero; *V = ginv(x); return gmul(y,*V);
}

/* calcule U et V tel que Ux+Vy=GCD(x,y) par le sous-resultant */
GEN
bezoutpol(GEN x, GEN y, GEN *U, GEN *V)
{
  long degq,av,tetpil,tx,ty,dx,dy,du,dv,dr;
  GEN g,h,r,p1,p2,p3,p4,u,v,lpu,um1,uze,vze,xprim,yprim;
  GEN *gptr[3];

  if (gcmp0(x)) return zero_bezout(y,U,V);
  if (gcmp0(y)) return zero_bezout(x,V,U);
  tx=typ(x); ty=typ(y); av=avma;
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return scalar_bezout(x,y,U,V);
    if (ty==t_POL) return scalar_bezout(y,x,V,U);
    *U=ginv(x); *V=gzero; return polun[0];
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"bezoutpol");
  if (varn(x)!=varn(y))
    return (varn(x)<varn(y))? scalar_bezout(x,y,U,V)
                            : scalar_bezout(y,x,V,U);
  dx=lgef(x); dy=lgef(y);
  if (dx<dy)
  {
    GEN *W=U; U=V; V=W;
    p1=x; x=y; y=p1; du=dx; dx=dy; dy=du;
  }
  if (dy==3) return scalar_bezout(x,y,U,V);

  p3=content(x); u=gdiv(x,p3);
  p4=content(y); v=gdiv(y,p4);
  xprim=u; yprim=v; g=gun; h=gun; um1=gun; uze=gzero;
  for(;;)
  {
    du=lgef(u); dv=lgef(v); degq=du-dv;
    lpu=gpuigs((GEN)v[dv-1],degq+1);
    p1=gmul(lpu,u); p2=poldivres(p1,v,&r);
    dr=lgef(r); if (dr<=2) break;
    p1=gsub(gmul(lpu,um1),gmul(p2,uze)); um1=uze; uze=p1;

    u=v; p1 = g; g  = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq), p1);
        h = gdiv(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    v=gdiv(r,p1); uze=gdiv(uze,p1);
    if (dr==3) break;
  }
  if (!poldivis(gsub(v,gmul(uze,xprim)),yprim, &vze))
    err(warner,"non-exact computation in bezoutpol");
  uze=gdiv(uze,p3); vze=gdiv(vze,p4); p1=ginv(content(v));

  tetpil=avma; uze=gmul(uze,p1); vze=gmul(vze,p1); p1=gmul(v,p1);
  gptr[0]=&uze; gptr[1]=&vze; gptr[2]=&p1;
  gerepilemanysp(av,tetpil,gptr,3);
  *U=uze; *V=vze; return p1;
}



/*******************************************************************/
/*                                                                 */
/*               RESULTANT PAR L'ALGORITHME DE DUCOS               */
/*                                                                 */
/*******************************************************************/
GEN addshiftw(GEN x, GEN y, long d);

static GEN
reductum(GEN P)
{
  if (signe(P)==0) return P;
  return normalizepol_i(dummycopy(P),lgef(P)-1);
}

static GEN
Lazard(GEN x, GEN y, long n)
{
  long a, b;
  GEN c;
  
  if (n<=1) return x;
  a=1; while (n >= (b=a+a)) a=b;
  c=x; n-=a;
  while (a>1)
  {
    a>>=1; c=gdivexact(gsqr(c),y);
    if (n>=a) { c=gdivexact(gmul(c,x),y); n -= a; }
  }
  return c;
}

static GEN
Lazard2(GEN F, GEN x, GEN y, long n)
{
  if (n<=1) return F;
  x = Lazard(x,y,n-1); return gdivexact(gmul(x,F),y);
}

static GEN
addshift(GEN x, GEN y)
{
  long v = varn(x);
  if (!signe(x)) return y;
  x = addshiftw(x,y,1);
  setvarn(x,v); return x;
}

static GEN
nextSousResultant(GEN P, GEN Q, GEN Z, GEN s)
{
  GEN p0, q0, z0, H, A;
  long p, q, j, av, lim, v = varn(P);

  z0 = leading_term(Z);
  p = degree(P); p0 = leading_term(P); P = reductum(P);
  q = degree(Q); q0 = leading_term(Q); Q = reductum(Q);

  av = avma; lim = stack_lim(av,1);
  H = gneg(reductum(Z));
  A = gmul((GEN)P[q+2],H);
  for (j = q+1; j < p; j++)
  {
    H = (degree(H) == q-1) ?
      addshift(reductum(H), gdivexact(gmul(gneg((GEN)H[q+1]),Q), q0)) :
      addshift(H, zeropol(v));
    A = gadd(A,gmul((GEN)P[j+2],H));
    if (low_stack(lim,stack_lim(av,1)))
    {
      GEN *gptr[2]; gptr[0]=&A; gptr[1]=&H;
      if(DEBUGMEM>1) err(warnmem,"nextSousResultant j = %ld/%ld",j,p);
      gerepilemany(av,gptr,2);
    }
  }
  P = normalizepol_i(P, q+2);
  A = gdivexact(gadd(A,gmul(z0,P)), p0);
  A = (degree(H) == q-1) ?
    gadd(gmul(q0,addshift(reductum(H),A)), gmul(gneg((GEN)H[q+1]),Q)) :
    gmul(q0, addshift(H,A));
  return gdivexact(A, ((p-q)&1)? s: gneg(s));
}

GEN
resultantducos(GEN P, GEN Q)
{
  long delta, av=avma, tetpil, lim = stack_lim(av,1);
  GEN Z, s;
  
  if ((Z = init_resultant(P,Q))) return Z;
  delta = degree(P) - degree(Q);
  if (delta < 0)
  {
    Z = ((degree(P)&1) && (degree(Q)&1)) ? gneg(Q) : Q;
    Q = P; P = Z; delta = -delta;
  }
  s = gun;
  if (degree(Q) > 0)
  {
    s = gpuigs(leading_term(Q),delta);
    Z = Q;
    Q = pseudorem(P, gneg(Q));
    P = Z;
    while(degree(Q) > 0)
    {
      if (low_stack(lim,stack_lim(av,1)))
      {
        GEN *gptr[2]; gptr[0]=&P; gptr[1]=&Q;
        if(DEBUGMEM>1) err(warnmem,"resultantducos, deg Q = %ld",degree(Q));
        gerepilemany(av,gptr,2); s = leading_term(P);
      }
      delta = degree(P) - degree(Q);
      Z = Lazard2(Q, leading_term(Q), s, delta);
      Q = nextSousResultant(P, Q, Z, s);
      P = Z;
      s = leading_term(P);
    }
  }
  if (!signe(Q)) { avma = av; return gzero; }
  if (!degree(P)){ avma = av; return gun; }
  s = Lazard(leading_term(Q), s, degree(P));
  tetpil = avma; return gerepile(av,tetpil,gcopy(s));
}

/*******************************************************************/
/*                                                                 */
/*               RESULTANT PAR MATRICE DE SYLVESTER                */
/*                                                                 */
/*******************************************************************/
static GEN
_zeropol(void)
{
  GEN x = cgetg(3,t_POL);
  x[1] = evallgef(3);
  x[2] = zero; return x;
}

static GEN
sylvester_col(GEN x, long j, long d, long D)
{
  GEN c = cgetg(d+1,t_COL);
  long i;
  for (i=1; i< j; i++) c[i]=zero;
  for (   ; i<=D; i++) c[i]=x[D-i+2];
  for (   ; i<=d; i++) c[i]=zero;
  return c;
}

GEN
sylvestermatrix_i(GEN x, GEN y)
{
  long j,d,dx,dy;
  GEN M;

  dx = lgef(x)-3; if (dx < 0) { dx = 0; x = _zeropol(); }
  dy = lgef(y)-3; if (dy < 0) { dy = 0; y = _zeropol(); }
  d = dx+dy; M = cgetg(d+1,t_MAT);
  for (j=1; j<=dy; j++) M[j]    = (long)sylvester_col(x,j,d,j+dx);
  for (j=1; j<=dx; j++) M[j+dy] = (long)sylvester_col(y,j,d,j+dy);
  return M;
}

GEN 
sylvestermatrix(GEN x, GEN y)
{
  long i,j,lx;
  if (typ(x)!=t_POL || typ(y)!=t_POL) err(typeer,"sylvestermatrix");
  if (varn(x) != varn(y))
    err(talker,"not the same variables in sylvestermatrix");
  x = sylvestermatrix_i(x,y); lx = lg(x);
  for (i=1; i<lx; i++)
    for (j=1; j<lx; j++) coeff(x,i,j) = lcopy(gcoeff(x,i,j));
  return x;
}

GEN
resultant2(GEN x, GEN y)
{
  long av;
  GEN r;
  if ((r = init_resultant(x,y))) return r;
  av = avma; return gerepileupto(av,det(sylvestermatrix_i(x,y)));
}

static GEN
fix_pol(GEN x, long v, long *mx)
{
  long vx;
  GEN p1;

  if (typ(x) == t_POL)
  {
    vx = varn(x);
    if (vx)
    {
      if (v>=vx) return gsubst(x,v,polx[0]);
      p1 = cgetg(3,t_POL);
      p1[1] = evalvarn(0)|evalsigne(signe(x))|evallgef(3);
      p1[2] = (long)x; return p1;
    }
    if (v)
    {
      *mx = 1;
      return gsubst(gsubst(x,0,polx[MAXVARN]),v,polx[0]);
    }
  }
  return x;
}

/* resultant of x and y with respect to variable v, or with respect to their
 * main variable if v < 0.
 */
GEN
polresultant0(GEN x, GEN y, long v, long flag)
{
  long av = avma, m = 0;

  if (v >= 0)
  {
    x = fix_pol(x,v, &m);
    y = fix_pol(y,v, &m);
  }
  switch(flag)
  {
    case 0: x=subresall(x,y,NULL); break;
    case 1: x=resultant2(x,y); break;
    case 2: x=resultantducos(x,y); break;
    default: err(flagerr,"polresultant");
  }
  if (m) x = gsubst(x,MAXVARN,polx[0]);
  return gerepileupto(av,x);
}

/*******************************************************************/
/*                                                                 */
/*           P.G.C.D PAR L'ALGORITHME DU SOUS RESULTANT            */
/*                                                                 */
/*******************************************************************/

GEN
srgcd(GEN x, GEN y)
{
  long av,av1,tetpil,tx=typ(x),ty=typ(y),dx,dy,vx,lim;
  GEN d,g,h,p1,p2,u,v;

  if (!signe(y)) return gcopy(x);
  if (!signe(x)) return gcopy(y);
  if (is_scalar_t(tx) || is_scalar_t(ty)) return gun;
  if (tx!=t_POL || ty!=t_POL) err(typeer,"srgcd");
  vx=varn(x); if (vx!=varn(y)) return gun;
  if (ismonome(x)) return gcdmonome(x,y);
  if (ismonome(y)) return gcdmonome(y,x);
  if (isrational(x) && isrational(y)) return modulargcd(x,y);

  av=avma;
  if (issimplefield(x) || issimplefield(y)) x = polgcdnun(x,y);
  else
  {
    dx=lgef(x); dy=lgef(y);
    if (dx<dy) { p1=x; x=y; y=p1; tx=dx; dx=dy; dy=tx; }
    p1=content(x); p2=content(y); d=ggcd(p1,p2);

    tetpil=avma; d=gmul(d,polun[vx]);
    if (dy==3) return gerepile(av,tetpil,d);

    av1=avma; lim=stack_lim(av1,1);
    u=gdiv(x,p1); v=gdiv(y,p2); g=h=gun;
    for(;;)
    {
      GEN r = pseudorem(u,v);
      long degq, du, dv, dr=lgef(r);

      if (dr<=3)
      {
        if (gcmp0(r)) break;
        avma=av1; return gerepile(av,tetpil,d);
      }
      if (DEBUGLEVEL > 9) fprintferr("srgcd: dr = %ld\n", dr);
      du=lgef(u); dv=lgef(v); degq=du-dv; u=v;
      switch(degq)
      {
        case 0:
          v = gdiv(r,g);
          g = leading_term(u);
          break;
        case 1:
          v = gdiv(r,gmul(h,g));
          h = g = leading_term(u);
          break;
        default:
          v = gdiv(r,gmul(gpuigs(h,degq),g));
          g = leading_term(u);
          h = gdiv(gpuigs(g,degq), gpuigs(h,degq-1));
      }
      if (low_stack(lim, stack_lim(av1,1)))
      {
        GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
        if(DEBUGMEM>1) err(warnmem,"srgcd");
        gerepilemany(av1,gptr,4);
      }
    }
    p1 = content(v); if (!gcmp1(p1)) v = gdiv(v,p1);
    x = gmul(d,v);
  }

  if (typ(x)!=t_POL) x = gmul(polun[vx],x);
  else
  {
    p1=leading_term(x); ty=typ(p1);
    if ((is_frac_t(ty) || is_intreal_t(ty)) && gsigne(p1)<0) x = gneg(x);
  }
  return gerepileupto(av,x);
}

extern GEN qf_disc(GEN x, GEN y, GEN z);

GEN
poldisc0(GEN x, long v)
{
  long av,tx=typ(x),i;
  GEN z,p1,p2;

  switch(tx)
  {
    case t_POL:
      if (gcmp0(x)) return gzero;
      av = avma; i = 0;
      if (v >= 0 && v != varn(x)) x = fix_pol(x,v, &i);
      p1 = subres(x, derivpol(x));
      p2 = leading_term(x); if (!gcmp1(p2)) p1 = gdiv(p1,p2);
      if ((lgef(x)-3) & 2) p1 = gneg(p1);
      if (i) p1 = gsubst(p1, MAXVARN, polx[0]);
      return gerepileupto(av,p1);

    case t_COMPLEX:
      return stoi(-4);

    case t_QUAD: case t_POLMOD:
      return poldisc0((GEN)x[1], v);

    case t_QFR: case t_QFI:
      av = avma; return gerepileuptoint(av, qf_disc(x,NULL,NULL));

    case t_VEC: case t_COL: case t_MAT:
      i=lg(x); z=cgetg(i,tx);
      for (i--; i; i--) z[i]=(long)poldisc0((GEN)x[i], v);
      return z;
  }
  err(typeer,"discsr");
  return NULL; /* not reached */
}

GEN
discsr(GEN x)
{
  return poldisc0(x, -1);
}

GEN
reduceddiscsmith(GEN pol)
{
  long av=avma,tetpil,i,j,n;
  GEN polp,alpha,p1,m;

  if (typ(pol)!=t_POL) err(typeer,"reduceddiscsmith");
  n=lgef(pol)-3;
  if (n<=0) err(constpoler,"reduceddiscsmith");
  check_pol_int(pol);
  if (!gcmp1((GEN)pol[n+2]))
    err(talker,"non-monic polynomial in poldiscreduced");
  polp = derivpol(pol); alpha = polx[varn(pol)];
  m=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1=cgetg(n+1,t_COL); m[j]=(long)p1;
    for (i=1; i<=n; i++) p1[i]=(long)truecoeff(polp,i-1);
    if (j<n) polp = gres(gmul(alpha,polp), pol);
  }
  tetpil=avma; return gerepile(av,tetpil,smith(m));
}

/***********************************************************************/
/**							              **/
/**	                 ALGORITHME DE STURM                          **/
/**	         (number of real roots of x in ]a,b])		      **/
/**								      **/
/***********************************************************************/

/* if a (resp. b) is NULL, set it to -oo (resp. +oo) */
long
sturmpart(GEN x, GEN a, GEN b)
{
  long av = avma, lim = stack_lim(av,1), sl,sr,s,t,r1;
  GEN g,h,u,v;

  if (typ(x) != t_POL) err(typeer,"sturm");
  if (gcmp0(x)) err(zeropoler,"sturm");
  s=lgef(x); if (s==3) return 0;

  sl = gsigne(leading_term(x));
  if (s==4)
  {
    t = a? gsigne(poleval(x,a)): -sl;
    if (t == 0) { avma = av; return 0; }
    s = b? gsigne(poleval(x,b)):  sl;
    avma = av; return (s == t)? 0: 1;
  }
  u=gdiv(x,content(x)); v=derivpol(x);
  v=gdiv(v,content(v));
  g=gun; h=gun;
  s = b? gsigne(poleval(u,b)): sl;
  t = a? gsigne(poleval(u,a)): ((lgef(u)&1)? sl: -sl);
  r1=0;
  sr = b? gsigne(poleval(v,b)): s;
  if (sr)
  {
    if (!s) s=sr;
    else if (sr!=s) { s= -s; r1--; }
  }
  sr = a? gsigne(poleval(v,a)): -t;
  if (sr)
  {
    if (!t) t=sr;
    else if (sr!=t) { t= -t; r1++; }
  }
  for(;;)
  {
    GEN p1, r = pseudorem(u,v);
    long du=lgef(u), dv=lgef(v), dr=lgef(r), degq=du-dv;

    if (dr<=2) err(talker,"not a squarefree polynomial in sturm");
    if (gsigne(leading_term(v)) > 0 || degq&1) r=gneg_i(r);
    sl = gsigne((GEN) r[dr-1]);
    sr = b? gsigne(poleval(r,b)): sl;
    if (sr)
    {
      if (!s) s=sr;
      else if (sr!=s) { s= -s; r1--; }
    }
    sr = a? gsigne(poleval(r,a)): ((dr&1)? sl: -sl);
    if (sr)
    {
      if (!t) t=sr;
      else if (sr!=t) { t= -t; r1++; }
    }
    if (dr==3) { avma=av; return r1; }

    u=v; p1 = g; g = gabs(leading_term(u),DEFAULTPREC);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq),p1);
        h = gdiv(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    v = gdiv(r,p1);
    if (low_stack(lim,stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      if(DEBUGMEM>1) err(warnmem,"polsturm, dr = %ld",dr);
      gerepilemany(av,gptr,4);
    }
  }
}

/*******************************************************************/
/*                                                                 */
/*         POLYNOME QUADRATIQUE ASSOCIE A UN DISCRIMINANT          */
/*                                                                 */
/*******************************************************************/

GEN
quadpoly0(GEN x, long v)
{
  long res,l,tetpil,i,sx, tx = typ(x);
  GEN y,p1;

  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i]=(long)quadpoly0((GEN)x[i],v);
    return y;
  }
  if (tx!=t_INT) err(arither1);
  if (v < 0) v = 0;
  sx=signe(x);
  if (!sx) err(talker,"zero discriminant in quadpoly");
  y=cgetg(5,t_POL);
  y[1]=evalsigne(1) | evalvarn(v) | evallgef(5); y[4]=un;
  res=mod4(x); if (sx<0 && res) res=4-res;
  if (res>1) err(funder2,"quadpoly");

  l=avma; p1=shifti(x,-2); setsigne(p1,-signe(p1));
  y[2] = (long) p1;
  if (!res) y[3] = zero;
  else
  {
    if (sx<0) { tetpil=avma; y[2] = lpile(l,tetpil,addsi(1,p1)); }
    y[3] = lnegi(gun);
  }
  return y;
}

GEN
quadpoly(GEN x)
{
  return quadpoly0(x,-1);
}

GEN
quadgen(GEN x)
{
  GEN y=cgetg(4,t_QUAD);
  y[1]=lquadpoly(x); y[2]=zero; y[3]=un; return y;
}

/*******************************************************************/
/*                                                                 */
/*                    INVERSE MODULO GENERAL                       */
/*                                                                 */
/*******************************************************************/

GEN
ginvmod(GEN x, GEN y)
{
  long tx=typ(x);

  switch(typ(y))
  {
    case t_POL:
      if (tx==t_POL) return polinvmod(x,y);
      if (is_scalar_t(tx)) return ginv(x);
      break;
    case t_INT:
      if (tx==t_INT) return mpinvmod(x,y);
      if (tx==t_POL) return gzero;
  }
  err(typeer,"ginvmod");
  return NULL; /* not reached */
}

/***********************************************************************/
/**							              **/
/**		            NEWTON POLYGON                            **/
/**								      **/
/***********************************************************************/

/* assume leading coeff of x is non-zero */
GEN
newtonpoly(GEN x, GEN p)
{
  GEN y;
  long n,ind,a,b,c,u1,u2,r1,r2;
  long *vval, num[] = {evaltyp(t_INT) | m_evallg(3), 0, 0};

  if (typ(x)!=t_POL) err(typeer,"newtonpoly");
  n=lgef(x)-3; if (n<=0) { y=cgetg(1,t_VEC); return y; }
  y = cgetg(n+1,t_VEC); x += 2; /* now x[i] = term of degree i */
  vval = (long *) gpmalloc(sizeof(long)*(n+1));
  for (a=0; a<=n; a++) vval[a] = ggval((GEN)x[a],p);
  for (a=0, ind=1; a<n; a++)
  {
    if (vval[a] != VERYBIGINT) break;
    y[ind++] = lstoi(VERYBIGINT);
  }
  for (b=a+1; b<=n; a=b, b=a+1)
  {
    while (vval[b] == VERYBIGINT) b++;
    u1=vval[a]-vval[b]; u2=b-a;
    for (c=b+1; c<=n; c++)
    {
      if (vval[c] == VERYBIGINT) continue;
      r1=vval[a]-vval[c]; r2=c-a;
      if (u1*r2<=u2*r1) { u1=r1; u2=r2; b=c; }
    }
    while (ind<=b) { affsi(u1,num); y[ind++] = ldivgs(num,u2); }
  }
  free(vval); return y;
}

extern int cmp_pol(GEN x, GEN y);

/* Factor polynomial a on the number field defined by polynomial t */
GEN
polfnf(GEN a, GEN t)
{
  GEN x0, y,p1,p2,u,g,fa,n,unt;
  long av=avma,tetpil,lx,v,i,k,vt;

  if (typ(a)!=t_POL || typ(t)!=t_POL) err(typeer,"polfnf");
  if (gcmp0(a)) return gcopy(a);
  vt=varn(t); v=varn(a);
  if (vt<=v)
    err(talker,"polynomial variable must be of higher priority than number field variable\nin factornf");
  u = gdiv(a, ggcd(a,derivpol(a)));
  unt = gmodulsg(1,t); u = gmul(unt,u);
  g = lift(u);
  for (k=-1; ; k++)
  {
    n = gsub(polx[MAXVARN], gmulsg(k,polx[vt]));
    n = subres(t, poleval(g,n));
    if (issquarefree(n)) break;
  }
  if (DEBUGLEVEL > 4) fprintferr("polfnf: choosing k = %ld\n",k);
  fa=factor(n); fa=(GEN)fa[1]; lx=lg(fa);
  y=cgetg(3,t_MAT);
  p1=cgetg(lx,t_COL); y[1]=(long)p1;
  p2=cgetg(lx,t_COL); y[2]=(long)p2;
  x0 = gadd(polx[v],gmulsg(k,gmodulcp(polx[vt],t)));
  for (i=1; i<lx; i++)
  {
    GEN b, pro = ggcd(u, gmul(unt, poleval((GEN)fa[i], x0)));
    long e;

    p1[i] = (typ(pro)==t_POL)? ldiv(pro,leading_term(pro)): (long)pro;
    if (gcmp1((GEN)p1[i])) err(talker,"reducible modulus in factornf");
    e=0; while (poldivis(a,(GEN)p1[i], &b)) { a = b; e++; }
    p2[i] = lstoi(e);
  }
  (void)sort_factor(y, cmp_pol);
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
}
