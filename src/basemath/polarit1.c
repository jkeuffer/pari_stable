/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (first part)                              **/
/**                                                                   **/
/***********************************************************************/
/* $Id$ */
#include "pari.h"
GEN get_mul_table(GEN x,GEN bas,GEN *T);
GEN pol_to_monic(GEN pol, GEN *lead);
GEN sort_factor(GEN y, int (*cmp)(GEN,GEN));
GEN bsrch(GEN p, GEN fa, long Ka, GEN eta, long Ma);
GEN eleval(GEN f,GEN h,GEN a);
GEN respm(GEN f1,GEN f2,GEN pm);
GEN setup(GEN p,GEN f,GEN theta,GEN nut, long *La, long *Ma);
GEN vstar(GEN p,GEN h);

/* see splitgen() for how to use these two */
GEN
setloop(GEN a)
{
  a=icopy(a); new_chunk(2); /* dummy to get two cells of extra space */
  return a;
}

/* assume a > 0 */
GEN
incpos(GEN a)
{
  long i,l=lgefint(a);

  for (i=l-1; i>1; i--)
    if (++a[i]) return a;
  i=l+1; a--; /* use extra cell */
  a[0]=evaltyp(1) | evallg(i);
  a[1]=evalsigne(1) | evallgefint(i);
  return a;
}

GEN
incloop(GEN a)
{
  long i,l;

  switch(signe(a))
  {
    case 0:
      a--; /* use extra cell */
      a[0]=evaltyp(t_INT) | evallg(3);
      a[1]=evalsigne(1) | evallgefint(3);
      a[2]=1; return a;

    case -1:
      l=lgefint(a);
      for (i=l-1; i>1; i--)
        if (a[i]--) break;
      if (a[2] == 0)
      {
        a++; /* save one cell */
        a[0] = evaltyp(t_INT) | evallg(2);
        a[1] = evalsigne(0) | evallgefint(2);
      }
      return a;

    default:
      return incpos(a);
  }
}

/*******************************************************************/
/*                                                                 */
/*                           DIVISIBILITE                          */
/*                 Renvoie 1 si y divise x, 0 sinon .              */
/*                                                                 */
/*******************************************************************/

int
gdivise(GEN x, GEN y)
{
  long av=avma;
  x=gmod(x,y); avma=av; return gcmp0(x);
}

int
poldivis(GEN x, GEN y, GEN *z)
{
  long av = avma;
  GEN p1 = poldivres(x,y,ONLY_DIVIDES);
  if (p1) { *z = p1; return 1; }
  avma=av; return 0;
}

/*******************************************************************/
/*                                                                 */
/*                          REDUCTION                              */
/*    Do the transformation t_FRACN/t_RFRACN --> t_FRAC/t_RFRAC    */
/*                                                                 */
/*******************************************************************/

/* x[1] is scalar, non-zero */
static GEN
gred_simple(GEN x)
{
  GEN p1,p2,x2,x3;

  x2=content((GEN)x[2]);
  if (gcmp1(x2)) { x = gcopy(x); settyp(x, t_RFRAC); return gcopy(x); }
  x3=gdiv((GEN)x[1],x2); p2=denom(x3);
  x2=gdiv((GEN)x[2],x2);

  p1=cgetg(3,t_RFRAC);
  p1[1]=(long)numer(x3);
  p1[2]=lmul(x2,p2); return p1;
}

GEN
gred_rfrac(GEN x)
{
  GEN y,p1,xx1,xx2,x3, x1 = (GEN)x[1], x2 = (GEN)x[2];
  long tx,ty;

  if (gcmp0(x1)) return gcopy(x1);

  tx=typ(x1); ty=typ(x2);
  if (ty!=t_POL)
  {
    if (tx!=t_POL) return gcopy(x);
    if (gvar2(x2) > varn(x1)) return gdiv(x1,x2);
    err(talker,"incompatible variables in gred");
  }
  if (tx!=t_POL)
  {
    if (varn(x2) < gvar2(x1)) return gred_simple(x);
    err(talker,"incompatible variables in gred");
  }
  if (varn(x2) < varn(x1)) return gred_simple(x);
  if (varn(x2) > varn(x1)) return gdiv(x1,x2);

  /* now x1 and x2 are polynomials with the same variable */
  xx1=content(x1); if (!gcmp1(xx1)) x1=gdiv(x1,xx1);
  xx2=content(x2); if (!gcmp1(xx2)) x2=gdiv(x2,xx2);
  x3=gdiv(xx1,xx2);
  y = poldivres(x1,x2,&p1);
  if (!signe(p1)) { cgiv(p1); return gmul(x3,y); }

  p1 = ggcd(x2,p1);
  if (!isscalar(p1)) { x1=gdeuc(x1,p1); x2=gdeuc(x2,p1); }
  xx1=numer(x3); xx2=denom(x3);
  p1=cgetg(3,t_RFRAC);
  p1[1]=lmul(x1,xx1);
  p1[2]=lmul(x2,xx2); return p1;
}
/*must NEVER returns a FRACN or a RFRACN*/
GEN
gred(GEN x)
{
  long tx=typ(x),av=avma;
  GEN y,p1,x1,x2;

  if (is_frac_t(tx))
  {
    x1=(GEN)x[1]; x2=(GEN)x[2];
    y = dvmdii(x1,x2,&p1);
    if (p1 == gzero) return y; /* gzero volontaire */
    (void)new_chunk((lgefint(x1)+lgefint(x2))<<1);
    p1=mppgcd(x2,p1);
    if (is_pm1(p1)) { avma=av; y=gcopy(x); settyp(y,t_FRAC); return y; }
    avma=av; y=cgetg(3,t_FRAC);
    y[1]=ldivii(x1,p1);
    y[2]=ldivii(x2,p1); return y;
  }
  if (is_rfrac_t(tx))
    return gerepileupto(av, gred_rfrac(x));
  return gcopy(x);
}

/*******************************************************************/
/*                                                                 */
/*                  POLYNOMIAL EUCLIDEAN DIVISION                  */
/*                                                                 */
/*******************************************************************/
GEN gdivexact(GEN x, GEN y);

/* Polynomial division x / y:
 *   if z = ONLY_REM  return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile)
 */
GEN
poldivres(GEN x, GEN y, GEN *pr)
{
  long ty=typ(y),tx,vx,vy,dx,dy,dz,i,j,avy,av,av1,sx,lrem;
  int remainder;
  GEN z,p1,rem,y_lead,mod;
  GEN (*f)(GEN,GEN);

  if (pr == ONLY_DIVIDES_EXACT)
    { f = gdivexact; pr = ONLY_DIVIDES; } 
  else
    f = gdiv;
  if (is_scalar_t(ty))
  {
    if (pr == ONLY_REM) return gzero;
    if (pr && pr != ONLY_DIVIDES) *pr=gzero;
    return f(x,y);
  }
  tx=typ(x); vy=gvar9(y);
  if (is_scalar_t(tx) || gvar9(x)>vy)
  {
    if (pr == ONLY_REM) return gcopy(x);
    if (pr == ONLY_DIVIDES) return gcmp0(x)? gzero: NULL;
    if (pr) *pr=gcopy(x);
    return gzero;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"euclidean division (poldivres)");

  vx=varn(x);
  if (vx<vy)
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      p1 = zeropol(vx); if (pr == ONLY_REM) return p1;
      *pr = p1;
    }
    return f(x,y);
  }
  if (!signe(y)) err(talker,"euclidean division by zero (poldivres)");

  dy=lgef(y)-3; y_lead = (GEN)y[dy+2];
  if (gcmp0(y_lead)) /* normalize denominator if leading term is 0 */
  {
    err(warner,"normalizing a polynomial with 0 leading term");
    for (dy--; dy>=0; dy--)
    {
      y_lead = (GEN)y[dy+2];
      if (!gcmp0(y_lead)) break;
    }
  }
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(vx);
      *pr = zeropol(vx);
    }
    return f(x,(GEN)y[2]);
  }
  dx=lgef(x)-3;
  if (vx>vy || dx<dy)
  {
    if (pr)
    {
      if (pr == ONLY_DIVIDES) return gcmp0(x)? gzero: NULL;
      if (pr == ONLY_REM) return gcopy(x);
      *pr = gcopy(x);
    }
    return zeropol(vy);
  }
  dz=dx-dy; av=avma; /* to avoid gsub's later on */
  p1 = new_chunk(dy+3);
  for (i=2; i<dy+3; i++)
  {
    GEN p2 = (GEN)y[i];
    p1[i] = isexactzero(p2)? 0: (long)gneg_i(p2);
  }
  y = p1;
  switch(typ(y_lead))
  {
    case t_INTMOD:
    case t_POLMOD: y_lead = ginv(y_lead);
      f = gmul; mod = gmodulcp(gun, (GEN)y_lead[1]);
      break;
    default: if (gcmp1(y_lead)) y_lead = NULL;
      mod = NULL;
  }
  avy=avma; z=cgetg(dz+3,t_POL);
  z[1]=evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx]; remainder = (pr == ONLY_REM);
  z[dz]=y_lead? (long)f(p1,y_lead): lcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av1=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      if (y[i-j]) p1 = gadd(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (y_lead) p1 = f(p1,y_lead);
    if (!remainder) p1 = avma==av1? gcopy(p1): gerepileupto(av1,p1);
    z[i-dy] = (long)p1;
  }
  if (!pr) return gerepileupto(av,z-2);

  rem = (GEN)avma; av1 = (long)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++)
      if (y[i-j]) p1 = gadd(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    if (!gcmp0(p1)) { sx = 1; break; } /* remainder is non-zero */
    if (!isinexactreal(p1) && !isexactzero(p1)) break;
    if (!i) break;
    avma=av1;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (sx) { avma=av; return NULL; }
    avma = (long)rem;
    return gerepileupto(av,z-2);
  }
  lrem=i+3; rem -= lrem;
  if (avma==av1) { avma = (long)rem; p1 = gcopy(p1); }
  else p1 = gerepileupto((long)rem,p1);
  rem[0]=evaltyp(t_POL) | evallg(lrem);
  rem[1]=evalsigne(1) | evalvarn(vx) | evallgef(lrem);
  rem += 2;
  rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av1=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      if (y[i-j]) p1 = gadd(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    rem[i]=avma==av1? lcopy(p1):lpileupto(av1,p1);
  }
  rem -= 2;
  if (!sx) normalizepol_i(rem, lrem);
  if (remainder) return gerepileupto(av,rem);
  z -= 2;
  {
    GEN *gptr[2]; gptr[0]=&z; gptr[1]=&rem;
    gerepilemanysp(av,avy,gptr,2); *pr = rem; return z;
  }
}

/*******************************************************************/
/*                                                                 */
/*           ROOTS MODULO a prime p (no multiplicities)            */
/*                                                                 */
/*******************************************************************/
static GEN
mod(GEN x, GEN y)
{
  GEN z = cgetg(3,t_INTMOD);
  z[1]=(long)y; z[2]=(long)x; return z;
}

static long
factmod_init(GEN *F, GEN pp, long *p)
{
  GEN f = *F;
  long i,d;
  if (typ(f)!=t_POL || typ(pp)!=t_INT) err(typeer,"factmod");
  if (expi(pp) > BITS_IN_LONG - 3) *p = 0;
  else
  {
    *p = itos(pp);
    if (*p < 2) err(talker,"not a prime in factmod");
  }
  f = gmul(f, mod(gun,pp));
  if (!signe(f)) err(zeropoler,"factmod");
  f = lift_intern(f); d = lgef(f);
  for (i=2; i <d; i++) 
    if (typ(f[i])!=t_INT) err(impl,"factormod for general polynomials");
  *F = f; return d-3;
}

#define mods(x,y) mod(stoi(x),y)
static GEN
root_mod_2(GEN f)
{
  int z1, z0 = !signe(f[2]);
  long i,n;
  GEN y;

  for (i=2, n=1; i < lgef(f); i++)
    if (signe(f[i])) n++;
  z1 = n & 1;
  y = cgetg(z0+z1+1, t_COL); i = 1;
  if (z0) y[i++] = (long)mods(0,gdeux);
  if (z1) y[i]   = (long)mods(1,gdeux);
  return y;
}

#define i_mod4(x) (signe(x)? mod4((GEN)(x)): 0)
static GEN
root_mod_4(GEN f)
{
  long no,ne;
  int z0 = !signe(f[2]);
  int z2 = ((i_mod4(f[2]) + 2*i_mod4(f[3])) & 3) == 0;
  int i,z1,z3;
  GEN y,p;

  for (ne=0,i=2; i<lgef(f); i+=2)
    if (signe(f[i])) ne += mael(f,i,2);
  for (no=0,i=3; i<lgef(f); i+=2)
    if (signe(f[i])) no += mael(f,i,2);
  no &= 3; ne &= 3;
  z3 = (no == ne);
  z1 = (no == ((4-ne)&3));
  y=cgetg(1+z0+z1+z2+z3,t_COL); i = 1; p = stoi(4);
  if (z0) y[i++] = (long)mods(0,p);
  if (z1) y[i++] = (long)mods(1,p);
  if (z2) y[i++] = (long)mods(2,p);
  if (z3) y[i]   = (long)mods(3,p);
  return y;
}
#undef i_mod4

/* p even, accept p = 4 for p-adic stuff */
static GEN
root_mod_even(GEN f, long p)
{
  switch(p)
  {
    case 2: return root_mod_2(f);
    case 4: return root_mod_4(f);
  }
  err(talker,"not a prime in rootmod");
  return NULL; /* not reached */
}

/* by checking f(0..p-1) */
GEN
rootmod2(GEN f, GEN pp)
{
  GEN g,y,ss,q,r, x_minus_s;
  long p,av = avma,av1,d,i,nbrac;

  if (!(d = factmod_init(&f, pp, &p))) { avma=av; return cgetg(1,t_COL); }
  if (!p) err(talker,"prime too big in rootmod2");
  if ((p & 1) == 0) { avma = av; return root_mod_even(f,p); }
  x_minus_s = gadd(polx[varn(f)], stoi(-1));

  nbrac=1;
  y=(GEN)gpmalloc((d+1)*sizeof(long));
  if (gcmp0((GEN)f[2])) y[nbrac++] = 0;
  ss = icopy(gun); av1 = avma;
  do
  {
    mael(x_minus_s,2,2) = ss[2];
    /* one might do a FFT-type evaluation */
    q = Fp_poldivres(f, x_minus_s, pp, &r);
    if (signe(r)) avma = av1;
    else
    {
      y[nbrac++] = ss[2]; f = q; av1 = avma;
    }
    ss[2]++;
  }
  while (nbrac<d && p>ss[2]);
  if (nbrac == 1) { avma=av; return cgetg(1,t_COL); }
  if (nbrac == d && p != ss[2])
  {
    g = mpinvmod((GEN)f[3], pp); setsigne(g,-1);
    ss = modis(mulii(g, (GEN)f[2]), p);
    y[nbrac++]=ss[2];
  }
  avma=av; g=cgetg(nbrac,t_COL);
  if (isonstack(pp)) pp = icopy(pp);
  for (i=1; i<nbrac; i++) g[i]=(long)mods(y[i],pp);
  free(y); return g;
}

/* by splitting */
GEN
rootmod(GEN f, GEN p)
{
  long av = avma,tetpil,n,i,j,la,lb;
  GEN y,pol,a,b,q,pol0;

  if (!factmod_init(&f, p, &i)) { avma=av; return cgetg(1,t_COL); }
  i = p[lgefint(p)-1];
  if ((i & 1) == 0) { avma = av; return root_mod_even(f,i); }
  i=2; while (!signe(f[i])) i++;
  if (i == 2) j = 1;
  else
  {
    j = lgef(f) - (i-2);
    if (j==3) /* f = x^n */
    {
      avma = av; y = cgetg(2,t_COL);
      y[1] = (long)gmodulsg(0,p);
      return y;
    }
    a = cgetg(j, t_POL); /* a = f / x^{v_x(f)} */
    a[1] =  evalsigne(1) | evalvarn(varn(f)) | evallgef(j);
    f += i-2; for (i=2; i<j; i++) a[i]=f[i];
    j = 2; f = a;
  }
  q = shifti(p,-1);
  /* take gcd(x^(p-1) - 1, f) by splitting (x^q-1) * (x^q+1) */
  b = Fp_pow_mod_pol(polx[varn(f)],q, f,p);
  if (lgef(b)<3) err(talker,"not a prime in rootmod");
  b[2] = laddis((GEN)b[2],-1); /* b = x^((p-1)/2) - 1 mod f */
  a = Fp_pol_gcd(f,b, p);
  b[2] = laddis((GEN)b[2], 2); /* b = x^((p-1)/2) + 1 mod f */
  b = Fp_pol_gcd(f,b, p);
  la = lgef(a)-3;
  lb = lgef(b)-3; n = la + lb;
  if (!n)
  {
    avma = av; y = cgetg(n+j,t_COL);
    if (j>1) y[1] = (long)gmodulsg(0,p);
    return y;
  }
  y = cgetg(n+j,t_COL);
  if (j>1) { y[1] = zero; n++; }
  y[j] = (long)normalize_mod_p(b,p);
  if (la) y[j+lb] = (long)normalize_mod_p(a,p);
  pol = gadd(polx[varn(f)], gun); pol0 = (GEN)pol[2];
  while (j<=n)
  {
    a=(GEN)y[j]; la=lgef(a)-3;
    if (la==1)
      y[j++] = lsubii(p, (GEN)a[2]);
    else if (la==2)
    {
      GEN d = subii(sqri((GEN)a[3]), shifti((GEN)a[2],2));
      GEN e = mpsqrtmod(d,p), u = addis(q, 1); /* u = 1/2 */
      y[j++] = lmodii(mulii(u,subii(e,(GEN)a[3])), p);
      y[j++] = lmodii(mulii(u,negi(addii(e,(GEN)a[3]))), p);
    }
    else for (pol0[2]=1; ; pol0[2]++)
    {
      b = Fp_pow_mod_pol(pol,q, a,p);
      b[2] = laddis((GEN)b[2], -1);
      b = Fp_pol_gcd(a,b, p); lb = lgef(b)-3;
      if (lb && lb<la)
      {
        b = normalize_mod_p(b, p);
        y[j+lb] = (long)Fp_deuc(a,b, p);
        y[j]    = (long)b; break;
      }
    }
  }
  tetpil = avma; y = gerepile(av,tetpil,sort(y));
  if (isonstack(p)) p = icopy(p);
  for (i=1; i<=n; i++) y[i] = (long)mod((GEN)y[i], p);
  return y;
}

GEN
rootmod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return rootmod(f,p);
    case 1: return rootmod2(f,p);
    default: err(flagerr,"polrootsmod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION MODULO p                      */
/*                                                                 */
/*******************************************************************/
/*
 *Functions giving information on the factorisation.
 */
/*
 * f in ZZ[X] and p a prime number.
 */
long
Fp_is_squarefree(GEN f, GEN p)
{
  long av = avma;
  GEN z;
  z = Fp_pol_gcd(f,derivpol(f),p);
  avma = av;
  return lgef(z)==3;
}
/* idem
 * leading term of f must be prime to p.
 */
long
Fp_is_totally_split(GEN f, GEN p)
{
  long av = avma, n=lgef(f);
  GEN z;
  if (n <= 4) return 1;
  if (!is_bigint(p) && n-3 > p[2]) return 0;
  f = Fp_pol_red(f, p);
  if (lgef(f) != n) { avma=av; return 0; }
  z = Fp_pow_mod_pol(polx[varn(f)], p, f, p);
  avma = av; return lgef(z)==4 && gcmp1((GEN)z[3]) && !signe(z[2]);
}
/*
 * u in ZZ[X] and pp a prime number.
 * u must be squarefree mod pp.
 * leading term of u must be prime to pp.
 *
 * OK it is a copy paste of splitberlekamp
 * Consider merging.
 */
long
Fp_pol_nbfact(GEN u, GEN pp)
{
  ulong av,ltop=avma;
  GEN p1, p2, vker,v,w;
  long N = lgef(u)-3, d,i,j, vu = varn(u);
  GEN Q;
  if (DEBUGLEVEL > 7) timer2();
  Q=cgetg(N+1,t_MAT); Q[1]=lgetg(N+1,t_COL);
  p1 = (GEN)Q[1];
  for (i=1; i<=N; i++) p1[i] = zero;
  w = v = Fp_pow_mod_pol(polx[vu],pp,u,pp);
  for (j=2; j<=N; j++)
  {
    Q[j]=lgetg(N+1,t_COL);
    p1 = (GEN)Q[j];
    d=lgef(w)-1; p2 = w+1;
    for (i=1; i<d ; i++) p1[i] = p2[i];
    for (   ; i<=N; i++) p1[i] = zero;
    p1[j] = laddis((GEN)p1[j], -1);
    if (j < N)
    {
      av = avma;
      w = gerepileupto(av, Fp_res(gmul(w,v), u, pp));
    }
  }
  if (DEBUGLEVEL > 7) msgtimer("frobenius");
  vker = ker_mod_p(Q,pp);
  if (DEBUGLEVEL > 7) msgtimer("kernel");
  avma=ltop;
  return lg(vker)-1;
}
/************************************************************/
static GEN
trivfact(void)
{
  GEN y=cgetg(3,t_MAT);
  y[1]=lgetg(1,t_COL);
  y[2]=lgetg(1,t_COL); return y;
}

static void
fqunclone(GEN x, GEN a, GEN p)
{
  long i,j,lx = lgef(x);
  for (i=2; i<lx; i++)
  {
    GEN p1 = (GEN)x[i];
    if (typ(p1) == t_POLMOD) { p1[1] = (long)a; p1 = (GEN)p1[2]; }
    if (typ(p1) == t_INTMOD) p1[1] = (long)p;
    else /* t_POL */
      for (j = lgef(p1)-1; j > 1; j--)
      {
        GEN p2 = (GEN)p1[j];
        if (typ(p2) == t_INTMOD) p2[1] = (long)p;
      }
  }
}

static GEN
try_pow(GEN w0, GEN pol, GEN p, GEN q, long r)
{
  GEN w2, w = Fp_pow_mod_pol(w0,q, pol,p);
  long s;
  if (gcmp1(w)) return w0;
  for (s=1; s<r; s++,w=w2)
  {
    w2 = gsqr(w);
    w2 = Fp_res(w2, pol, p);
    if (gcmp1(w2)) break;
  }
  return gcmp_1(w)? NULL: w;
}

/* INPUT:
 *  m integer (converted to polynomial w in Z[X] by stopoly)
 *  p prime; q = (p^d-1) / 2^r
 *  t[0] polynomial of degree k*d product of k irreducible factors of degree d
 *  t[0] is expected to be normalized (leading coeff = 1)
 * OUTPUT:
 *  t[0],t[1]...t[k-1] the k factors, normalized
 */
static void
split(long m, GEN *t, long d, GEN pg, GEN q, long r)
{
  long p,l,v,dv,av0,av;
  GEN w,w0;

  dv=lgef(*t)-3; if (dv==d) return;
  v=varn(*t); av0=avma; p = pg[2];
  for(av=avma;;avma=av)
  {
    if (p==2)
    {
      w0=w=gpuigs(polx[v],m-1); m+=2;
      for (l=1; l<d; l++)
      {
        w = gadd(w0, gsqr(w));
        w = Fp_pol_red(w, pg);
        w = Fp_res(w, *t, pg);
      }
    }
    else
    {
      w = Fp_res(stopoly(m,p,v),*t, pg);
      m++; w = try_pow(w,*t,pg,q,r);
      if (!w) continue;
      /* set w = w - 1 */
      w[2] = laddis((GEN)w[2], -1); /* w != 1 or -1 */
    }
    w = Fp_pol_gcd(*t,w, pg);
    l = lgef(w)-3; if (l && l!=dv) break;
  }
  w = normalize_mod_p(w, pg);
  w = gerepileupto(av0, w);
  l /= d; t[l]=Fp_deuc(*t,w,pg); *t=w;
  split(m,t+l,d,pg,q,r);
  split(m,t,  d,pg,q,r);
}

static void
splitgen(GEN m, GEN *t, long d, GEN  p, GEN q, long r)
{
  long l,v,dv,av;
  GEN w;

  dv=lgef(*t)-3; if (dv==d) return;
  v=varn(*t); m=setloop(m); m=incpos(m);
  av=avma;
  for(;; avma=av, m=incpos(m))
  {
    w = Fp_res(stopoly_gen(m,p,v),*t, p);
    w = try_pow(w,*t,p,q,r);
    if (!w) continue;
    /* set w = w - 1 */
    w[2] = laddis((GEN)w[2], -1); /* w != 1 or -1 */
    w = Fp_pol_gcd(*t,w, p); l=lgef(w)-3;
    if (l && l!=dv) break;

  }
  w = normalize_mod_p(w, p);
  w = gerepileupto(av, w);
  l /= d; t[l]=Fp_deuc(*t,w,p); *t=w;
  splitgen(m,t+l,d,p,q,r);
  splitgen(m,t,  d,p,q,r);
}

/* return S = [ x^p, x^2p, ... x^(n-1)p ] mod (p, T) */
static GEN
init_pow_p_mod_pT(GEN p, GEN T)
{
  long i, n = lgef(T)-3, v = varn(T);
  GEN p1, S = cgetg(n, t_VEC);
  S[1] = (long)Fp_pow_mod_pol(polx[v], p, T, p);
#if 1 /* use as many squarings as possible */
  for (i=2; i < n; i+=2)
  {     
    p1 = gsqr((GEN)S[i>>1]);
    S[i]   = (long)Fp_res(p1, T, p);
    if (i == n-1) break;
    p1 = gmul((GEN)S[i], (GEN)S[1]);
    S[i+1] = (long)Fp_res(p1, T, p);
  }       
#else
  for (i=2; i < n; i++)
  { 
    p1 = gmul((GEN)S[i-1], (GEN)S[1]);
    S[i] = (long)Fp_res(p1, T, p);
  } 
#endif
  return S;
} 

/* compute x^p, S is as above */
static GEN
spec_Fp_pow_mod_pol(GEN x, GEN p, GEN S)
{
  long av = avma, lim = stack_lim(av,1), i,dx = lgef(x)-3;
  GEN x0 = x+2, z;
  z = (GEN)x0[0];
  for (i = 1; i <= dx; i++)
  {
    GEN d, c = (GEN)x0[i]; /* assume coeffs in [0, p-1] */
    if (!signe(c)) continue;
    d = (GEN)S[i]; if (!gcmp1(c)) d = gmul(c,d);
    z = gadd(z, d);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"spec_Fp_pow_mod_pol");
      z = gerepileupto(av, z);
    }
  }
  z = Fp_pol_red(z, p);
  return gerepileupto(av, z);
}

/* factor f mod pp.
 * If (flag = 1) return the degrees, not the factors
 * If (flag = 2) return NULL if f is not irreducible
 */
static GEN
factcantor0(GEN f, GEN pp, long flag)
{
  long i,j,k,d,e,vf,p,nbfact,tetpil,av = avma;
  GEN ex,y,p1,f2,g,g1,u,v,pd,q;
  GEN *t;

  if (!(d = factmod_init(&f, pp, &p))) { avma=av; return trivfact(); }
  /* to hold factors and exponents */
  t = (GEN*)cgetg(d+1,t_VEC); ex = new_chunk(d+1);
  vf=varn(f); e = nbfact = 1;
  f = lift_intern(f);
  for(;;)
  {
    f2 = Fp_pol_gcd(f,derivpol(f), pp);
    if (flag > 1 && lgef(f2) > 3) return NULL;
    g1 = Fp_deuc(f,f2,pp);
    k = 0;
    while (lgef(g1)>3)
    {
      long du,dg;
      GEN S;
      k++; if (p && !(k%p)) { k++; f2 = Fp_deuc(f2,g1,pp); }
      p1 = Fp_pol_gcd(f2,g1, pp); u = g1; g1 = p1;
      if (!gcmp1(p1))
      {
        u = Fp_deuc( u,p1,pp);
        f2= Fp_deuc(f2,p1,pp);
      }
      du = lgef(u)-3;
      if (du <= 0) continue;

      /* here u is square-free (product of irred. of multiplicity e * k) */
      S = init_pow_p_mod_pT(pp, u);
      pd=gun; v=polx[vf];
      for (d=1; d <= du>>1; d++)
      {
        if (!flag) pd = mulii(pd,pp);
        v = spec_Fp_pow_mod_pol(v, pp, S);
        g = Fp_pol_gcd(gadd(v, gneg(polx[vf])), u, pp);
        dg = lgef(g)-3;
        if (dg <= 0) continue;

        /* Ici g est produit de pol irred ayant tous le meme degre d; */
        j=nbfact+dg/d;

        if (flag)
        {
          if (flag > 1) return NULL;
          for ( ; nbfact<j; nbfact++) { t[nbfact]=(GEN)d; ex[nbfact]=e*k; }
        }
        else
        {
          long r;
          g = normalize_mod_p(g, pp);
          t[nbfact]=g; q = subis(pd,1); /* also ok for p=2: unused */
          r = vali(q); q = shifti(q,-r);
         /* le premier parametre est un entier variable m qui sera
          * converti en un polynome w dont les coeff sont ses digits en
          * base p (initialement m = p --> X) pour faire pgcd de g avec
          * w^(p^d-1)/2 jusqu'a casser. p = 2 is treated separately.
          */
          if (p)
            split(p,t+nbfact,d,pp,q,r);
          else
            splitgen(pp,t+nbfact,d,pp,q,r);
          for (; nbfact<j; nbfact++) ex[nbfact]=e*k;
        }
        du -= dg;
        u = Fp_deuc(u,g,pp);
        v = Fp_res(v,u,pp);
      }
      if (du)
      {
        t[nbfact] = flag? (GEN)du: normalize_mod_p(u, pp);
        ex[nbfact++]=e*k;
      }
    }
    j = lgef(f2); if (j==3) break;

    e*=p; j=(j-3)/p+3; setlg(f,j); setlgef(f,j);
    for (i=2; i<j; i++) f[i]=f2[p*(i-2)+2];
  }
  if (flag > 1) { avma = av; return gun; } /* irreducible */
  tetpil=avma; y=cgetg(3,t_MAT);
  if (!flag)
  {
    y[1]=(long)t; setlg(t, nbfact);
    y[2]=(long)ex; (void)sort_factor(y,cmpii);
  }
  u=cgetg(nbfact,t_COL); y[1]=(long)u;
  v=cgetg(nbfact,t_COL); y[2]=(long)v;
  if (flag)
    for (j=1; j<nbfact; j++)
    {
      u[j] = lstoi((long)t[j]);
      v[j] = lstoi(ex[j]);
    }
  else
    for (j=1; j<nbfact; j++)
    {
      u[j] = (long)Fp_pol(t[j], pp);
      v[j] = lstoi(ex[j]);
    }
  return gerepile(av,tetpil,y);
}

GEN
factcantor(GEN f, GEN p)
{
  return factcantor0(f,p,0);
}

GEN
simplefactmod(GEN f, GEN p)
{
  return factcantor0(f,p,1);
}

GEN
is_irred_mod_p(GEN f, GEN p)
{
  return factcantor0(f,p,2);
}

/* vector of polynomials (in v) whose coeffs are given by the columns of x */
GEN
mat_to_vecpol(GEN x, long v)
{
  long i,j, lx = lg(x), lcol = lg(x[1]);
  GEN y = cgetg(lx, t_VEC);

  for (j=1; j<lx; j++)
  {
    GEN p1, col = (GEN)x[j];
    long k = lcol;

    while (k-- && gcmp0((GEN)col[k]));
    i=k+2; p1=cgetg(i,t_POL);
    p1[1] = evalsigne(1) | evallgef(i) | evalvarn(v);
    col--; for (k=2; k<i; k++) p1[k] = col[k];
    y[j] = (long)p1;
  }
  return y;
}

/* matrix whose entries are given by the coeffs of the polynomials in 
 * vector v (considered as degree n polynomials) */
GEN
vecpol_to_mat(GEN v, long n)
{
  long i,j,d,N = lg(v);
  GEN p1,w, y = cgetg(N, t_MAT);
  n++;
  for (j=1; j<N; j++)
  {
    p1 = cgetg(n,t_COL); y[j] = (long)p1;
    w = (GEN)v[j];
    if (typ(w) != t_POL) { p1[1] = (long)w; i=2; }
    else
    {
      d=lgef(w)-1; w++;
      for (i=1; i<d; i++) p1[i] = w[i];
    }
    for ( ; i<n; i++) p1[i] = zero;
  }
  return y;
}

/* set x <-- x + c*y mod p */
static void
Fp_pol_addmul(GEN x, GEN y, long c, long p)
{
  long i,lx = lgef(x), ly = lgef(y), l = min(lx,ly);
  if (p & ~MAXHALFULONG)
  {
    for (i=2; i<l;  i++) x[i] = ((ulong)x[i]+ (ulong)mulssmod(c,y[i],p)) % p; 
    for (   ; i<ly; i++) x[i] = mulssmod(c,y[i],p);
  }
  else
  {
    for (i=2; i<l;  i++) x[i] = ((ulong)x[i] + (ulong)(c*y[i])) % p; 
    for (   ; i<ly; i++) x[i] = (c*y[i]) % p; 
  }
  do i--; while (i>1 && !x[i]);
  if (i==1) setsigne(x,0); else { setsigne(x,1); setlgef(x,i+1); }
}

long
split_berlekamp(GEN Q, GEN *t, GEN pp, GEN pps2)
{
  GEN u = *t, p1, p2, vker,v,w,pol;
  long av,N = lgef(u)-3, d,i,j,kk,l1,l2,p, vu = varn(u);
  
  if (DEBUGLEVEL > 7) timer2();
  p = is_bigint(pp)? 0: pp[2];
  setlg(Q, N+1); setlg(Q[1], N+1);
  w = v = Fp_pow_mod_pol(polx[vu],pp,u,pp);
  for (j=2; j<=N; j++)
  {
    p1 = (GEN)Q[j]; setlg(p1, N+1);
    d=lgef(w)-1; p2 = w+1;
    for (i=1; i<d ; i++) p1[i] = p2[i];
    for (   ; i<=N; i++) p1[i] = zero;
    p1[j] = laddis((GEN)p1[j], -1);
    if (j < N)
    {
      av = avma;
      w = gerepileupto(av, Fp_res(gmul(w,v), u, pp));
    }
  }
  if (DEBUGLEVEL > 7) msgtimer("frobenius");
  vker = mat_to_vecpol(ker_mod_p(Q,pp), vu);
  if (DEBUGLEVEL > 7) msgtimer("kernel");
  d = lg(vker)-1;
  if (p)
    for (i=1; i<=d; i++)
    {
      p1 = (GEN)vker[i];
      for (j=2; j<lg(p1); j++) p1[j] = itos((GEN)p1[j]);
    }
  pol = cgetg(N+3,t_POL);

  for (kk=1; kk<d; )
  {
    GEN polt;
    if (p)
    {
      if (p==2)
      {
        pol[2] = ((mymyrand() & 0x1000) == 0);
        pol[1] = evallgef(pol[2]? 3: 2);
        for (i=2; i<=d; i++)
          Fp_pol_addmul(pol, (GEN)vker[i], ((mymyrand() & 0x1000) == 0), p);
      }
      else
      {
        pol[2] = mymyrand()%p; /* vker[1] = 1 */
        pol[1] = evallgef(pol[2]? 3: 2);
        for (i=2; i<=d; i++)
          Fp_pol_addmul(pol, (GEN)vker[i], mymyrand()%p, p);
      }
      polt = small_to_pol(pol+2, lgef(pol), p);
      setvarn(polt,vu);
    }
    else
    {
      pol[2] = (long)genrand(pp);
      pol[1] = evallgef(signe(pol[2])? 3: 2) | evalvarn(vu);
      for (i=2; i<=d; i++)
        pol = gadd(pol, gmul((GEN)vker[i], genrand(pp)));
      polt = Fp_pol_red(pol,pp);
    }
    for (i=1; i<=kk && kk<d; i++)
    {
      p1=t[i-1]; l1=lgef(p1)-3;
      if (l1>1)
      {
        av = avma; p2 = Fp_res(polt, p1, pp);
        if (lgef(p2) <= 3) { avma=av; continue; }
        p2 = Fp_pow_mod_pol(p2,pps2, p1,pp);
        /* set p2 = p2 - 1 */
        p2[2] = laddis((GEN)p2[2], -1);
        p2 = Fp_pol_gcd(p1,p2, pp); l2=lgef(p2)-3;
        if (l2>0 && l2<l1)
        {
          p2 = normalize_mod_p(p2, pp);
          t[i-1] = p2; kk++;
          t[kk-1] = Fp_deuc(p1,p2,pp);
          if (DEBUGLEVEL > 7) msgtimer("new factor");
        }
        else avma = av;
      }
    }
  }
  return d;
}

GEN
factmod(GEN f, GEN pp)
{
  long i,j,k,e,p,N,nbfact,av = avma,tetpil,d;
  GEN pps2,ex,y,f2,p1,g1,Q,u,v, *t;

  if (!(d = factmod_init(&f, pp, &p))) { avma=av; return trivfact(); }
  /* to hold factors and exponents */
  t = (GEN*)cgetg(d+1,t_VEC); ex = new_chunk(d+1);
  e = nbfact = 1;
  pps2 = shifti(pp,-1);

  Q = cgetg(d+1,t_MAT);
  for (i=1; i<=d; i++) Q[i] = lgetg(d+1, t_COL);
  p1 = (GEN)Q[1];
  for (i=1; i<=d; i++) p1[i] = zero;
  for(;;)
  {
    f2 = Fp_pol_gcd(f,derivpol(f), pp);
    g1 = gcmp1(f2)? f: Fp_deuc(f,f2,pp);
    k = 0;
    while (lgef(g1)>3)
    {
      k++; if (p && !(k%p)) { k++; f2 = Fp_deuc(f2,g1,pp); }
      p1 = Fp_pol_gcd(f2,g1, pp); u = g1; g1 = p1;
      if (!gcmp1(p1))
      {
        u = Fp_deuc( u,p1,pp);
        f2= Fp_deuc(f2,p1,pp);
      }
      N = lgef(u)-3;
      if (N)
      {
        /* here u is square-free (product of irred. of multiplicity e * k) */
        t[nbfact] = normalize_mod_p(u,pp);
        d = (N==1)? 1: split_berlekamp(Q, t+nbfact, pp, pps2);
        for (j=0; j<d; j++) ex[nbfact+j] = e*k;
        nbfact += d;
      }
    }
    if (!p) break;
    j=(lgef(f2)-3)/p+3; if (j==3) break;

    e*=p; setlg(f,j); setlgef(f,j);
    for (i=2; i<j; i++) f[i] = f2[p*(i-2)+2];
  }
  tetpil=avma; y=cgetg(3,t_MAT);
  y[1]=(long)t; setlg(t, nbfact);
  y[2]=(long)ex; (void)sort_factor(y,cmpii);
  u=cgetg(nbfact,t_COL); y[1]=(long)u;
  v=cgetg(nbfact,t_COL); y[2]=(long)v;
  for (j=1; j<nbfact; j++)
  {
    u[j] = (long)Fp_pol(t[j], pp);
    v[j] = lstoi(ex[j]);
  }
  return gerepile(av,tetpil,y);
}

GEN
factormod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return factmod(f,p);
    case 1: return simplefactmod(f,p);
    default: err(flagerr,"factormod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                Recherche de racines  p-adiques                  */
/*                                                                 */
/*******************************************************************/
/* make f suitable for [root|factor]padic */
static GEN
padic_pol_to_int(GEN f)
{
  long i, l = lgef(f);
  f = gdiv(f,content(f));
  for (i=2; i<l; i++)
    switch(typ(f[i]))
    {
      case t_INT: break;
      case t_PADIC: f[i] = ltrunc((GEN)f[i]); break;
      default: err(talker,"incorrect coeffs in padic_pol_to_int");
    }
  return f;
}

/* return x + O(pr), x in Z, pr = p^r */
static GEN
int_to_padic(GEN x, GEN p, GEN pr, long r)
{
  GEN p1,y;
  long v;
  if (typ(x) == t_PADIC) return gcopy(x);
  y = cgetg(5,t_PADIC);
  if (signe(x) && (v = pvaluation(x,p,&p1)) < r)
  {
    y[4] = lmodii(p1,pr); r -= v;
  }
  else 
  {
    y[4] = zero; v = r; r = 0;
  }
  y[3] = (long)pr; 
  y[2] = (long)p;
  y[1] = evalprecp(r)|evalvalp(v); return y;
}

/* return x + O(p^r), x in Z[X] */
static GEN
pol_to_padic(GEN x, GEN pr, GEN p, long r)
{
  long i,lx = lgef(x);
  GEN z = cgetg(lx,t_POL);
  for (i=2; i<lx; i++)
    z[i] = (long)int_to_padic((GEN)x[i],p,pr,r);
  z[1] = x[1]; return z;
}

static GEN
padic_trivfact(GEN x, GEN p, long r)
{
  GEN p1, y = cgetg(3,t_MAT);
  p1=cgetg(2,t_COL); y[1]=(long)p1; p = icopy(p);
  p1[1]=(long)pol_to_padic(x,gpowgs(p,r),p,r);
  p1=cgetg(2,t_COL); y[2]=(long)p1;
  p1[1]=un; return y;
}

/* a etant un p-adique, retourne le vecteur des racines p-adiques de f
 * congrues a a modulo p dans le cas ou on suppose f(a) congru a 0 modulo p
 * (ou a 4 si p=2).
 */
GEN
apprgen(GEN f, GEN a)
{
  GEN fp,p1,p,pro,x,x2,u,ip,quatre;
  long av=avma,tetpil,v,ps,i,j,k,lu,n,fl2;

  if (typ(f)!=t_POL) err(notpoler,"apprgen");
  if (gcmp0(f)) err(zeropoler,"apprgen");
  if (typ(a) != t_PADIC) err(rootper1);
  f = padic_pol_to_int(f);
  fp=derivpol(f); p1=ggcd(f,fp);
  if (lgef(p1)>3) { f=gdeuc(f,p1); fp=derivpol(f); }
  p=(GEN)a[2]; p1=poleval(f,a);
  v=ggval(p1,p); if (v <= 0) err(rootper2);
  fl2=egalii(p,gdeux);
  if (fl2)
  {
    if (v==1) err(rootper2);
    quatre=stoi(4);
  }
  v=ggval(poleval(fp,a),p);
  if (!v) /* simple zero */
  {
    while (!gcmp0(p1))
    {
      a = gsub(a,gdiv(p1,poleval(fp,a)));
      p1 = poleval(f,a);
    }
    tetpil=avma; pro=cgetg(2,t_VEC); pro[1]=lcopy(a);
    return gerepile(av,tetpil,pro);
  }
  n=lgef(f)-3; pro=cgetg(n+1,t_VEC);
  p1=poleval(f,gadd(a,gmul(fl2?quatre:p,polx[varn(f)])));
  if (!gcmp0(p1)) p1=gdiv(p1,gpuigs(p,ggval(p1,p)));

  if (is_bigint(p)) err(impl,"apprgen for p>=2^31");
  x = ggrandocp(p, valp(a) | precp(a));
  if (fl2)
  {
    ps=4; x2=ggrandocp(p,2); p=quatre;
  }
  else
  {
    ps=itos(p); x2=ggrandocp(p,1);
  }
  for (j=0,i=0; i<ps; i++)
  {
    ip=stoi(i);
    if (gcmp0(poleval(p1,gadd(ip,x2))))
    {
      u=apprgen(p1,gadd(x,ip)); lu=lg(u);
      for (k=1; k<lu; k++)
      {
        j++; pro[j]=ladd(a,gmul(p,(GEN)u[k]));
      }
    }
  }
  tetpil=avma; setlg(pro,j+1);
  return gerepile(av,tetpil,gcopy(pro));
}

/* Retourne le vecteur des racines p-adiques de f en precision r */
GEN
rootpadic(GEN f, GEN p, long r)
{
  GEN fp,y,z,p1,pr,rac;
  long lx,i,j,k,n,av=avma,tetpil,fl2;

  if (typ(f)!=t_POL) err(notpoler,"rootpadic");
  if (gcmp0(f)) err(zeropoler,"rootpadic");
  if (r<=0) err(rootper4);
  f = padic_pol_to_int(f);
  fp=derivpol(f); p1=ggcd(f,fp);
  if (lgef(p1)>3) { f=gdeuc(f,p1); fp=derivpol(f); }
  fl2=egalii(p,gdeux); rac=(fl2 && r>=2)? rootmod(f,stoi(4)): rootmod(f,p);
  lx=lg(rac); p=gclone(p);
  if (r==1)
  {
    tetpil=avma; y=cgetg(lx,t_COL);
    for (i=1; i<lx; i++)
    {
      z=cgetg(5,t_PADIC); y[i]=(long)z;
      z[1] = evalprecp(1)|evalvalp(0);
      z[2] = z[3] = (long)p;
      z[4] = lcopy(gmael(rac,i,2));
    }
    return gerepile(av,tetpil,y);
  }
  n=lgef(f)-3; y=cgetg(n+1,t_COL);
  j=0; pr = NULL;
  z = cgetg(5,t_PADIC);
  z[2] = (long)p;
  for (i=1; i<lx; i++)
  {
    p1 = gmael(rac,i,2);
    if (signe(p1))
    {
      if (!fl2 || mod2(p1))
      {
        z[1] = evalvalp(0)|evalprecp(r);
        z[4] = (long)p1;
      }
      else
      {
        z[1] = evalvalp(1)|evalprecp(r);
        z[4] = un;
      }
      if (!pr) pr=gpuigs(p,r);
      z[3] = (long)pr;
    }
    else
    {
      z[1] = evalvalp(r);
      z[3] = un;
      z[4] = (long)p1;
    }
    p1 = apprgen(f,z);
    for (k=1; k<lg(p1); k++) y[++j]=p1[k];
  }
  tetpil=avma; setlg(y,j+1);
  return gerepile(av,tetpil,gcopy(y));
}
/*************************************************************************/
/*                             rootpadicfast                             */
/*************************************************************************/

/*
  SPEC:
  q is an integer > 1
  Q is an integer > 0 and Q|q^r for an exponent r
  
  f in ZZ[X], with leading term prime to q.
  S must be a simple root mod p for all p|q.

  return roots of f mod Q, as integers (implicitly mod Q)
*/

/* STANDARD USE
   There exists p a prime number and a>0,b two long such that
   q=p^a , Q=p^b
   
   f in ZZ[X], with leading term prime to p.
   S must be a simple root mod p.

   return p-adics roots of f with prec b, as integers (implicitly mod Q)
*/

GEN
rootpadiclift(GEN T, GEN S, GEN q, GEN Q)
{
  ulong   ltop=avma;
  long    x;
  GEN     qold;
  GEN     W, Tr, Sr, Wr = gzero;
  int     flag, init;
  x = varn(T);
  qold = q ;
  Tr = Fp_pol_red(T,q);
  W=Fp_poleval(deriv(Tr, x),S,q);
  W=mpinvmod(W,q);
  flag = 1; init = 0;
  while (flag)
  {
    q = sqri(q);
    if (cmpii(q,Q)>= 0)
    {
      flag = 0;
      q = Q;
    }
    Tr = Fp_pol_red(T,q);
    Sr = S;
    if (init)
    {
      W = modii(mulii(Wr,Fp_poleval(deriv(Tr,x),Sr,q)),qold);
      W = subii(gdeux,W);
      W = modii(mulii(Wr, W),qold);
    }
    else
      init = 1;
    Wr = W;
    S = subii(Sr, mulii(Wr, Fp_poleval(Tr, Sr,q)));
    S = modii(S,q);
    qold = q;
  }
  return gerepileupto(ltop,S);
}
/*
 * Apply rootpadiclift to all roots in S and trace trick.
 * Elements of S must be distinct simple roots mod p for all p|q.
 */

GEN
rootpadicliftroots(GEN f, GEN S, GEN q, GEN pr)
{
  GEN y;
  long i,n=lg(S);
  if (n==1)
    return gcopy(S);
  y=cgetg(n,typ(S));
  for (i=1; i<n-1; i++)
    y[i]=(long) rootpadiclift(f, (GEN) S[i], q, pr);
  if (n!=lgef(f)-2)/* non totally split*/
    y[n-1]=(long) rootpadiclift(f, (GEN) S[n-1], q, pr);
  else/* distinct-->totally split-->use trace trick */
  {
    ulong av=avma;
    GEN z;
    z=(GEN)f[lgef(f)-2];/*-trace(roots)*/
    for(i=1; i<n-1;i++)
      z=addii(z,(GEN) y[i]);
    z=modii(negi(z),pr);
    y[n-1]=lpileupto(av,z);
  }
  return y;
}
/*
 p is a prime number, pr a power of p,

 f in ZZ[X], with leading term prime to p.
 f must have no multiple roots mod p.

 return p-adics roots of f with prec pr, as integers (implicitly mod pr)
 
*/
GEN
rootpadicfast(GEN f, GEN p, GEN pr)
{
  ulong ltop=avma;
  GEN S,y;
  S=lift(rootmod(f,p));/*no multiplicity*/
  if (lg(S)==1)/*no roots*/
  {
    avma=ltop;
    return cgetg(1,t_COL);
  }
  S=gclone(S);
  avma=ltop;
  y=rootpadicliftroots(f,S,p,pr);
  gunclone(S);
  return y;
}
/**************************************************************************/
static long
getprec(GEN x, long prec, GEN *p)
{
  long i,e;
  GEN p1;

  for (i = lgef(x)-1; i>1; i--)
  {
    p1=(GEN)x[i];
    if (typ(p1)==t_PADIC)
    {
      e=valp(p1); if (signe(p1[4])) e += precp(p1);
      if (e<prec) prec = e; *p = (GEN)p1[2];
    }
  }
  return prec;
}

/* a appartenant a une extension finie de Q_p, retourne le vecteur des
 * racines de f congrues a a modulo p dans le cas ou on suppose f(a) congru a
 * 0 modulo p (ou a 4 si p=2).
 */
GEN
apprgen9(GEN f, GEN a)
{
  GEN fp,p1,p,pro,x,x2,u,ip,t,vecg,quatre;
  long av=avma,tetpil,v,ps_1,i,j,k,lu,n,prec,d,va,fl2;

  if (typ(f)!=t_POL) err(notpoler,"apprgen9");
  if (gcmp0(f)) err(zeropoler,"apprgen9");
  if (typ(a)==t_PADIC) return apprgen(f,a);
  if (typ(a)!=t_POLMOD || typ(a[2])!=t_POL) err(rootper1);
  fp=derivpol(f); p1=ggcd(f,fp);
  if (lgef(p1)>3) { f=gdeuc(f,p1); fp=derivpol(f); }
  t=(GEN)a[1];
  prec = getprec((GEN)a[2], BIGINT, &p);
  prec = getprec(t, prec, &p);
  if (prec==BIGINT) err(rootper1);

  p1=poleval(f,a); v=ggval(lift_intern(p1),p); if (v<=0) err(rootper2);
  fl2=egalii(p,gdeux);
  if (fl2)
  {
    if (v==1) err(rootper2);
    quatre=stoi(4);
  }
  v=ggval(lift_intern(poleval(fp,a)), p);
  if (!v)
  {
    while (!gcmp0(p1))
    {
      a = gsub(a, gdiv(p1,poleval(fp,a)));
      p1 = poleval(f,a);
    }
    tetpil=avma; pro=cgetg(2,t_COL); pro[1]=lcopy(a);
    return gerepile(av,tetpil,pro);
  }
  n=lgef(f)-3; pro=cgetg(n+1,t_COL); j=0;
  p1=poleval(f,gadd(a,gmul(fl2?quatre:p,polx[varn(f)])));
  if (!gcmp0(p1)) p1=gdiv(p1,gpuigs(p,ggval(p1,p)));

  if (is_bigint(p)) err(impl,"apprgen9 for p>=2^31");
  x=gmodulcp(ggrandocp(p,prec), t);
  if (fl2)
  {
    ps_1=3; x2=ggrandocp(p,2); p=quatre;
  }
  else
  {
    ps_1=itos(p)-1; x2=ggrandocp(p,1);
  }
  d=lgef(t)-3; vecg=cgetg(d+1,t_COL);
  for (i=1; i<=d; i++)
    vecg[i] = (long)setloop(gzero);
  va=varn(t);
  for(;;) /* loop through F_q */
  {
    ip=gmodulcp(gtopoly(vecg,va),t);
    if (gcmp0(poleval(p1,gadd(ip,x2))))
    {
      u=apprgen9(p1,gadd(ip,x)); lu=lg(u);
      for (k=1; k<lu; k++)
      {
        j++; pro[j]=ladd(a,gmul(p,(GEN)u[k]));
      }
    }
    for (i=d; i; i--)
    {
      p1 = (GEN)vecg[i];
      if (p1[2] != ps_1) { (void)incloop(p1); break; }
      affsi(0, p1);
    }
    if (!i) break;
  }
  tetpil=avma; setlg(pro,j+1);
  return gerepile(av,tetpil,gcopy(pro));
}

/*****************************************/
/*  Factorisation p-adique d'un polynome */
/*****************************************/

/* factorise le polynome T=nf[1] dans Zp avec la precision pr */
static GEN
padicff2(GEN nf,GEN p,long pr)
{
  long N=lgef(nf[1])-3,i,j,d,l;
  GEN mat,V,D,fa,p1,pk,dec_p,pke,a,theta;

  pk=gpuigs(p,pr); dec_p=primedec(nf,p);
  l=lg(dec_p); fa=cgetg(l,t_COL);
  for (i=1; i<l; i++)
  {
    p1 = (GEN)dec_p[i];
    pke = idealpows(nf,p1, pr * itos((GEN)p1[3]));
    p1=smith2(pke); V=(GEN)p1[3]; D=(GEN)p1[1];
    for (d=1; d<=N; d++)
      if (! egalii(gcoeff(V,d,d),pk)) break;
    a=ginv(D); theta=gmael(nf,8,2); mat=cgetg(d,t_MAT);
    for (j=1; j<d; j++)
    {
      p1 = gmul(D, element_mul(nf,theta,(GEN)a[j]));
      setlg(p1,d); mat[j]=(long)p1;
    }
    fa[i]=(long)caradj(mat,0,NULL);
  }
  a = cgetg(l,t_COL); pk = icopy(pk);
  for (i=1; i<l; i++)
    a[i] = (long)pol_to_padic((GEN)fa[i],pk,p,pr);
  return a;
}

static GEN
padicff(GEN x,GEN p,long pr)
{
  GEN q,bas,mul,dx,nf,mat;
  long n=lgef(x)-3,av=avma;

  nf=cgetg(10,t_VEC); nf[1]=(long)x; dx=discsr(x);
  mat=cgetg(3,t_MAT); mat[1]=lgetg(3,t_COL); mat[2]=lgetg(3,t_COL);
  coeff(mat,1,1)=(long)p; coeff(mat,1,2)=lstoi(pvaluation(dx,p,&q));
  coeff(mat,2,1)=(long)q; coeff(mat,2,2)=un;
  bas=allbase4(x,(long)mat,(GEN*)(nf+3),NULL);
  if (!carrecomplet(divii(dx,(GEN)nf[3]),(GEN*)(nf+4)))
    err(bugparier,"factorpadic2 (incorrect discriminant)");
  mul = get_mul_table(x,bas,NULL);
  nf[7]=(long)bas;
  nf[8]=linv(vecpol_to_mat(bas,n));
  nf[9]=lmul((GEN)nf[8],mul); nf[2]=nf[5]=nf[6]=zero;
  return gerepileupto(av,padicff2(nf,p,pr));
}

GEN
factorpadic2(GEN x, GEN p, long r)
{
  long av=avma,av2,k,i,j,i1,f,nbfac;
  GEN res,p1,p2,y,d,a,ap,t,v,w;
  GEN *fa;

  if (typ(x)!=t_POL) err(notpoler,"factorpadic");
  if (gcmp0(x)) err(zeropoler,"factorpadic");
  if (r<=0) err(rootper4);

  if (lgef(x)==3) return trivfact();
  if (lgef(x)==4) return padic_trivfact(x,p,r);
  y=cgetg(3,t_MAT);
  fa = (GEN*)new_chunk(lgef(x)-2);
  d=content(x); a=gdiv(x,d);
  ap=derivpol(a); t=ggcd(a,ap); v=gdeuc(a,t);
  w=gdeuc(ap,t); j=0; f=1; nbfac=0;
  while (f)
  {
    j++; w=gsub(w,derivpol(v)); f=signe(w);
    if (f) { res=ggcd(v,w); v=gdeuc(v,res); w=gdeuc(w,res); }
    else res=v;
    fa[j]=(lgef(res)>3) ? padicff(res,p,r) : cgetg(1,t_COL);
    nbfac += (lg(fa[j])-1);
  }
  av2=avma; y=cgetg(3,t_MAT);
  p1=cgetg(nbfac+1,t_COL); y[1]=(long)p1;
  p2=cgetg(nbfac+1,t_COL); y[2]=(long)p2;
  for (i=1,k=0; i<=j; i++)
    for (i1=1; i1<lg(fa[i]); i1++)
    {
      p1[++k]=lcopy((GEN)fa[i][i1]); p2[k]=lstoi(i);
    }
  return gerepile(av,av2,y);
}

/*******************************************************************/
/*                                                                 */
/*                FACTORISATION P-adique avec ROUND 4              */
/*                                                                 */
/*******************************************************************/
GEN Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu,long r);
GEN nilord(GEN p, GEN fx, long mf, GEN gx, long flag);

static GEN
squarefree(GEN f, GEN *ex)
{
  GEN T,V,W,A,B;
  long n,i,k;

  T=ggcd(derivpol(f),f); V=gdeuc(f,T);
  n=lgef(f)-2; A=cgetg(n,t_COL); B=cgetg(n,t_COL);
  k=1; i=1;
  do
  {
    W=ggcd(T,V); T=gdeuc(T,W);
    if (lgef(V) != lgef(W))
    {
      A[i]=ldeuc(V,W); B[i]=k; i++;
    }
    k++; V=W;
  }
  while (lgef(V)>3);
  setlg(A,i); *ex=B; return A;
}

GEN
factorpadic4(GEN f,GEN p,long prec)
{
  GEN w,g,poly,fx,y,p1,p2,ex,pols,exps,ppow,lead;
  long v=varn(f),n=lgef(f)-3,av,tetpil,mfx,i,k,j,m,r,pr;

  if (typ(f)!=t_POL) err(notpoler,"factorpadic");
  if (gcmp0(f)) err(zeropoler,"factorpadic");
  if (prec<=0) err(rootper4);

  if (n==0) return trivfact();
  av=avma; f = padic_pol_to_int(f);
  if (n==1) return gerepileupto(av, padic_trivfact(f,p,prec));
  f = pol_to_monic(f, &lead);
  pr = lead? prec + (n-1) * ggval(lead,p): prec;
  poly=squarefree(f,&ex);
  pols=cgetg(n+1,t_COL);
  exps=cgetg(n+1,t_COL); n = lg(poly);
  for (j=1,i=1; i<n; i++)
  {
    long av1 = avma;
    fx=(GEN)poly[i]; mfx=ggval(discsr(fx),p);
    m = (pr<=mfx)?mfx+1:pr;
    w = (GEN)factmod(fx,p)[1]; r = lg(w)-1;
    g = lift_intern((GEN)w[r]);
    p2 = (r == 1)? nilord(p,fx,mfx,g,pr)
                 : Decomp(p,fx,mfx,polx[v],fx,g,m);
    if (p2)
    {
      p2 = gerepileupto(av1,p2);
      p1 = (GEN)p2[1];
      p2 = (GEN)p2[2];
      for (k=1; k<lg(p1); k++,j++)
      {
        pols[j]=p1[k];
        exps[j]=lmulis((GEN)p2[k],ex[i]);
      }
    }
    else
    {
      avma=av1;
      pols[j]=(long)fx;
      exps[j]=lstoi(ex[i]); j++;
    }
  }
  if (lead)
  {
    p1 = gmul(polx[v],lead);
    for (i=1; i<j; i++)
    {
      p2 = poleval((GEN)pols[i], p1);
      pols[i] = ldiv(p2, content(p2));
    }
  }

  tetpil=avma; y=cgetg(3,t_MAT);
  p1 = cgetg(j,t_COL); ppow = gpowgs(p,prec); p = icopy(p);
  for (i=1; i<j; i++)
    p1[i] = (long)pol_to_padic((GEN)pols[i],ppow,p,prec);
  y[1]=(long)p1; setlg(exps,j);
  y[2]=lcopy(exps); return gerepile(av,tetpil,y);
}

GEN
factorpadic0(GEN f,GEN p,long r,long flag)
{
  switch(flag)
  {
     case 0: return factorpadic4(f,p,r);
     case 1: return factorpadic2(f,p,r);
     default: err(flagerr,"factorpadic");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION DANS F_q                      */
/*                                                                 */
/*******************************************************************/
GEN to_Kronecker(GEN P, GEN Q);
GEN from_Kronecker(GEN z, GEN pol);
static GEN spec_Fq_pow_mod_pol(GEN x, GEN p, GEN a, GEN S);

static GEN
to_fq(GEN x, GEN a, GEN p)
{
  long i,lx = lgef(x);
  GEN p1, z = cgetg(3,t_POLMOD), pol = cgetg(lx,t_POL);
  pol[1] = x[1];
  for (i=2; i<lx; i++)
  {
    p1 = cgetg(3,t_INTMOD);
    p1[1] = (long)p;
    p1[2] = x[i]; pol[i] = (long)p1;
  }
  /* assume deg(pol) < deg(a) */
  z[1] = (long)a;
  z[2] = (long)pol; return z;
}

/* x POLMOD over Fq, return lift(x^n) */
static GEN
Kronecker_powmod(GEN x, GEN mod, GEN n)
{
  long lim,av,av0 = avma, i,j,m,v = varn(x);
  GEN y, p1, p, pol;

  for (i=lgef(mod)-1; i>1; i--)
  {
    p1 = (GEN)mod[i];
    if (typ(p1) == t_POLMOD) { pol = (GEN)p1[1] ; break; }
  }
  for (i=lgef(pol)-1; i>1; i--)
  {
    p1 = (GEN)pol[i];
    if (typ(p1) == t_INTMOD) { p = (GEN)p1[1] ; break; }
  }
  x = lift_intern(to_Kronecker(x,pol));

  /* adapted from powgi */
  av=avma; lim=stack_lim(av,1);
  p1 = n+2; m = *p1;

  y=x; j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = gsqr(y);
      y = from_Kronecker(Fp_pol(y,p), pol);
      setvarn(y, v);
      y = gres(y, mod);
      y = lift_intern(to_Kronecker(y,pol));

      if (m<0)
      {
        y = gmul(y,x);
        y = from_Kronecker(Fp_pol(y,p), pol);
        setvarn(y, v);
        y = gres(y, mod);
        y = lift_intern(to_Kronecker(y,pol));
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"Kronecker_powmod");
        y = gerepileupto(av, y);
      }
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  y = from_Kronecker(Fp_pol(y,p),pol);
  setvarn(y, v); return gerepileupto(av0, y);
}

/* pol. in v whose coeff are the digits of m in base qq */
static GEN
stopoly9(GEN pp, GEN mm, GEN qq, long v, GEN a)
{
  long q,l,m,l1,i,va, smll = !is_bigint(mm), p = pp[2];
  GEN y,p1,r;

  y = cgetg(bit_accuracy(lgefint(mm)) + 2, t_POL);
  va = varn(a);
  p1 = cgetg(bit_accuracy(lgefint(qq)) + 2,t_POL);
  p1[1] = evalsigne(1) | evalvarn(va);
  l = 2;
  if (smll)
  {
    q = itos(qq); m = itos(mm);
    do { y[l++] = m % q; m /= q; } while (m);
  }
  else
    do { mm=dvmdii(mm,qq,&r); y[l++]=(long)r; } while (signe(mm));
  if (smll)
    for (i=2; i<l; i++)
    {
      m=y[i]; l1=2;
      do { p1[l1++] = lstoi(m % p); m /= p; } while (m);
      setlgef(p1,l1); y[i]=(long)to_fq(p1,a,pp);
    }
  else
    for (i=2; i<l; i++)
    {
      mm=(GEN)y[i]; l1=2;
      do { mm=dvmdis(mm,p,&r); p1[l1++]=(long)r; } while (signe(mm));
      setlgef(p1,l1); y[i]=(long)to_fq(p1,a,pp);
    }
  y[1] = evalsigne(1) | evalvarn(v) | evallgef(l);
  return y;
}

/* renvoie un polynome aleatoire de la variable v
de degre inferieur ou egal a 2*d1-1 */
static GEN
stopoly92(GEN pg, long d1, long v, GEN a, GEN *ptres)
{
  GEN y,p1;
  long m,l1,i,d2,l,va=varn(a),k=lgef(a)-3,nsh;

  d2=2*d1+1; y=cgetg(d2+1,t_POL); y[1]=1;
  nsh=BITS_IN_RANDOM-1-k; if (nsh<=0) nsh=1;
  do
  {
    for (l=2; l<=d2; l++) y[l] = mymyrand() >> nsh;
    l=d2; while (!y[l]) l--;
  }
  while (l<=2);
  l++; y[1] = mymyrand() >> nsh;
  p1 = cgetg(BITS_IN_LONG+2,t_POL);
  p1[1] = evalsigne(1) | evalvarn(va);
  for (i=1; i<l; i++)
  {
    m=y[i]; l1=2;
    do { p1[l1++] = m&1? un: zero; m>>=1; } while (m);
    setlgef(p1,l1); y[i]=(long)to_fq(p1,a,pg);
  }
  *ptres = (GEN)y[1];
  y[1] = evalsigne(1) | evalvarn(v) | evallgef(l);
  return y;
}

static void
split9(GEN m, GEN *t, long d, GEN pp, GEN q, GEN munfq, GEN qq, GEN a, GEN S)
{
  long l,dv,v,av0,av,tetpil,p;
  GEN w,res,pol;

  dv=lgef(*t)-3; if (dv==d) return;
  v=varn(*t); m=setloop(m);
  av0=avma; p = pp[2];
  for(av=avma;;avma=av)
  {
    if (p==2)
    {
      pol = gres(stopoly92(pp,d,v,a,&res), *t);
      pol = lift_intern(lift_intern(pol));
      w = pol;
      for (l=1; l<d; l++)
      {
        GEN p1 = spec_Fq_pow_mod_pol(w, pp, a, S);
        p1 = lift_intern(lift_intern(p1));
        w = gadd(pol, p1); /* += w^q */
      }
      w = gadd(w, res); /* - res = res ! */
    }
    else
    {
      pol = gres(stopoly9(pp,m,qq,v,a), *t);
      m = incpos(m);
      w = Kronecker_powmod(pol, *t, q);
      if (lgef(w) == 3) continue;
      w[2] = ladd((GEN)w[2], munfq);
    }
    tetpil=avma; w=ggcd(*t,w); l=lgef(w)-3;
    if (l && l!=dv) break;
  }
  w = gerepile(av0,tetpil,w);
  l /= d; t[l]=gdeuc(*t,w); *t=w;
  split9(m,t+l,d,pp,q,munfq,qq,a,S);
  split9(m,t  ,d,pp,q,munfq,qq,a,S);
}

/* to "compare" (real) scalars and t_INTMODs */
static int
cmp_coeff(GEN x, GEN y)
{
  if (typ(x) == t_INTMOD) x = (GEN)x[2];
  if (typ(y) == t_INTMOD) y = (GEN)y[2];
  return gcmp(x,y);
}

int
cmp_pol(GEN x, GEN y)
{
  long fx[3], fy[3];
  long i,lx,ly;
  int fl;
  if (typ(x) == t_POLMOD) x = (GEN)x[2];
  if (typ(y) == t_POLMOD) y = (GEN)y[2];
  if (typ(x) == t_POL) lx = lgef(x); else { lx = 3; fx[2] = (long)x; x = fx; }
  if (typ(y) == t_POL) ly = lgef(y); else { ly = 3; fy[2] = (long)y; y = fy; }
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if ((fl = cmp_coeff((GEN)x[i], (GEN)y[i]))) return fl;
  return 0;
}

/* assume n > 0, x a POLMOD over Fq */
/* return S = [ X^q, X^2q, ... X^(n-1)q ] mod T (in Fq[X]) in Kronecker form */
static GEN
init_pow_q_mod_pT(GEN Xmod, GEN q, GEN a, GEN T)
{
  long i, n = lgef(T)-3;
  GEN p1, S = cgetg(n, t_VEC);

  S[1] = (long)Kronecker_powmod((GEN)Xmod[2], (GEN)Xmod[1], q);
#if 1 /* use as many squarings as possible */
  for (i=2; i < n; i+=2)
  {     
    p1 = gsqr((GEN)S[i>>1]);
    S[i]   = lres(p1, T);
    if (i == n-1) break;
    p1 = gmul((GEN)S[i], (GEN)S[1]);
    S[i+1] = lres(p1, T);
  }       
#else
  for (i=2; i < n; i++)
  { 
    p1 = gmul((GEN)S[i-1], (GEN)S[1]);
    S[i] = lres(p1, T);
  } 
#endif
  for (i=1; i < n; i++)
    S[i] = (long)lift_intern(to_Kronecker((GEN)S[i], a));
  return S;
}

/* compute x^q, S is as above */
static GEN
spec_Fq_pow_mod_pol(GEN x, GEN p, GEN a, GEN S)
{
  long av = avma, lim = stack_lim(av,1), i,dx = lgef(x)-3;
  GEN x0 = x+2, z,c;

  c = (GEN)x0[0];
  if (gcmp0(c)) z = gzero;
  else
    z = lift_intern(to_Kronecker(lift(c), a));
  for (i = 1; i <= dx; i++)
  {
    GEN d;
    c = (GEN)x0[i];
    if (gcmp0(c)) continue;
    d = (GEN)S[i];
    if (!gcmp1(c))
    {
      c = lift_intern(to_Kronecker(lift(c), a));
      d = gmul(c,d);
    }
    z = gadd(z, d);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"spec_Fq_pow_mod_pol");
      z = gerepileupto(av, z);
    }
  }
  z = Fp_pol(z, p);
  z = from_Kronecker(z, a);
  setvarn(z, varn(x)); return gerepileupto(av, z);
}

GEN
factmod9(GEN f, GEN pp, GEN a)
{
  long av = avma, tetpil,p,i,j,k,d,e,vf,va,nbfact,nbf,pk;
  GEN ex,y,f2,f3,df1,df2,g,g1,xmod,u,v,pd,q,qq,unfp,unfq,munfq, *t;
  GEN frobinv,X,m;

  if (typ(a)!=t_POL || typ(f)!=t_POL || gcmp0(a)) err(typeer,"factmod9");
  vf=varn(f); va=varn(a);
  if (va<=vf) err(talker,"polynomial variable must be of higher priority than finite field\nvariable in factorff");
  p=itos(pp); unfp=gmodulss(1,p); a=gmul(unfp,a);
  unfq=gmodulo(gmul(unfp,polun[va]), a); a = (GEN)unfq[1];
  f = gmul(unfq,f); if (!signe(f)) err(zeropoler,"factmod9");
  d = lgef(f)-3; if (!d) { avma=av; gunclone(a); return trivfact(); }

  pp = gmael(a,2,1); /* out of the stack */
  t = (GEN*)cgetg(d+1,t_VEC); ex = new_chunk(d+1);

  frobinv = gpowgs(pp, lgef(a)-4);
  xmod = cgetg(3,t_POLMOD);
  X = gmul(polx[vf],unfq);
  xmod[2] = (long)X;
  munfq = gneg(unfq);
  qq=gpuigs(pp,lgef(a)-3);
  m = addii(qq,pp);
  e = nbfact = 1;
  pk=1; df1=derivpol(f); f3=NULL;
  for(;;)
  {
    long du,dg;
    GEN S;
    while (gcmp0(df1))
    {
      pk *= p; e=pk;
      j=(lgef(f)-3)/p+3; setlg(f,j); setlgef(f,j);
      for (i=2; i<j; i++) f[i] = (long)powgi((GEN)f[p*(i-2)+2], frobinv);
      df1=derivpol(f); f3=NULL;
    }
    f2 = f3? f3: ggcd(f,df1);
    if (lgef(f2)==3) u=f;
    else
    {
      g1=gdeuc(f,f2); df2=derivpol(f2);
      if (gcmp0(df2)) { u=g1; f3=f2; }
      else
      {
        f3=ggcd(f2,df2);
        if (lgef(f3)==3) u=gdeuc(g1,f2);
        else
          u=gdeuc(g1,gdeuc(f2,f3));
      }
    }
    /* u is square-free (product of irreducibles of multiplicity e) */
    pd=gun; xmod[1]=(long)u;
    S = init_pow_q_mod_pT(xmod, qq, a, u);
    
    du = lgef(u)-3; v = X;
    for (d=1; d <= du>>1; d++)
    {
      pd=mulii(pd,qq);
      v = spec_Fq_pow_mod_pol(v, pp, a, S);
      g = ggcd(gsub(v,X),u);
      dg = lgef(g)-3;
      if (dg <= 0) continue;

      /* all factors of g have degree d */
      j = nbfact+dg/d;

      t[nbfact] = g;
      q = shifti(subis(pd,1),-1);
      split9(m,t+nbfact,d,pp,q,munfq,qq,a,S);
      for (; nbfact<j; nbfact++) ex[nbfact]=e;
      du -= dg;
      u = gdeuc(u,g);
      v = gres(v,u); xmod[1] = (long)u;
    }
    if (du) { t[nbfact]=u; ex[nbfact++]=e; }
    if (lgef(f2) == 3) break;

    f=f2; df1=df2; e += pk;
  }

  nbf=nbfact; tetpil=avma; y=cgetg(3,t_MAT);
  for (j=1; j<nbfact; j++)
  {
    t[j]=gdiv((GEN)t[j],leading_term(t[j]));
    for (k=1; k<j; k++)
      if (ex[k] && gegal(t[j],t[k]))
      {
        ex[k] += ex[j]; ex[j]=0;
        nbf--; break;
      }
  }
  u=cgetg(nbf,t_COL); y[1]=(long)u;
  v=cgetg(nbf,t_COL); y[2]=(long)v;
  for (j=1,k=0; j<nbfact; j++)
    if (ex[j])
    {
      k++;
      u[k]=(long)t[j];
      v[k]=lstoi(ex[j]);
    }
  y = gerepile(av,tetpil,y);
  u=(GEN)y[1];
  { /* put a back on the stack */
    GEN tokill = a;
    a = forcecopy(a);
    gunclone(tokill);
  }
  pp = (GEN)leading_term(a)[1];
  for (j=1; j<nbf; j++) fqunclone((GEN)u[j], a, pp);
  (void)sort_factor(y, cmp_pol); return y;
}

/*******************************************************************/
/*                                                                 */
/*                         RACINES COMPLEXES                       */
/*        l represente la longueur voulue pour les parties         */
/*            reelles et imaginaires des racines de x              */
/*                                                                 */
/*******************************************************************/
GEN square_free_factorization(GEN pol);
static GEN gnorml1(GEN x, long PREC);
static GEN laguer(GEN pol,long N,GEN y0,GEN EPS,long PREC);
static GEN zrhqr(GEN a,long PREC);

GEN
rootsold(GEN x, long l)
{
  long av1=avma,i,j,f,g,gg,fr,deg,l0,l1,l2,l3,l4,ln;
  long exc,expmin,m,deg0,k,ti,h,ii,e,e1,emax,v;
  GEN y,xc,xd0,xd,xdabs,p1,p2,p3,p4,p5,p6,p7,p8;
  GEN p9,p10,p11,p12,p14,p15,pa,pax,pb,pp,pq,ps;

  if (typ(x)!=t_POL) err(typeer,"rootsold");
  v=varn(x); deg0=lgef(x)-3; expmin=12 - bit_accuracy(l);
  if (!signe(x)) err(zeropoler,"rootsold");
  y=cgetg(deg0+1,t_COL); if (!deg0) return y;
  for (i=1; i<=deg0; i++)
  {
    p1=cgetg(3,t_COMPLEX); p1[1]=lgetr(l); p1[2]=lgetr(l); y[i]=(long)p1;
    for (j=3; j<l; j++) ((GEN)p1[2])[j]=((GEN)p1[1])[j]=0;
  }
  g=1; gg=1; f=1;
  for (i=2; i<=deg0+2; i++)
  {
    ti=typ(x[i]);
    if (ti==t_REAL) gg=0;
    else if (ti==t_QUAD)
    {
      p2=gmael3(x,i,1,2);
      if (gsigne(p2)>0) g=0;
    } else if (ti != t_INT && ti != t_INTMOD && !is_frac_t(ti)) g=0;
  }
  l1=avma; p2=cgetg(3,t_COMPLEX);
  p2[1]=lmppi(DEFAULTPREC); p2[2]=ldivrs((GEN)p2[1],10);
  p11=cgetg(4,t_POL); p11[1]=evalsigne(1)+evallgef(4);
  setvarn(p11,v); p11[3]=un;

  p12=cgetg(5,t_POL); p12[1]=evalsigne(1)+evallgef(5);
  setvarn(p12,v); p12[4]=un;
  for (i=2; i<=deg0+2 && gcmp0((GEN)x[i]); i++) gaffsg(0,(GEN)y[i-1]);
  k=i-2;
  if (k!=deg0)
  {
    if (k)
    {
      j=deg0+3-k; pax=cgetg(j,t_POL);
      pax[1]=evalsigne(1)+evallgef(j); setvarn(pax,v);
      for (i=2; i<j; i++) pax[i]=x[i+k];
    }
    else pax=x;
    xd0=deriv(pax,v); m=1; pa=pax;
    if (gg) { pp=ggcd(pax,xd0); h=isnonscalar(pp); if (h) pq=gdeuc(pax,pp); }
    else{ pp=gun; h=0; }
    do
    {
      if (h)
      {
        pa=pp; pb=pq; pp=ggcd(pa,deriv(pa,v)); h=isnonscalar(pp);
        if (h) pq=gdeuc(pa,pp); else pq=pa; ps=gdeuc(pb,pq);
      }
      else ps=pa;
          /* calcul des racines d'ordre exactement m */
      deg=lgef(ps)-3;
      if (deg)
      {
        l3=avma; e=gexpo((GEN)ps[deg+2]); emax=e;
        for (i=2; i<deg+2; i++)
        {
          p3=(GEN)(ps[i]);
          e1=gexpo(p3); if (e1>emax) emax=e1;
        }
        e=emax-e; if (e<0) e=0; avma=l3; if (ps!=pax) xd0=deriv(ps,v);
        xdabs=cgetg(deg+2,t_POL); xdabs[1]=xd0[1];
        for (i=2; i<deg+2; i++)
        {
          l3=avma; p3=(GEN)xd0[i];
          p4=gabs(greal(p3),l);
          p5=gabs(gimag(p3),l); l4=avma;
          xdabs[i]=lpile(l3,l4,gadd(p4,p5));
        }
        l0=avma; xc=gcopy(ps); xd=gcopy(xd0); l2=avma;
        for (i=1; i<=deg; i++)
        {
          if (i==deg)
          {
            p1=(GEN)y[k+m*i]; gdivz(gneg_i((GEN)xc[2]),(GEN)xc[3],p1);
            p14=(GEN)(p1[1]); p15=(GEN)(p1[2]);
          }
          else
          {
            p3=gshift(p2,e); p4=poleval(xc,p3); p5=gnorm(p4); exc=0;
            while (exc>= -20)
            {
              p6=poleval(xd,p3); p7=gneg_i(gdiv(p4,p6)); f=1;
              l3=avma;
              if (gcmp0(p5)) exc= -32;
              else exc=expo(gnorm(p7))-expo(gnorm(p3));
              avma=l3;
              for (j=1; j<=10 && f; j++)
              {
                p8=gadd(p3,p7); p9=poleval(xc,p8); p10=gnorm(p9);
                f=(cmprr(p10,p5)>=0)&&(exc>= -20);
                if (f){ gshiftz(p7,-2,p7); avma=l3; }
              }
              if (f)
              {
                avma=av1;
                if (DEBUGLEVEL)
                {
                  fprintferr("too many iterations in rootsold(): ");
                  fprintferr("using roots2()\n"); flusherr();
                }
                return roots2(x,l);
              }
              else
              {
                GEN *gptr[3];
                p3=p8; p4=p9; p5=p10;
                gptr[0]=&p3; gptr[1]=&p4; gptr[2]=&p5;
                gerepilemanysp(l2,l3,gptr,3);
              }
            }
            p1=(GEN)y[k+m*i]; setlg(p1[1],3); setlg(p1[2],3); gaffect(p3,p1);
            avma=l2; p14=(GEN)(p1[1]); p15=(GEN)(p1[2]);
            for (ln=4; ln<=l; ln=(ln<<1)-2)
            {
              setlg(p14,ln); setlg(p15,ln);
              if (gcmp0(p14)) { settyp(p14,t_INT); p14[1]=2; }
              if (gcmp0(p15)) { settyp(p15,t_INT); p15[1]=2; }
              p4=poleval(xc,p1);
              p5=poleval(xd,p1); p6=gneg_i(gdiv(p4,p5));
              settyp(p14,t_REAL); settyp(p15,t_REAL);
              gaffect(gadd(p1,p6),p1); avma=l2;
            }
          }
          setlg(p14,l); setlg(p15,l);
          p7=gcopy(p1); p14=(GEN)(p7[1]); p15=(GEN)(p7[2]);
          setlg(p14,l+1); setlg(p15,l+1);
          if (gcmp0(p14)) { settyp(p14,t_INT); p14[1]=2; }
          if (gcmp0(p15)) { settyp(p15,t_INT); p15[1]=2; }
          for (ii=1; ii<=5; ii++)
          {
            p4=poleval(ps,p7); p5=poleval(xd0,p7);
            p6=gneg_i(gdiv(p4,p5)); p7=gadd(p7,p6);
            p14=(GEN)(p7[1]); p15=(GEN)(p7[2]);
            if (gcmp0(p14)) { settyp(p14,t_INT); p14[1]=2; }
            if (gcmp0(p15)) { settyp(p15,t_INT); p15[1]=2; }
          }
          gaffect(p7,p1); p4=poleval(ps,p7);
          p6=gdiv(p4,poleval(xdabs,gabs(p7,l)));
          if (gexpo(p6)>=expmin)
          {
            avma=av1;
            if (DEBUGLEVEL)
            {
              fprintferr("internal error in rootsold(): using roots2()\n");
              flusherr();
            }
            return roots2(x,l);
          }
          avma=l2;
          if (expo(p1[2])<expmin && g)
          {
            gaffect(gzero,(GEN)p1[2]);
            for (j=1; j<m; j++) gaffect(p1,(GEN)y[k+(i-1)*m+j]);
            p11[2]=lneg((GEN)p1[1]);
            l4=avma; xc=gerepile(l0,l4,gdeuc(xc,p11));
          }
          else
          {
            for (j=1; j<m; j++) gaffect(p1,(GEN)y[k+(i-1)*m+j]);
            if (g)
            {
              p1=gconj(p1);
              for (j=1; j<=m; j++) gaffect(p1,(GEN)y[k+i*m+j]);
              i++;
              p12[2]=lnorm(p1); p12[3]=lmulsg(-2,(GEN)p1[1]); l4=avma;
              xc=gerepile(l0,l4,gdeuc(xc,p12));
            }
            else
            {
              p11[2]=lneg(p1); l4=avma;
              xc=gerepile(l0,l4,gdeuc(xc,p11));
            }
          }
          xd=deriv(xc,v); l2=avma;
        }
        k=k+deg*m;
      }
      m++;
    }
    while (k!=deg0);
  }
  avma=l1;
  if (deg0>1)
  {
    for (j=2; j<=deg0; j++)
    {
      p1=(GEN)y[j]; if (gcmp0((GEN)p1[2])) fr=0; else fr=1;
      for (k=j-1; k>=1; k--)
      {
        if (gcmp0((GEN)((GEN)y[k])[2])) f=0; else f=1;
        if (f<fr) break;
        if (f==fr && gcmp(gmael(y,k,1),(GEN)p1[1])<=0) break;
        y[k+1]=y[k];
      }
      y[k+1]=(long)p1;
    }
  }
  return y;
}

#if 0
GEN
rootslong(GEN x, long l)
{
  long av1=avma,i,j,f,g,fr,deg,l0,l1,l2,l3,l4,ln;
  long exc,expmin,m,deg0,k,ti,h,ii,e,e1,emax,v;
  GEN y,xc,xd0,xd,xdabs,p1,p2,p3,p4,p5,p6,p7,p8;
  GEN p9,p10,p11,p12,p14,p15,pa,pax,pb,pp,pq,ps;

  if (typ(x)!=t_POL) err(typeer,"rootslong");
  v=varn(x); deg0=lgef(x)-3; expmin = -bit_accuracy(l)+12;
  if (!signe(x)) err(zeropoler,"rootslong");
  y=cgetg(deg0+1,t_COL); if (!deg0) return y;
  for (i=1; i<=deg0; i++)
  {
    p1=cgetg(3,t_COMPLEX); y[i]=(long)p1;
    p1[1]=lgetr(l); p1[2]=lgetr(l);
    for (j=3; j<l; j++) mael(p1,2,j)=mael(p1,1,j)=0;
  }
  g=1; f=1;
  for (i=2; i<=deg0+2; i++)
  {
    ti=typ(x[i]);
    if (ti==t_QUAD)
    {
      p2=gmael3(x,i,1,2);
      if (gcmpgs(p2,0)>0) g=0;
    }
    else
      if (!is_const_t(ti) || ti==t_PADIC || ti==t_COMPLEX) g=0;
  }
  l1=avma; p2=cgetg(3,t_COMPLEX);
  p2[1]=lmppi(l);
  p2[2]=ldivrs((GEN)p2[1],10);
  p11=cgetg(4,t_POL); p11[1]=evalsigne(1)+evallgef(4); setvarn(p11,v); p11[3]=un;
  p12=cgetg(5,t_POL); p12[1]=evalsigne(1)+evallgef(5); setvarn(p12,v); p12[4]=un;
  for (i=2; (i<=deg0+2)&&(gcmp0((GEN)x[i])); i++)
    gaffsg(0,(GEN)y[i-1]); k=i-2;
  if (k!=deg0)
  {
    if (k)
    {
      j=deg0+3-k; pax=cgetg(j,t_POL); pax[1]=evalsigne(1)+evallgef(j);
      setvarn(pax,v);
      for (i=2; i<j; i++)
        pax[i]=x[i+k];
    }
    else pax=x;
    xd0=deriv(pax,v); pp=ggcd(pax,xd0); m=1; pa=pax;
    h=isnonscalar(pp); if (h) pq=gdeuc(pax,pp);
    do
    {
      if (h)
      {
        pa=pp; pb=pq;
        pp=ggcd(pa,deriv(pa,v)); h=isnonscalar(pp);
        if (h) pq=gdeuc(pa,pp); else pq=pa;
        ps=gdeuc(pb,pq);
      }
      else ps=pa;
          /* calcul des racines d'ordre exactement m */
      deg=lgef(ps)-3;
      if (deg)
      {
        l3=avma; e=gexpo((GEN)ps[deg+2]); emax=e;
        for (i=2; i<deg+2; i++)
        {
          p3=(GEN)(ps[i]);
          if (!gcmp0(p3))
          {
            e1=gexpo(p3);
            if (e1>emax) emax=e1;
          }
        }
        e=emax-e; if (e<0) e=0; avma=l3;
        if (ps!=pax) xd0=deriv(ps,v);
        xdabs=cgetg(deg+2,t_POL); xdabs[1]=xd0[1];
        for (i=2; i<deg+2; i++)
        {
          l3=avma; p3=(GEN)xd0[i]; p4=gabs(greal(p3),l);
          p5=gabs(gimag(p3),l); l4=avma;
          xdabs[i]=lpile(l3,l4,gadd(p4,p5));
        }
        l0=avma; xc=gcopy(ps); xd=gcopy(xd0); l2=avma;
        for (i=1; i<=deg; i++)
        {
          if (i==deg)
          {
            p1=(GEN)y[k+m*i];
            gdivz(gneg_i((GEN)xc[2]),(GEN)xc[3],p1);
            p14=(GEN)(p1[1]); p15=(GEN)(p1[2]);
          }
          else
          {
            p3=gshift(p2,e); p4=poleval(xc,p3);
            p5=gnorm(p4); exc=0;
            while (exc>= -20)
            {
              p6=poleval(xd,p3); p7=gneg_i(gdiv(p4,p6));
              f=1; l3=avma; if (gcmp0(p5)) exc= -32;
              else exc=expo(gnorm(p7))-expo(gnorm(p3));
              avma=l3;
              for (j=1; (j<=50)&&f; j++)
              {
                p8=gadd(p3,p7); p9=poleval(xc,p8);
                p10=gnorm(p9);
                f=(cmprr(p10,p5)>=0)&&(exc>= -20);
                if (f) { gshiftz(p7,-2,p7); avma=l3; }
              }
              if (f) err(poler9);
              else
              {
                GEN *gptr[3];
                p3=p8; p4=p9; p5=p10;
                gptr[0]=&p3; gptr[1]=&p4; gptr[2]=&p5;
                gerepilemanysp(l2,l3,gptr,3);
              }
            }
            p1=(GEN)y[k+m*i]; gaffect(p3,p1); avma=l2;
            p14=(GEN)(p1[1]); p15=(GEN)(p1[2]);
            for (ln=4; ln<=l; ln=(ln<<1)-2)
            {
              if (gcmp0(p14))
              { settyp(p14,t_INT); p14[1]=2; }
              if (gcmp0(p15))
              { settyp(p15,t_INT); p15[1]=2; }
              p4=poleval(xc,p1); p5=poleval(xd,p1);
              p6=gneg_i(gdiv(p4,p5));
              settyp(p14,t_REAL); settyp(p15,t_REAL);
              gaffect(gadd(p1,p6),p1); avma=l2;
            }
          }
          p7=gcopy(p1);
          p14=(GEN)(p7[1]); p15=(GEN)(p7[2]);
          setlg(p14,l+1); setlg(p15,l+1);
          if (gcmp0(p14))
          { settyp(p14,t_INT); p14[1]=2; }
          if (gcmp0(p15))
          { settyp(p15,t_INT); p15[1]=2; }
          for (ii=1; ii<=max(32,((e<<TWOPOTBITS_IN_LONG)+2)); ii<<=1)
          {
            p4=poleval(ps,p7); p5=poleval(xd0,p7);
            p6=gneg_i(gdiv(p4,p5)); p7=gadd(p7,p6);
            p14=(GEN)(p7[1]); p15=(GEN)(p7[2]);
            if (gcmp0(p14))
            { settyp(p14,t_INT); p14[1]=2; }
            if (gcmp0(p15))
            { settyp(p15,t_INT); p15[1]=2; }
          }
          gaffect(p7,p1); p4=poleval(ps,p7);
          p6=gdiv(p4,poleval(xdabs,gabs(p7,l)));
          if ((!gcmp0(p6))&&(gexpo(p6)>=expmin))
          {
            avma=av1;
            if (DEBUGLEVEL)
            {
              fprintferr("internal error in roots: using roots2\n"); flusherr();
            }
            return roots2(x,l);
          }
          avma=l2;
          if ((expo(p1[2])<expmin)&&g)
          {
            gaffect(gzero,(GEN)p1[2]);
            for (j=1; j<m; j++)
              gaffect(p1,(GEN)y[k+(i-1)*m+j]);
            p11[2]=lneg((GEN)p1[1]); l4=avma;
            xc=gerepile(l0,l4,gdeuc(xc,p11));
          }
          else
          {
            for (j=1; j<m; j++)
              gaffect(p1,(GEN)y[k+(i-1)*m+j]);
            if (g)
            {
              p1=gconj(p1);
              for (j=1; j<=m; j++)
                gaffect(p1,(GEN)y[k+i*m+j]); i++;
              p12[2]=lnorm(p1);
              p12[3]=lmulsg(-2,(GEN)p1[1]);
              l4=avma;
              xc=gerepile(l0,l4,gdeuc(xc,p12));
            }
            else
            {
              p11[2]=lneg(p1); l4=avma;
              xc=gerepile(l0,l4,gdeuc(xc,p11));
            }
          }
          xd=deriv(xc,v); l2=avma;
        }
        k=k+deg*m;
      }
      m++;
    }
    while (k!=deg0);
  }
  avma=l1;
  if (deg0>1)
  {
    for (j=2; j<=deg0; j++)
    {
      p1=(GEN)y[j]; if (gcmp0((GEN)p1[2])) fr=0; else fr=1;
      for (k=j-1; k>=1; k--)
      {
        if (gcmp0((GEN)((GEN)y[k])[2])) f=0; else f=1;
        if (f<fr) break;
        if ((f==fr)&&(gcmp((GEN)((GEN)y[k])[1],(GEN)p1[1])<=0)) break;
        y[k+1]=y[k];
      }
      y[k+1]=(long)p1;
    }
  }
  return y;
}
#endif

GEN
roots2(GEN pol,long PREC)
{
  long av = avma,tetpil,N,flagexactpol,flagrealpol,flagrealrac,ti,i,j;
  long nbpol,k,av1,multiqol,deg,nbroot,fr,f;
  GEN p1,p2,rr,EPS,qol,qolbis,x,b,c,*ad,v,tabqol;

  if (typ(pol)!=t_POL) err(typeer,"roots2");
  if (!signe(pol)) err(zeropoler,"roots2");
  N=lgef(pol)-3;
  if (!N) return cgetg(1,t_COL);
  if (N==1)
  {
    p1=gmul(realun(PREC),(GEN)pol[3]);
    p2=gneg_i(gdiv((GEN)pol[2],p1));
    tetpil=avma; return gerepile(av,tetpil,gcopy(p2));
  }
  EPS=realun(3); setexpo(EPS, 12 - bit_accuracy(PREC));
  flagrealpol=1; flagexactpol=1;
  for (i=2; i<=N+2; i++)
  {
    ti=typ(pol[i]);
    if (ti!=t_INT && ti!=t_INTMOD && !is_frac_t(ti))
    {
      flagexactpol=0;
      if (ti!=t_REAL) flagrealpol=0;
    }
    if (ti==t_QUAD)
    {
      p1=gmael3(pol,i,1,2);
      flagrealpol = (gsigne(p1)>0)? 0 : 1;
    }
  }
  rr=cgetg(N+1,t_COL);
  for (i=1; i<=N; i++)
  {
    rr[i]=lgetg(3,t_COMPLEX); p1=(GEN)rr[i];
    mael(rr,i,1)=lgetr(PREC); mael(rr,i,2)=lgetr(PREC);
    for (j=3; j<PREC; j++) mael(p1,2,j)=mael(p1,1,j)=0;
  }
  if (flagexactpol) tabqol=square_free_factorization(pol);
  else
  {
    tabqol=cgetg(3,t_MAT);
    tabqol[1]=lgetg(2,t_COL); mael(tabqol,1,1)=un;
    tabqol[2]=lgetg(2,t_COL); mael(tabqol,2,1)=lcopy(pol);
  }
  nbpol=lg(tabqol[1])-1; nbroot=0;
  for (k=1; k<=nbpol; k++)
  {
    av1=avma; qol=gmael(tabqol,2,k); qolbis=gcopy(qol);
    multiqol=itos(gmael(tabqol,1,k)); deg=lgef(qol)-3;
    for (j=deg; j>=1; j--)
    {
      x=gzero; flagrealrac=0;
      if (j==1) x=gneg_i(gdiv((GEN)qolbis[2],(GEN)qolbis[3]));
      else
      {
        x=laguer(qolbis,j,x,EPS,PREC);
        if (x == NULL) goto RLAB;
      }
      if (flagexactpol)
      {
        x=gprec(x,(long)((PREC-1)*pariK));
        x=laguer(qol,deg,x,gmul2n(EPS,-32),PREC+1);
      }
      else x=laguer(qol,deg,x,EPS,PREC);
      if (x == NULL) goto RLAB;

      if (typ(x)==t_COMPLEX &&
          gcmp(gabs(gimag(x),PREC),gmul2n(gmul(EPS,gabs(greal(x),PREC)),1))<=0)
        { x[2]=zero; flagrealrac=1; }
      else if (j==1 && flagrealpol)
        { x[2]=zero; flagrealrac=1; }
      else if (typ(x)!=t_COMPLEX) flagrealrac=1;

      for (i=1; i<=multiqol; i++) gaffect(x,(GEN)rr[nbroot+i]);
      nbroot+=multiqol;
      if (!flagrealpol || flagrealrac)
      {
        ad = (GEN*) new_chunk(j+1);
        for (i=0; i<=j; i++) ad[i]=(GEN)qolbis[i+2];
        b=(GEN)ad[j];
        for (i=j-1; i>=0; i--)
        {
          c=(GEN)ad[i]; ad[i]=b;
          b=gadd(gmul((GEN)rr[nbroot],b),c);
        }
        v=cgetg(j+1,t_VEC); for (i=1; i<=j; i++) v[i]=(long)ad[j-i];
        qolbis=gtopoly(v,varn(qolbis));
        if (flagrealpol)
          for (i=2; i<=j+1; i++)
            if (typ(qolbis[i])==t_COMPLEX) mael(qolbis,i,2)=zero;
      }
      else
      {
        ad = (GEN*) new_chunk(j-1); ad[j-2]=(GEN)qolbis[j+2];
        p1=gmulsg(2,greal((GEN)rr[nbroot])); p2=gnorm((GEN)rr[nbroot]);
        ad[j-3]=gadd((GEN)qolbis[j+1],gmul(p1,ad[j-2]));
        for (i=j-2; i>=2; i--)
          ad[i-2] = gadd((GEN)qolbis[i+2],gsub(gmul(p1,ad[i-1]),gmul(p2,ad[i])));
        v=cgetg(j,t_VEC); for (i=1; i<=j-1; i++) v[i]=(long)ad[j-1-i];
        qolbis=gtopoly(v,varn(qolbis));
        for (i=2; i<=j; i++)
          if (typ(qolbis[i])==t_COMPLEX) mael(qolbis,i,2)=zero;
        for (i=1; i<=multiqol; i++)
          gaffect(gconj((GEN)rr[nbroot]), (GEN)rr[nbroot+i]);
        nbroot+=multiqol; j--;
      }
    }
    avma=av1;
  }
  for (j=2; j<=N; j++)
  {
    x=(GEN)rr[j]; if (gcmp0((GEN)x[2])) fr=0; else fr=1;
    for (i=j-1; i>=1; i--)
    {
      if (gcmp0(gmael(rr,i,2))) f=0; else f=1;
      if (f<fr) break;
      if (f==fr && gcmp(greal((GEN)rr[i]),greal(x)) <= 0) break;
      rr[i+1]=rr[i];
    }
    rr[i+1]=(long)x;
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(rr));

 RLAB:
  avma=av;
  for(i=2;i<=N+2;i++)
  {
    ti=typ(pol[i]);
    if (is_intreal_t(ti) || ti==t_INTMOD) err(poler9);
  }
  if (DEBUGLEVEL)
  {
    fprintferr("too many iterations in roots2() ( laguer() ): \n");
    fprintferr("     real coefficients polynomial, using zrhqr()\n");
    flusherr();
  }
  return zrhqr(pol,PREC);
}

#define MR 8
#define MT 10

static GEN
laguer(GEN pol,long N,GEN y0,GEN EPS,long PREC)
{
  long av = avma, av1,MAXIT,iter,i,j;
  GEN rac,erre,I,x,abx,abp,abm,dx,x1,b,d,f,g,h,sq,gp,gm,g2,*ffrac;

  MAXIT=MR*MT; rac=cgetg(3,t_COMPLEX);
  rac[1]=lgetr(PREC); rac[2]=lgetr(PREC);
  av1 = avma;
  I=cgetg(3,t_COMPLEX); I[1]=un; I[2]=un;
  ffrac=(GEN*)new_chunk(MR+1); for (i=0; i<=MR; i++) ffrac[i]=cgetr(PREC);
  affrr(dbltor(0.0), ffrac[0]); affrr(dbltor(0.5), ffrac[1]);
  affrr(dbltor(0.25),ffrac[2]); affrr(dbltor(0.75),ffrac[3]);
  affrr(dbltor(0.13),ffrac[4]); affrr(dbltor(0.38),ffrac[5]);
  affrr(dbltor(0.62),ffrac[6]); affrr(dbltor(0.88),ffrac[7]);
  affrr(dbltor(1.0),ffrac[8]);
  x=y0;
  for (iter=1; iter<=MAXIT; iter++)
  {
    b=(GEN)pol[N+2]; erre=gnorml1(b,PREC);
    d=gzero; f=gzero; abx=gnorml1(x,PREC);
    for (j=N-1; j>=0; j--)
    {
      f=gadd(gmul(x,f),d); d=gadd(gmul(x,d),b);
      b=gadd(gmul(x,b),(GEN)pol[j+2]);
      erre=gadd(gnorml1(b,PREC),gmul(abx,erre));
    }
    erre=gmul(erre,EPS);
    if (gcmp(gnorml1(b,PREC),erre)<=0)
    {
      gaffect(x,rac); avma = av1; return rac;
    }
    g=gdiv(d,b); g2=gsqr(g); h=gsub(g2, gmul2n(gdiv(f,b),1));
    sq=gsqrt(gmulsg(N-1,gsub(gmulsg(N,h),g2)),PREC);
    gp=gadd(g,sq); gm=gsub(g,sq); abp=gnorm(gp); abm=gnorm(gm);
    if (gcmp(abp,abm)<0) gp=gcopy(gm);
    if (gsigne(gmax(abp,abm))==1)
      dx = gdivsg(N,gp);
    else
      dx = gmul(gadd(gun,abx),gexp(gmulgs(I,iter),PREC));
    x1=gsub(x,dx);
    if (gcmp(gnorml1(gsub(x,x1),PREC),EPS)<0)
    {
      gaffect(x,rac); avma = av1; return rac;
    }
    if (iter%MT) x=gcopy(x1); else x=gsub(x,gmul(ffrac[iter/MT],dx));
  }
  avma=av; return NULL;
}

#undef MR
#undef MT

static GEN
gnorml1(GEN x,long PREC)
{
  long av,tetpil,lx,i;
  GEN p1,p2,s;
  av=avma;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return gabs(x,PREC);

    case t_INTMOD: case t_PADIC: case t_POLMOD: case t_POL:
    case t_SER: case t_RFRAC: case t_RFRACN: case t_QFR: case t_QFI:
      return gcopy(x);

    case t_COMPLEX:
      p1=gabs((GEN)x[1],PREC); p2=gabs((GEN)x[2],PREC); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,p2));

    case t_QUAD:
      p1=gabs((GEN)x[2],PREC); p2=gabs((GEN)x[3],PREC); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,p2));

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); s=gzero;
      for (i=1; i<lx; i++) s=gadd(s,gnorml1((GEN)x[i],PREC)); tetpil=avma;
      return gerepile(av,tetpil,gcopy(s));
  }
  err(talker,"not a PARI object in gnorml1");
  return NULL; /* not reached */
}

/***********************************************************************/
/**                                                                   **/
/**                     RACINES D'UN POLYNOME                         **/
/**                     A COEFFICIENTS REELS                          **/
/**                                                                   **/
/***********************************************************************/

#define RADIX 1
#define COF 0.95

/* ONLY FOR REAL COEFFICIENTS MATRIX : replace the matrix x with
   a symmetric matrix a with the same eigenvalues */
static GEN
balanc(GEN x)
{
  long av,tetpil,n,last,j,i,sqrdx;
  GEN s,r,g,f,c,cofgen,a;

  av=avma; a=gcopy(x); n=lg(a)-1; sqrdx=RADIX+RADIX; last=0; cofgen=dbltor(COF);
  while (!last)
  {
    last=1;
    for (i=1; i<=n; i++)
    {
      r=c=gzero;
      for (j=1; j<=n; j++)
        if (j!=i){ c=gadd(gabs(gcoeff(a,j,i),0),c); r=gadd(gabs(gcoeff(a,i,j),0),r); }
        if ((!gcmp0(r))&&(!gcmp0(c)))
        {
          g=gmul2n(r,-RADIX); f=gun; s=gadd(c,r);
          while (gcmp(c,g)<0){ f=gmul2n(f,RADIX); c=gmul2n(c,sqrdx); }
          g=gmul2n(r,RADIX);
          while (gcmp(c,g)>0){ f=gmul2n(f,-RADIX); c=gmul2n(c,-sqrdx); }
          if (gcmp(gdiv(gadd(c,r),f),gmul(cofgen,s))<0)
          {
            last=0; g=ginv(f);
            for (j=1; j<=n; j++) coeff(a,i,j)=lmul(gcoeff(a,i,j),g);
            for (j=1; j<=n; j++) coeff(a,j,i)=lmul(gcoeff(a,j,i),f);
          }
        }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(a));
}

#define SIGN(a,b) ((b)>=0.0 ? fabs(a) : -fabs(a))
static GEN
hqr(GEN mat) /* find all the eigenvalues of the matrix mat */
{
  long nn,n,m,l,k,j,its,i,mmin,flj,flk;
  double **a,p,q,r,s,t,u,v,w,x,y,z,anorm,*wr,*wi,eps;
  GEN eig;

  eps=0.000001;
  n=lg(mat)-1; a=(double**)gpmalloc(sizeof(double*)*(n+1));
  for (i=1; i<=n; i++) a[i]=(double*)gpmalloc(sizeof(double)*(n+1));
  for (j=1; j<=n; j++)
    for (i=1; i<=n; i++) a[i][j]=gtodouble((GEN)((GEN)mat[j])[i]);
  wr=(double*)gpmalloc(sizeof(double)*(n+1));
  wi=(double*)gpmalloc(sizeof(double)*(n+1));

  anorm=fabs(a[1][1]);
  for (i=2; i<=n; i++) for (j=(i-1); j<=n; j++) anorm+=fabs(a[i][j]);
  nn=n; t=0.0;
  if (DEBUGLEVEL>3)
  { fprintferr("* Finding eigenvalues\n"); flusherr(); }
  while (nn>=1)
  {
    its=0;
    do
    {
      for (l=nn; l>=2; l--)
      {
        s=fabs(a[l-1][l-1])+fabs(a[l][l]); if (s==0.0) s=anorm;
        if ((double)(fabs(a[l][l-1])+s)==s) break;
      }
      x=a[nn][nn];
      if (l==nn){ wr[nn]=x+t; wi[nn--]=0.0; }
      else
      {
        y=a[nn-1][nn-1]; w=a[nn][nn-1]*a[nn-1][nn];
        if (l==(nn-1))
        {
          p=0.5*(y-x); q=p*p+w; z=sqrt(fabs(q)); x+=t;
          if ((q>=0.0)||(fabs(q)<=eps))
          {
            z=p+SIGN(z,p); wr[nn-1]=wr[nn]=x+z;
            if (fabs(z)>eps) wr[nn]=x-w/z;
            wi[nn-1]=wi[nn]=0.0;
          }
          else{ wr[nn-1]=wr[nn]=x+p; wi[nn-1]=-(wi[nn]=z); }
          nn-=2;
        }
        else
        {
          if (its==30) err(talker,"too many iterations in hqr");
          if ((its==10)||(its==20))
          {
            t+=x; for (i=1; i<=nn; i++) a[i][i]-=x; s=fabs(a[nn][nn-1])+fabs(a[nn-1][nn-2]);
            y=x=0.75*s; w=-0.4375*s*s;
          }
          ++its;
          for (m=(nn-2); m>=l; m--)
          {
            z=a[m][m]; r=x-z; s=y-z; p=(r*s-w)/a[m+1][m]+a[m][m+1]; q=a[m+1][m+1]-z-r-s;
            r=a[m+2][m+1]; s=fabs(p)+fabs(q)+fabs(r); p/=s; q/=s; r/=s;
            if (m==l) break;
            u=fabs(a[m][m-1])*(fabs(q)+fabs(r));
            v=fabs(p)*(fabs(a[m-1][m-1])+fabs(z)+fabs(a[m+1][m+1]));
            if ((double)(u+v)==v) break;
          }
          for (i=m+2; i<=nn; i++){ a[i][i-2]=0.0; if (i!=(m+2)) a[i][i-3]=0.0; }
          for (k=m; k<=nn-1; k++)
          {
            if (k!=m)
            {
              p=a[k][k-1]; q=a[k+1][k-1]; r=0.0; if (k!=(nn-1)) r=a[k+2][k-1];
              if ((x=fabs(p)+fabs(q)+fabs(r))!=0.0){ p/=x; q/=x; r/=x; }
            }
            if ((s=SIGN(sqrt(p*p+q*q+r*r),p))!=0.0)
            {
              if (k==m){ if (l!=m) a[k][k-1]=-a[k][k-1]; }else a[k][k-1]=-s*x;
              p+=s; x=p/s; y=q/s; z=r/s; q/=p; r/=p;
              for (j=k; j<=nn; j++)
              {
                p=a[k][j]+q*a[k+1][j]; if (k!=(nn-1)){ p+=r*a[k+2][j]; a[k+2][j]-=p*z; }
                a[k+1][j]-=p*y; a[k][j]-=p*x;
              }
              mmin=(nn<k+3) ? nn : k+3;
              for (i=l; i<=mmin; i++)
              {
                p=x*a[i][k]+y*a[i][k+1]; if (k!=(nn-1)){ p+=z*a[i][k+2]; a[i][k+2]-=p*r; }
                a[i][k+1]-=p*q; a[i][k]-=p;
              }
            }
          }
        }
      }
    }
    while (l<nn-1);
  }
  for (j=2; j<=n; j++) /* ordering the roots */
  {
    x=wr[j]; y=wi[j]; if (y) flj=1; else flj=0;
    for (k=j-1; k>=1; k--)
    {
      if (wi[k]) flk=1; else flk=0;
      if (flk<flj) break;
      if ((!flk)&&(!flj)&&(wr[k]<=x)) break;
      if (flk&&flj&&(wr[k]<x)) break;
      if (flk&&flj&&(wr[k]==x)&&(wi[k]>0)) break;
      wr[k+1]=wr[k]; wi[k+1]=wi[k];
    }
    wr[k+1]=x; wi[k+1]=y;
  }
  if (DEBUGLEVEL>3)
  { fprintferr("* End of the computation of eigenvalues\n"); flusherr(); }
  for (i=1; i<=n; i++) free(a[i]); free(a); eig=cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    if (wi[i])
    {
      eig[i]=lgetg(3,t_COMPLEX);
      ((GEN)eig[i])[1]=(long)dbltor(wr[i]); ((GEN)eig[i])[2]=(long)dbltor(wi[i]);
    }
    else eig[i]=(long)dbltor(wr[i]);
  }
  free(wr); free(wi); return eig;
}

static GEN
zrhqr(GEN a,long PREC)
/*    ONLY FOR POLYNOMIAL WITH REAL COEFFICIENTS : give the roots of
 *  the polynomial a (first, the real roots, then the
 *  non real roots) in increasing order of their real
 *  parts MULTIPLE ROOTS ARE FORBIDDEN.
 */
{
  long av,tetpil,n,i,j,k,ct,prec;
  GEN aa,b,p1,rt,rr,hess,x,dx,y,hessbis,eps,newval;
  GEN oldval = NULL; /* for lint */

  av=avma; n=lgef(a)-3; prec=PREC;
  hess=cgetg(n+1,t_MAT); for (k=1; k<=n; k++) hess[k]=lgetg(n+1,t_COL);
  for (k=1; k<=n; k++)
  {
    p1=(GEN)hess[k]; p1[1]=lneg(gdiv((GEN)a[n-k+2],(GEN)a[n+2]));
    for (j=2; j<=n; j++){ if (j==(k+1)) p1[j]=un; else p1[j]=zero; }
  }
  rr=cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    rr[i]=lgetg(3,t_COMPLEX);
    mael(rr,i,1)=lgetr(PREC);
    mael(rr,i,2)=lgetr(PREC);
  }
  hessbis=balanc(hess); rt=hqr(hessbis);
  eps=cgetr(prec);
  p1=gpuigs(gdeux,-bit_accuracy(prec)); gaffect(p1,eps);
  prec=2*PREC; /* polishing the roots */
  aa=cgetg(n+3,t_POL); aa[1]=a[1];
  for (i=2; i<=n+2; i++){ aa[i]=lgetr(prec); gaffect((GEN)a[i],(GEN)aa[i]); }
  b=deriv(aa,varn(aa));
  for (i=1; i<=n; i++)
  {
    ct=0;
    if (typ(rt[i])==t_REAL) { x=cgetr(prec); affrr((GEN)rt[i],x); }
    else
    {
      x=cgetg(3,t_COMPLEX);
      x[1]=lgetr(prec); affrr(gmael(rt,i,1),(GEN)x[1]);
      x[2]=lgetr(prec); affrr(gmael(rt,i,2),(GEN)x[2]);
    }
  LAB1:
    dx=poleval(b,x);
    if (gcmp(gabs(dx,prec),eps) <= 0)
      err(talker,"the polynomial has probably multiple roots in zrhqr");
    y=gsub(x,gdiv(poleval(aa,x),dx));
    newval=gabs(poleval(aa,y),prec);
    if (gcmp(newval,eps) > 0 && (!ct || gcmp(newval,oldval) < 0))
    {
      ct++; oldval=newval; x=y;
      goto LAB1;
    }
    gaffect(y,(GEN)rr[i]);
  }
  if (DEBUGLEVEL>3){ fprintferr("polished roots = %Z",rr); flusherr(); }
  tetpil=avma; return gerepile(av,tetpil,gcopy(rr));
}
