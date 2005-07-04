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

/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                         (first part)                            **/
/**                                                                 **/
/*********************************************************************/
#include "pari.h"
#include "paripriv.h"

/*********************************************************************/
/**                                                                 **/
/**                  ARITHMETIC FUNCTION PROTOTYPES                 **/
/**                                                                 **/
/*********************************************************************/
GEN
garith_proto(GEN f(GEN), GEN x, int do_error)
{
  long tx = typ(x), lx, i;
  GEN y;
  if (is_matvec_t(tx))
  {
    lx = lg(x); y = cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i] = (long)garith_proto(f, (GEN)x[i], do_error);
    return y;
  }
  if (tx != t_INT && do_error) err(arither1);
  return f(x);
}

GEN
arith_proto(long f(GEN), GEN x, int do_error)
{
  long tx = typ(x), lx, i;
  GEN y;
  if (is_matvec_t(tx))
  {
    lx = lg(x); y = cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i] = (long)arith_proto(f, (GEN)x[i], do_error);
    return y;
  }
  if (tx != t_INT && do_error) err(arither1);
  return stoi(f(x));
}

GEN
arith_proto2(long f(GEN,GEN), GEN x, GEN n)
{
  long l,i,tx = typ(x);
  GEN y;
  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i] = (long)arith_proto2(f,(GEN) x[i],n);
    return y;
  }
  if (tx != t_INT) err(arither1);
  tx=typ(n);
  if (is_matvec_t(tx))
  {
    l = lg(n); y = cgetg(l,tx);
    for (i=1; i<l; i++) y[i] = (long)arith_proto2(f,x,(GEN) n[i]);
    return y;
  }
  if (tx != t_INT) err(arither1);
  return stoi(f(x,n));
}

GEN
arith_proto2gs(long f(GEN,long), GEN x, long y)
{
  long l, i, tx = typ(x);
  GEN t;

  if (is_matvec_t(tx))
  {
    l=lg(x); t=cgetg(l,tx);
    for (i=1; i<l; i++) t[i]= (long)arith_proto2gs(f,(GEN) x[i],y);
    return t;
  }
  if (tx != t_INT) err(arither1);
  return stoi(f(x,y));
}

GEN
garith_proto2gs(GEN f(GEN,long), GEN x, long y)
{
  long l, i, tx = typ(x);
  GEN t;

  if (is_matvec_t(tx))
  {
    l = lg(x); t = cgetg(l,tx);
    for (i=1; i<l; i++) t[i] = (long)garith_proto2gs(f,(GEN) x[i],y);
    return t;
  }
  if (tx != t_INT) err(arither1);
  return f(x,y);
}

GEN
gassoc_proto(GEN f(GEN,GEN), GEN x, GEN y)
{
  if (!y)
  {
    pari_sp av = avma;
    long tx = typ(x);
    if (!is_vec_t(tx)) err(typeer,"association");
    return gerepileupto(av, divide_conquer_prod(x,f));
  }
  return f(x,y);
}

/*********************************************************************/
/**                                                                 **/
/**               ORDER of INTEGERMOD x  in  (Z/nZ)*                **/
/**                                                                 **/
/*********************************************************************/

GEN
znorder(GEN x, GEN o)
{
  pari_sp av = avma;
  long i, e;
  GEN m, p, b = gel(x,1), a = gel(x,2);

  if (typ(x) != t_INTMOD || !gcmp1(gcdii(a,b)))
    err(talker,"not an element of (Z/nZ)* in order");
  if (!o)
    o = phi(b); 
  else if(typ(o) != t_INT) err(arither1);

  m = decomp(o);
  for (i = lg(m[1])-1; i; i--)
  {
    p = gcoeff(m,i,1); e = itos(gcoeff(m,i,2));
    do
    {
      GEN o1 = diviiexact(o,p), y = Fp_pow(a, o1, b);
      if (!is_pm1(y)) break;
      e--; o = o1;
    }
    while (e);
  }
  return gerepilecopy(av, o);
}
GEN
order(GEN x) { return znorder(x, NULL); }

/******************************************************************/
/*                                                                */
/*                 GENERATOR of (Z/mZ)*                           */
/*                                                                */
/******************************************************************/

GEN
ggener(GEN m)
{
  return garith_proto(gener,m,1);
}

/* assume p prime */
ulong
gener_Fl_local(ulong p, GEN L0)
{
  const pari_sp av = avma;
  const ulong q = p - 1;
  int i, x, k ;
  GEN L;
  if (p == 2) return 1;

  if (!L0) {
    L0 = L = gel(factoru(q), 1);
    k = lg(L)-1;
  } else {
    k = lg(L0)-1;
    L = cgetg(k + 1, t_VECSMALL);
  }

  for (i=1; i<=k; i++) L[i] = q / (ulong)L0[i];
  for (x=2;;x++)
    if (x % p)
    {
      for (i=k; i; i--)
	if (Fl_pow(x, (ulong)L[i], p) == 1) break;
      if (!i) break;
    }
  avma = av; return x;
}
ulong
gener_Fl(ulong p) { return gener_Fl_local(p, NULL); }

/* assume p prime, return a generator of all L[i]-Sylows in F_p^*. */
GEN
gener_Fp_local(GEN p, GEN L0)
{
  pari_sp av0 = avma;
  long k, i;
  GEN x, q, L;
  if (equaliu(p, 2)) return gen_1;
  if (lgefint(p) == 3)
  {
    ulong z;
    if (L0) L0 = ZV_to_nv(L0);
    z = gener_Fl_local((ulong)p[2], L0);
    avma = av0; return utoipos(z);
  }

  q = subis(p, 1);
  if (!L0) {
    L0 = L = gel(decomp(q), 1);
    k = lg(L)-1;
  } else {
    k = lg(L0)-1;
    L = cgetg(k + 1, t_VEC);
  }

  for (i=1; i<=k; i++) L[i] = (long)diviiexact(q, (GEN)L0[i]);
  x = utoipos(2);
  for (;; x[2]++)
  {
    GEN d = gcdii(p,x);
    if (!is_pm1(d)) continue;
    for (i = k; i; i--) {
      GEN e = Fp_pow(x, (GEN)L[i], p);
      if (is_pm1(e)) break;
    }
    if (!i) { avma = av0; return utoipos((ulong)x[2]); }
  }
}

GEN
gener_Fp(GEN p) { return gener_Fp_local(p, NULL); }

/* p prime, e > 0. Return a primitive root modulo p^e */
static GEN
Zpn_gener(GEN p, long e)
{
  GEN x;
  if (equaliu(p, 2))
    switch(e)
    {
      case 1: return gen_1;
      case 2: return utoipos(3);
      default: err(talker,"primitive root mod 2^%ld does not exist", e);
    }
  x = gener_Fp(p);
  if (e > 1)
  {
    GEN y = Fp_pow(x, subis(p,1), sqri(p));
    if (is_pm1(y)) x = addii(x,p); else avma = (pari_sp)x;
  }
  return x;
}

GEN
gener(GEN m)
{
  pari_sp av;
  long e;
  GEN x, t, p, z;

  if (typ(m) != t_INT) err(arither1);
  if (!signe(m)) err(talker,"zero modulus in znprimroot");
  if (is_pm1(m)) return mkintmodu(0,1);
  z = cgetg(3, t_INTMOD);
  m = absi(m);
  z[1] = (long)m; av = avma;

  e = mod4(m);
  if (e == 0) /* m = 0 mod 4 */
  { /* m != 4, non cyclic */
    if (!equaliu(m,4)) err(talker,"primitive root mod %Z does not exist", m);
    z[2] = (long)utoipos(3); return z;
  }
  if (e == 2) /* m = 0 mod 2 */
  {
    GEN q = shifti(m,-1); x = (GEN) gener(q)[2];
    if (!mod2(x)) x = addii(x,q);
    z[2] = lpileuptoint(av, x); return z;
  }

  t = decomp(m);
  if (lg(t[1]) != 2) err(talker,"primitive root mod %Z does not exist", m);
  p = gcoeff(t,1,1);
  e = itos(gcoeff(t,1,2));
  z[2] = lpileuptoint(av, Zpn_gener(p, e)); return z;
}

GEN
znstar(GEN n)
{
  GEN z, P, E, cyc, gen, mod;
  long i, j, nbp, sizeh;
  pari_sp av;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n))
  {
    z = cgetg(4,t_VEC);
    z[1] = (long)gen_2;
    z[2] = (long)mkvec(gen_2);
    z[3] = (long)mkvec(gen_m1); return z;
  }
  if (cmpiu(n,2) <= 0)
  {
    z = cgetg(4,t_VEC);
    z[1] = (long)gen_1;
    z[2] = lgetg(1,t_VEC);
    z[3] = lgetg(1,t_VEC); return z;
  }
  av = avma; if (signe(n) < 0) n = negi(n);
  z = decomp(n);
  P = (GEN)z[1];
  E = (GEN)z[2]; nbp = lg(P)-1;
  cyc = cgetg(nbp+2,t_VEC);
  gen = cgetg(nbp+2,t_VEC);
  mod = cgetg(nbp+2,t_VEC);
  switch(mod8(n))
  {
    case 0: {
      long v2 = itos((GEN)E[1]);
      cyc[1] = (long)int2n(v2-2);
      cyc[2] = (long)gen_2;
      gen[1] = (long)utoipos(5);
      gen[2] = laddis(int2n(v2-1), -1);
      mod[1] = mod[2] = (long)int2n(v2);
      sizeh = nbp+1; i = 3; j = 2; break;
    }
    case 4:
      cyc[1] = (long)gen_2;
      gen[1] = (long)utoipos(3);
      mod[1] = (long)utoipos(4);
      sizeh = nbp; i = j = 2; break;
    case 2: case 6:
      sizeh = nbp-1; i=1; j=2; break;
    default: /* 1, 3, 5, 7 */
      sizeh = nbp; i = j = 1;
  }
  for ( ; j<=nbp; i++,j++)
  {
    long e = itos((GEN)E[j]);
    GEN p = (GEN)P[j], q = powiu(p, e-1), Q = mulii(p, q);
    cyc[i] = lsubii(Q, q); /* phi(p^e) */
    gen[i] = (long)Zpn_gener(p, e);
    mod[i] = (long)Q;
  }
  for (i=1; i<=sizeh; i++)
  {
    GEN q = (GEN)mod[i], a = (GEN)gen[i];
    z = Fp_inv(q, diviiexact(n,q));
    a = addii(a, mulii(mulii(subsi(1,a),z),q));
    gen[i] = lmodulcp(a, n);
  }

  for (i=sizeh; i>=2; i--)
    for (j=i-1; j>=1; j--)
      if (remii((GEN)cyc[j],(GEN)cyc[i]) != gen_0)
      {
	GEN u, v, d = bezout((GEN)cyc[i],(GEN)cyc[j],&u,&v);
        GEN q = diviiexact((GEN)cyc[j],d);
	cyc[j] = lmulii((GEN)cyc[i],q);
        cyc[i] = (long)d;
	gen[j] = ldiv((GEN)gen[j], (GEN)gen[i]);
	gen[i] = lmul((GEN)gen[i], powgi((GEN)gen[j], mulii(v,q)));
      }
  setlg(cyc, sizeh+1); z = detcyc(cyc, &i);
  setlg(cyc,i);
  setlg(gen,i); return gerepilecopy(av, mkvec3(z,cyc,gen));
}

/*********************************************************************/
/**                                                                 **/
/**                     INTEGRAL SQUARE ROOT                        **/
/**                                                                 **/
/*********************************************************************/
GEN
gracine(GEN a)
{
  return garith_proto(racine,a,1); /* hm. --GN */
}

GEN
racine(GEN a)
{
  if (typ(a) != t_INT) err(arither1);
  switch (signe(a))
  {
    case 1: return sqrti(a);
    case 0: return gen_0;
    default: err(talker, "negative integer in sqrtint");
  }
  return NULL; /* not reached */
}

/*********************************************************************/
/**                                                                 **/
/**                      PERFECT SQUARE                             **/
/**                                                                 **/
/*********************************************************************/
static int
carremod(ulong A)
{
  static int carresmod64[]={
    1,1,0,0,1,0,0,0,0,1, 0,0,0,0,0,0,1,1,0,0, 0,0,0,0,0,1,0,0,0,0,
    0,0,0,1,0,0,1,0,0,0, 0,1,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,1,0,0, 0,0,0,0};
  static int carresmod63[]={
    1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,1,0,1,0, 0,0,1,0,0,1,0,0,1,0,
    0,0,0,0,0,0,1,1,0,0, 0,0,0,1,0,0,1,0,0,1, 0,0,0,0,0,0,0,0,1,0, 0,0,0};
  static int carresmod65[]={
    1,1,0,0,1,0,0,0,0,1, 1,0,0,0,1,0,1,0,0,0, 0,0,0,0,0,1,1,0,0,1,
    1,0,0,0,0,1,1,0,0,1, 1,0,0,0,0,0,0,0,0,1, 0,1,0,0,0,1,1,0,0,0, 0,1,0,0,1};
  static int carresmod11[]={1,1,0,1,1,1,0,0,0,1, 0};
  return (carresmod64[A & 0x3fUL]
    && carresmod63[A % 63UL]
    && carresmod65[A % 65UL]
    && carresmod11[A % 11UL]);
}

/* emulate carrecomplet on single-word positive integers */
ulong
ucarrecomplet(ulong A)
{
  if (carremod(A))
  {
    ulong a = usqrtsafe(A);
    if (a * a == A) return a;
  }
  return 0;
}

long
carrecomplet(GEN x, GEN *pt)
{
  pari_sp av;
  GEN y, r;

  switch(signe(x))
  {
    case -1: return 0;
    case 0: if (pt) *pt=gen_0; return 1;
  }
  if (lgefint(x) == 3)
  {
    ulong a = ucarrecomplet((ulong)x[2]);
    if (!a) return 0;
    if (pt) *pt = utoipos(a);
    return 1;
  }
  if (!carremod(umodiu(x, 64*63*65*11))) return 0;
  av = avma; y = sqrtremi(x, &r);
  if (r != gen_0) { avma = av; return 0; }
  if (pt) { *pt = y; avma = (pari_sp)y; } else avma = av;
  return 1;
}

static long
polcarrecomplet(GEN x, GEN *pt)
{
  pari_sp av;
  long v, l = degpol(x);
  GEN y, a, b;

  if (!signe(x))
  {
    if (pt) *pt = gcopy(x);
    return 1;
  }
  if (pt) *pt = gen_0;
  if (l&1) return 0; /* odd degree */
  av = avma;
  v = polvaluation(x, &x);
  if (v) {
    l = degpol(x);
    if (l&1) return 0;
  }
  a = (GEN)x[2];
  switch (typ(a))
  {
    case t_INT: y =    carrecomplet(a,&b)? gen_1: gen_0; break;
    case t_POL: y = polcarrecomplet(a,&b)? gen_1: gen_0; break;
    default: y = gcarreparfait(a); b = NULL; break;
  }
  if (y == gen_0) { avma = av; return 0; }
  if (!l) {
    if (!pt) { avma = av; return 1; }
    if (!b) b = gsqrt(a,DEFAULTPREC);
    y = scalarpol(b, varn(x)); goto END;
  }
  x = gdiv(x,a);
  y = gtrunc(gsqrt(greffe(x,2+l,1),0));
  if (!gequal(gsqr(y), x)) { avma = av; return 0; }
  if (!pt) { avma = av; return 1; }

  if (!gcmp1(a))
  {
    if (!b) b = gsqrt(a,DEFAULTPREC);
    y = gmul(b, y);
  }
END:
  *pt = v? gerepilecopy(av, gmulXn(y, v >> 1)): gerepileupto(av, y);
  return 1;
}

GEN
gcarrecomplet(GEN x, GEN *pt)
{
  long l, tx = typ(x);
  GEN *F;
  pari_sp av;

  if (!pt) return gcarreparfait(x);
  if (is_vec_t(tx))
  {
    long i, l = lg(x);
    GEN p, t, y = cgetg(l,tx), z = cgetg(l,tx);
    for (i=1; i<l; i++)
    {
      t = gcarrecomplet((GEN)x[i],&p);
      gel(y,i) = t;
      gel(z,i) = t == gen_0? gen_0: p;
    }
    *pt = z; return y;
  }
  switch(tx)
  {
    case t_INT: l = carrecomplet(x, pt); break;
    case t_FRAC: av = avma;
      F = (GEN*)cgetg(3, t_FRAC);
      l = carrecomplet((GEN)x[1], &F[1]);
      if (l) l = carrecomplet((GEN)x[2], &F[2]);
      if (!l) { avma = av; break; }
      *pt = (GEN)F; break;

    case t_POL: l = polcarrecomplet(x,pt); break;
    case t_RFRAC: av = avma;
      F = (GEN*)cgetg(3, t_RFRAC);
      l = (gcarrecomplet((GEN)x[1], &F[1]) != gen_0);
      if (l) l = polcarrecomplet((GEN)x[2], &F[2]);
      if (!l) { avma = av; break; }
      *pt = (GEN)F; break;

    default: err(arither1);
      return NULL; /* not reached */
  }
  return l? gen_1: gen_0;
}

GEN
gcarreparfait(GEN x)
{
  pari_sp av;
  GEN p1,a,p;
  long tx=typ(x),l,i,v;

  switch(tx)
  {
    case t_INT:
      return carreparfait(x)? gen_1: gen_0;

    case t_REAL:
      return (signe(x)>=0)? gen_1: gen_0;

    case t_INTMOD:
    {
      GEN b, q;
      long w;
      a = (GEN)x[2]; if (!signe(a)) return gen_1;
      av = avma;
      q = absi((GEN)x[1]); v = vali(q);
      if (v) /* > 0 */
      {
        long dv;
        w = vali(a); dv = v - w;
        if (dv > 0)
        {
          if (w & 1) { avma = av; return gen_0; }
          if (dv >= 2)
          {
            b = w? shifti(a,-w): a;
            if ((dv>=3 && mod8(b) != 1) ||
                (dv==2 && mod4(b) != 1)) { avma = av; return gen_0; }
          }
        }
        q = shifti(q, -v);
      }
      /* q is now odd */
      i = kronecker(a,q);
      if (i < 0) { avma = av; return gen_0; }
      if (i==0)
      {
        GEN d = gcdii(a,q);
        p = (GEN)factor(d)[1]; l = lg(p);
        for (i=1; i<l; i++)
        {
          v = Z_pvalrem(a,(GEN)p[i],&p1);
          w = Z_pvalrem(q,(GEN)p[i], &q);
          if (v < w && (v&1 || kronecker(p1,(GEN)p[i]) == -1))
            { avma = av; return gen_0; }
        }
        if (kronecker(a,q) == -1) { avma = av; return gen_0; }
      }
      /* kro(a,q) = 1, q odd: need to factor q */
      p = (GEN)factor(q)[1]; l = lg(p) - 1;
      /* kro(a,q) = 1, check all p|q but the last (product formula) */
      for (i=1; i<l; i++)
        if (kronecker(a,(GEN)p[i]) == -1) { avma = av; return gen_0; }
      return gen_1;
    }

    case t_FRAC:
      av=avma; l=carreparfait(mulii((GEN)x[1],(GEN)x[2]));
      avma=av; return l? gen_1: gen_0;

    case t_COMPLEX:
      return gen_1;

    case t_PADIC:
      a = (GEN)x[4]; if (!signe(a)) return gen_1;
      if (valp(x)&1) return gen_0;
      p = (GEN)x[2];
      if (!equaliu(p, 2))
        return (kronecker(a,p)== -1)? gen_0: gen_1;

      v = precp(x); /* here p=2, a is odd */
      if ((v>=3 && mod8(a) != 1 ) ||
          (v==2 && mod4(a) != 1)) return gen_0;
      return gen_1;

    case t_POL:
      return stoi( polcarrecomplet(x,NULL) );

    case t_SER:
      if (!signe(x)) return gen_1;
      if (valp(x)&1) return gen_0;
      return gcarreparfait((GEN)x[2]);

    case t_RFRAC:
      av = avma; a = gcarreparfait(gmul((GEN)x[1],(GEN)x[2]));
      avma = av; return a;

    case t_QFR: case t_QFI:
      return gcarreparfait((GEN)x[1]);

    case t_VEC: case t_COL: case t_MAT:
      l=lg(x); p1=cgetg(l,tx);
      for (i=1; i<l; i++) p1[i]=(long)gcarreparfait((GEN)x[i]);
      return p1;
  }
  err(typeer,"issquare");
  return NULL; /* not reached */
}

/*********************************************************************/
/**                                                                 **/
/**                        PERFECT POWER                            **/
/**                                                                 **/
/*********************************************************************/
static int
pow_check(ulong p, GEN *x, GEN *logx, long *k)
{
  GEN u, y;
  long e;
  setlg(*logx, DEFAULTPREC + (lg(*x)-2) / p);
  u = divrs(*logx, p); y = grndtoi(mpexp(u), &e);
  if (e >= -10 || !equalii(powiu(y, p), *x)) return 0;
  *k *= p; *x = y; *logx = u; return 1;
}

static long
polispower(GEN x, GEN K, GEN *pt)
{
  pari_sp av,av2;
  long v, l = degpol(x), k = itos(K);
  GEN y, a, b;

  if (!signe(x)) return 1;
  if (l % k) return 0; /* degree not multiple of k */
  v = polvaluation(x, &x);
  if (v % k) return 0;
  av2 = avma; a = (GEN)x[2]; b = NULL;
  if (!ispower(a, K, &b)) { avma = av2; return 0; }
  av = avma;
  if (degpol(x))
  {
    x = gdiv(x,a);
    y = gtrunc(gsqrtn(greffe(x,lg(x),1), K, NULL, 0)); av2 = avma;
    if (!gequal(powgi(y, K), x)) { avma = av; return 0; }
  }
  else y = polun[varn(x)];
  if (pt)
  {
    if (!gcmp1(a))
    {
      if (!b) b = gsqrtn(a, K, NULL, DEFAULTPREC);
      y = gmul(b,y);
    }
    *pt = v? gerepilecopy(av, gmulXn(y, v/k)): gerepileupto(av, y);
  }
  else avma = av;
  return 1;
}

long
ispower(GEN x, GEN K, GEN *pty)
{
  ulong k, mask;
  GEN z;

  if (!K) return gisanypower(x, pty);
  if (typ(K) != t_INT || signe(K) <= 0) err(typeer, "ispower");
  if (is_pm1(K)) { if (pty) *pty = gcopy(x); return 1; }
  switch(typ(x)) {
    case t_INT:
      k = itou(K);
      if (k == 2) return carrecomplet(x, pty);
      if (k == 3) { mask = 1; return !!is_357_power(x, pty, &mask); }
      if (k == 5) { mask = 2; return !!is_357_power(x, pty, &mask); }
      if (k == 7) { mask = 4; return !!is_357_power(x, pty, &mask); }
      return is_kth_power(x, k, pty, NULL);
    case t_FRAC:
    {
      GEN a = (GEN)x[1], b = (GEN)x[2];
      z = cgetg(3, t_FRAC);
      if (ispower(a, K, pty? &a: NULL)
       && ispower(b, K, pty? &b: NULL))
      {
        if (pty) { *pty = z; z[1] = (long)a; z[2] = (long)b; }
        return 1;
      }
      avma = (pari_sp)(z + 3); return 0;
    }
    case t_INTMOD:
    {
      pari_sp av = avma;
      GEN d, p = (GEN)x[1];
      z = (GEN)x[2]; if (!signe(z)) return 1;
      d = subis(p, 1); ;
      z = Fp_pow(z, diviiexact(d, gcdii(K, d)), p);
      avma = av; return is_pm1(z);
    }
    case t_PADIC:
      z = padic_sqrtn(x, K, NULL);
      if (!z) return 0;
      if (pty) *pty = z;
      return 1;

    case t_POL:
      return polispower(x, K, pty);
    case t_RFRAC:
      if (polcarrecomplet(gmul((GEN)x[1], powgi((GEN)x[2], subis(K,1))), pty))
      {
        if (pty) *pty = gdiv(*pty, (GEN)x[2]);
        return 1;
      }
      return 0;

    default: err(impl, "ispower for non-rational arguments");
    return 0; /* not reached */
  }
}

long
gisanypower(GEN x, GEN *pty)
{
  long tx = typ(x);
  ulong k, h;
  if (tx == t_FRAC)
  {
    pari_sp av = avma;
    GEN fa, P, E, a = (GEN)x[1], b = (GEN)x[2];
    long i, j, p, e;
    int sw = (cmpii(a, b) > 0);

    if (sw) swap(a, b);
    k = isanypower(a, pty? &a: NULL);
    if (!k) { avma = av; return 0; }
    fa = factoru(k);
    P = (GEN)fa[1];
    E = (GEN)fa[2]; h = k;
    for (i = lg(P) - 1; i > 0; i--)
    {
      p = P[i];
      e = E[i];
      for (j = 0; j < e; j++)
        if (!is_kth_power(b, p, &b, NULL)) break;
      if (j < e) k /= upowuu(p, e - j);
    }
    if (k == 1) { avma = av; return 0; }
    if (!pty) { avma = av; return k; }
    if (k != h) a = powiu(a, h/k);
    *pty = gerepilecopy(av, mkfrac(a, b));
    return k;
  }
  if (tx == t_INT) return isanypower(x, pty);
  err(talker, "missing exponent");
  return 0; /* not reached */
}

long
isanypower(GEN x, GEN *pty)
{
  pari_sp av = avma;
  long ex, k = 1;
  GEN logx, y;
  byteptr d = diffptr;
  ulong mask = 7, p = 0, ex0 = 11, e2;

  if (typ(x) != t_INT || cmpii(x, gen_2) < 0)
    err(talker, "isanypower: argument must be > 1");
  while (carrecomplet(x, &y)) { k <<= 1; x = y; }
  while ( (ex = is_357_power(x, &y, &mask)) ) { k *= ex; x = y; }
  /* cut off at 4 bits not 1 which seems to be about optimum;  for primes
   * >> 10^3 the modular checks are no longer competitively fast */
  while ( (ex = is_odd_power(x, &y, &ex0, 4)) ) { k *= ex; x = y; }
  if (DEBUGLEVEL>4) fprintferr("isanypower: now k=%ld, x=%Z\n", k, x);
  do
  {
    if (*d) NEXT_PRIME_VIADIFF(p,d);
    else { p = itou( nextprime(utoipos(p + 1)) ); }
  } while (p < ex0);

  e2 = expi(x) + 1;
  logx = logr_abs( itor(x, DEFAULTPREC + (lg(x)-2) / p) );
  while (p < e2)
  {
    if (pow_check(p, &x, &logx, &k)) {
      e2 = expi(x) + 1;
      continue; /* success, retry same p */
    }
    if (*d) NEXT_PRIME_VIADIFF(p, d);
    else p = itou( nextprime(utoipos(p + 1)) );
  }
  if (pty) *pty = gerepilecopy(av, x); else avma = av;
  return k == 1? 0: k;
}

/*********************************************************************/
/**                                                                 **/
/**                        KRONECKER SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/
/* u = 3,5 mod 8 ?  (= 2 not a square mod u) */
#define  ome(t) (labs(((t)&7)-4) == 1)
#define gome(t) (ome(modBIL(t)))

/* assume y odd, return kronecker(x,y) * s */
long
krouu_s(ulong x, ulong y, long s)
{
  ulong x1 = x, y1 = y, z;
  while (x1)
  {
    long r = vals(x1);
    if (r)
    {
      if (odd(r) && ome(y1)) s = -s;
      x1 >>= r;
    }
    if (x1 & y1 & 2) s = -s;
    z = y1 % x1; y1 = x1; x1 = z;
  }
  return (y1 == 1)? s: 0;
}

GEN
gkronecker(GEN x, GEN y) { return arith_proto2(kronecker,x,y); }

long
kronecker(GEN x, GEN y)
{
  const pari_sp av = avma;
  GEN z;
  long s = 1, r;
  ulong xu, yu;

  switch (signe(y))
  {
    case -1: y = negi(y); if (signe(x) < 0) s = -1; break;
    case 0: return is_pm1(x);
  }
  r = vali(y);
  if (r)
  {
    if (!mpodd(x)) { avma = av; return 0; }
    if (odd(r) && gome(x)) s = -s;
    y = shifti(y,-r);
  }
  x = modii(x,y);
  while (lgefint(x) > 3) /* x < y */
  {
    r = vali(x);
    if (r)
    {
      if (odd(r) && gome(y)) s = -s;
      x = shifti(x,-r);
    }
    /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
    if (modBIL(x) & modBIL(y) & 2) s = -s;
    z = remii(y,x); y = x; x = z;
  }
  xu = itou(x);
  if (!xu) return is_pm1(y)? s: 0;
  r = vals(xu);
  if (r)
  {
    if (odd(r) && gome(y)) s = -s;
    xu >>= r;
  }
  /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
  if (xu & modBIL(y) & 2) s = -s;
  yu = umodiu(y, xu);
  avma = av; return krouu_s(yu, xu, s);
}

GEN
gkrogs(GEN x, long y) { return arith_proto2gs(krois,x,y); }

long
krois(GEN x, long y)
{
  ulong yu;
  long s = 1, r;

  if (y <= 0)
  {
    if (y == 0) return is_pm1(x);
    yu = (ulong)-y; if (signe(x) < 0) s = -1;
  }
  else
    yu = (ulong)y;
  r = vals(yu);
  if (r)
  {
    if (!mpodd(x)) return 0;
    if (odd(r) && gome(x)) s = -s;
    yu >>= r;
  }
  return krouu_s(umodiu(x, yu), yu, s);
}

long
krosi(long x, GEN y)
{
  const pari_sp av = avma;
  long s = 1, r;
  ulong u, xu;

  switch (signe(y))
  {
    case -1: y = negi(y); if (x < 0) s = -1; break;
    case 0: return (x==1 || x==-1);
  }
  r = vali(y);
  if (r)
  {
    if (!odd(x)) { avma = av; return 0; }
    if (odd(r) && ome(x)) s = -s;
    y = shifti(y,-r);
  }
  if (x < 0) { x = -x; if (mod4(y) == 3) s = -s; }
  xu = (ulong)x;
  if (lgefint(y) == 3)
    return krouu_s(xu, itou(y), s);
  if (!xu) return 0; /* y != 1 */
  r = vals(xu);
  if (r)
  {
    if (odd(r) && gome(y)) s = -s;
    xu >>= r;
  }
  /* xu=3 mod 4 && y=3 mod 4 ? (both are odd here) */
  if (xu & modBIL(y) & 2) s = -s;
  u = umodiu(y, xu);
  avma = av; return krouu_s(u, xu, s);
}

long
kross(long x, long y)
{
  ulong yu;
  long s = 1, r;

  if (y <= 0)
  {
    if (y == 0) return (labs(x)==1);
    yu = (ulong)-y; if (x < 0) s = -1;
  }
  else
    yu = (ulong)y;
  r = vals(yu);
  if (r)
  {
    if (!odd(x)) return 0;
    if (odd(r) && ome(x)) s = -s;
    yu >>= r;
  }
  x %= (long)yu; if (x < 0) x += yu;
  return krouu_s((ulong)x, yu, s);
}

long
krouu(ulong x, ulong y)
{
  long r;
  if (y & 1) return krouu_s(x, y, 1);
  if (!odd(x)) return 0;
  r = vals(y);
  return krouu_s(x, y >> r, (odd(r) && ome(x))? -1: 1);
}

/*********************************************************************/
/**                                                                 **/
/**                          HILBERT SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/

long
hil0(GEN x, GEN y, GEN p)
{
  return hil(x,y, p? p: gen_0);
}

#define eps(t) (((signe(t)*(modBIL(t)))&3)==3)
long
hilii(GEN x, GEN y, GEN p)
{
  pari_sp av;
  long a, b, z;
  GEN u, v;

  if (signe(p)<=0)
    return (signe(x)<0 && signe(y)<0)? -1: 1;
  av = avma;
  a = odd(Z_pvalrem(x,p,&u));
  b = odd(Z_pvalrem(y,p,&v));
  if (equaliu(p, 2))
  {
    z = (eps(u) && eps(v))? -1: 1;
    if (a && gome(v)) z = -z;
    if (b && gome(u)) z = -z;
  }
  else
  {
    z = (a && b && eps(p))? -1: 1;
    if (a && kronecker(v,p)<0) z = -z;
    if (b && kronecker(u,p)<0) z = -z;
  }
  avma = av; return z;
}

static void
err_at2() { err(talker, "insufficient precision for p = 2 in hilbert"); }

long
hil(GEN x, GEN y, GEN p)
{
  pari_sp av;
  long a,tx,ty,z;
  GEN p1,p2;

  if (gcmp0(x) || gcmp0(y)) return 0;
  av = avma; tx = typ(x); ty = typ(y);
  if (tx>ty) { p1=x; x=y; y=p1; a=tx,tx=ty; ty=a; }
  switch(tx) /* <= ty */
  {
    case t_INT:
      switch(ty)
      {
	case t_INT: return hilii(x,y,p);
	case t_REAL:
	  return (signe(x)<0 && signe(y)<0)? -1: 1;
	case t_INTMOD:
          p = (GEN)y[1]; if (equaliu(p,2)) err_at2();
	  return hilii(x, (GEN)y[2], p);
	case t_FRAC:
	  z = hilii(x, mulii((GEN)y[1],(GEN)y[2]), p);
	  avma = av; return z;
	case t_PADIC:
          p = (GEN)y[2];
	  if (equaliu(p,2) && precp(y) <= 1) err_at2();
	  p1 = odd(valp(y))? mulii(p,(GEN)y[4]): (GEN)y[4];
	  z = hilii(x, p1, p); avma = av; return z;
      }
      break;

    case t_REAL:
      if (ty != t_FRAC) break;
      if (signe(x) > 0) return 1;
      return signe(y[1])*signe(y[2]);

    case t_INTMOD:
      p = (GEN)x[1]; if (equaliu(p,2)) err_at2();
      switch(ty)
      {
        case t_INTMOD:
          if (!equalii(p, (GEN)y[1])) break;
          return hilii((GEN)x[2],(GEN)y[2],p);
        case t_FRAC:
	  return hil((GEN)x[2],y,p);
        case t_PADIC:
          if (!equalii(p, (GEN)y[2])) break;
          return hil((GEN)x[2],y,p);
      }
      break;

    case t_FRAC:
      p1 = mulii((GEN)x[1],(GEN)x[2]);
      switch(ty)
      {
	case t_FRAC:
	  p2 = mulii((GEN)y[1],(GEN)y[2]);
	  z = hilii(p1,p2,p); avma = av; return z;
	case t_PADIC:
	  z = hil(p1,y,NULL); avma = av; return z;
      }
      break;

    case t_PADIC:
      p = (GEN)x[2];
      if (ty != t_PADIC || !equalii(p,(GEN)y[2])) break;
      if (equaliu(p,2) && (precp(x) <= 1 || precp(y) <= 1)) err_at2();
      p1 = odd(valp(x))? mulii(p,(GEN)x[4]): (GEN)x[4];
      p2 = odd(valp(y))? mulii(p,(GEN)y[4]): (GEN)y[4];
      z = hilii(p1,p2,p); avma = av; return z;
  }
  err(talker,"forbidden or incompatible types in hil");
  return 0; /* not reached */
}
#undef eps
#undef ome
#undef gome

/*******************************************************************/
/*                                                                 */
/*                       SQUARE ROOT MODULO p                      */
/*                                                                 */
/*******************************************************************/

/* Tonelli-Shanks. Assume p is prime and (a,p) != -1. */
ulong
Fl_sqrt(ulong a, ulong p)
{
  long i, e, k;
  ulong p1, q, v, y, w, m;

  if (!a) return 0;
  p1 = p - 1; e = vals(p1);
  if (e == 0) /* p = 2 */
  {
    if (p != 2) err(talker,"composite modulus in Fl_sqrt: %lu",p);
    return ((a & 1) == 0)? 0: 1;
  }
  q = p1 >> e; /* q = (p-1)/2^oo is odd */
  if (e == 1) y = p1;
  else /* look for an odd power of a primitive root */
    for (k=2; ; k++)
    { /* loop terminates for k < p (even if p composite) */
      i = krouu(k, p);
      if (i >= 0)
      {
        if (i) continue;
        err(talker,"composite modulus in Fl_sqrt: %lu",p);
      }
      y = m = Fl_pow(k, q, p);
      for (i=1; i<e; i++)
	if ((m = Fl_sqr(m,p)) == 1) break;
      if (i == e) break; /* success */
    }

  p1 = Fl_pow(a, q >> 1, p); /* a ^ [(q-1)/2] */
  if (!p1) return 0;
  v = Fl_mul(a, p1, p);
  w = Fl_mul(v, p1, p);
  while (w != 1)
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = Fl_sqr(w,p);
    for (k=1; p1 != 1 && k < e; k++) p1 = Fl_sqr(p1,p);
    if (k == e) return ~0UL;
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = Fl_sqr(p1,p);
    y = Fl_sqr(p1, p); e = k;
    w = Fl_mul(y, w, p);
    v = Fl_mul(v, p1, p);
  }
  p1 = p - v; if (v > p1) v = p1;
  return v;
}

/* Cipolla's algorithm is better when e = v_2(p-1) is "too big".
 * Otherwise, is a constant times worse than the above one.
 * For p = 3 (mod 4), is about 3 times worse, and in average
 * is about 2 or 2.5 times worse.
 *
 * But try both algorithms for e.g. S(n)=(2^n+3)^2-8 with
 * n = 750, 771, 779, 790, 874, 1176, 1728, 2604, etc.
 *
 * If X^2 = t^2 - a  is not a square in F_p, then
 *
 *   (t+X)^(p+1) = (t+X)(t-X) = a
 *
 * so we get sqrt(a) in F_p^2 by
 *
 *   sqrt(a) = (t+X)^((p+1)/2)
 *
 * If (a|p)=1, then sqrt(a) is in F_p.
 *
 * cf: LNCS 2286, pp 430-434 (2002)  [Gonzalo Tornaria] */

GEN
sqrt_Cipolla_sqr(void *data, GEN y)
{ 
  GEN u=(GEN) y[1];
  GEN v=(GEN) y[2];
  GEN p=((GEN*) data)[2];
  GEN n=((GEN*) data)[3];
  GEN u2 = sqri(u);
  GEN v2 = sqri(v);
  v = modii(subii(sqri(addii(v,u)), addii(u2,v2)), p);
  u = modii(addii(u2, mulii(v2,n)), p);
  return mkvec2(u,v);
}

GEN
sqrt_Cipolla_msqr(void *data, GEN y)
{ 
  GEN a =((GEN*) data)[1];
  GEN p =((GEN*) data)[2];
  long t= mael(data,4,2);
  GEN u =(GEN)y[1];
  GEN v =(GEN)y[2];
  GEN d = addii(u, mulsi(t,v));
  GEN d2= sqri(d);
  GEN b = remii(mulii(a,v), p);
  u = modii(subii(mulsi(t,d2), mulii(b,addii(u,d))), p);
  v = modii(subii(d2, mulii(b,v)), p);
  return mkvec2(u,v);
}

static GEN
sqrt_Cipolla(GEN a, GEN p)
{
  pari_sp av = avma, av1;
  long t;
  GEN u, v, n;
  GEN y, data;

  if (kronecker(a, p) < 0) return NULL;
  /*Avoid multiplying by huge base*/
  if(cmpii(a,shifti(p,-1)) > 0) a=subii(a,p);

  av1 = avma;
  for(t=1; ; t++)
  {
    n = subsi(t*t, a);
    if (kronecker(n, p) < 0) break;
    avma = av1;
  }

  u = utoipos((ulong)t); v = gen_1; /* u+vX = t+X */
  y=mkvec2(u,v); data=mkvec4(a,p,n,u);
  y=leftright_pow_fold(y, shifti(p, -1), data,
                sqrt_Cipolla_sqr,sqrt_Cipolla_msqr);

  u=(GEN)y[1]; v=(GEN)y[2];

  /* Now u+vX = (t+X)^((p-1)/2); thus
   *
   *   (u+vX)(t+X) = sqrt(a) + 0 X
   *
   * Whence,
   *
   *   sqrt(a) = (u+vt)t - v*a
   *   0       = (u+vt)
   *
   * Thus a square root is v*a */

  v = modii(mulii(v,a), p);

  u = subii(p,v); if (cmpii(v,u) > 0) v = u;
  return gerepileuptoint(av,v);
}

#define sqrmod(x,p) (remii(sqri(x),p))

/* Tonelli-Shanks. Assume p is prime and return NULL if (a,p) = -1. */
GEN
Fp_sqrt(GEN a, GEN p)
{
  pari_sp av = avma, av1,lim;
  long i, k, e;
  GEN p1, q, v, y, w, m;

  if (typ(a) != t_INT || typ(p) != t_INT) err(arither1);
  if (signe(p) <= 0 || is_pm1(p)) err(talker,"not a prime in Fp_sqrt");
  if (lgefint(p) == 3)
  {
    ulong u = (ulong)p[2]; u = Fl_sqrt(umodiu(a, u), u);
    if (u == ~0UL) return NULL;
    return utoi(u);
  }

  p1 = addsi(-1,p); e = vali(p1);

  /* On average, the algorithm of Cipolla is better than the algorithm of
   * Tonelli and Shanks if and only if e(e-1)>8*log2(n)+20
   * see LNCS 2286 pp 430 [GTL] */

  if (e*(e-1) > 20 + 8 * bit_accuracy(lgefint(p)))
  {
    v = sqrt_Cipolla(a,p);
    if (!v) { avma = av; return NULL; }
    return gerepileuptoint(av,v);
  }

  if (e == 0) /* p = 2 */
  {
    avma = av;
    if (!equaliu(p,2)) err(talker,"composite modulus in Fp_sqrt: %Z",p);
    if (!signe(a) || !mod2(a)) return gen_0;
    return gen_1;
  }
  q = shifti(p1,-e); /* q = (p-1)/2^oo is odd */
  if (e == 1) y = p1;
  else /* look for an odd power of a primitive root */
    for (k=2; ; k++)
    { /* loop terminates for k < p (even if p composite) */

      i = krosi(k,p);
      if (i >= 0)
      {
        if (i) continue;
        err(talker,"composite modulus in Fp_sqrt: %Z",p);
      }
      av1 = avma;
      y = m = Fp_pow(utoipos((ulong)k),q,p);
      for (i=1; i<e; i++)
	if (gcmp1(m = sqrmod(m,p))) break;
      if (i == e) break; /* success */
      avma = av1;
    }

  p1 = Fp_pow(a, shifti(q,-1), p); /* a ^ [(q-1)/2] */
  if (!signe(p1)) { avma=av; return gen_0; }
  v = modii(mulii(a, p1), p);
  w = modii(mulii(v, p1), p);
  lim = stack_lim(av,1);
  while (!is_pm1(w))
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = sqrmod(w,p);
    for (k=1; !is_pm1(p1) && k < e; k++) p1 = sqrmod(p1,p);
    if (k == e) { avma=av; return NULL; } /* p composite or (a/p) != 1 */
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = sqrmod(p1,p);
    y = sqrmod(p1, p); e = k;
    w = modii(mulii(y, w), p);
    v = modii(mulii(v, p1), p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[3]; gptr[0]=&y; gptr[1]=&w; gptr[2]=&v;
      if(DEBUGMEM>1) err(warnmem,"Fp_sqrt");
      gerepilemany(av,gptr,3);
    }
  }
  av1 = avma;
  p1 = subii(p,v); if (cmpii(v,p1) > 0) v = p1; else avma = av1;
  return gerepileuptoint(av, v);
}

/*******************************************************************/
/*                                                                 */
/*                       n-th ROOT MODULO p                        */
/*                                                                 */
/*******************************************************************/
/* Assume l is prime. Return a non l-th power residue and set *zeta to a
 * primitive l-th root of 1.
 *
 * q = p-1 = l^e*r, e>=1, (r,l)=1
 * UNCLEAN */
static GEN
mplgenmod(GEN l, long e, GEN r,GEN p,GEN *zeta)
{
  const pari_sp av1 = avma;
  GEN m, m1;
  long k, i;
  for (k=2; ; k++)
  {
    m1 = m = Fp_pow(utoipos(k), r, p);
    if (is_pm1(m)) { avma = av1; continue; }
    for (i=1; i<e; i++)
      if (gcmp1(m = Fp_pow(m,l,p))) break;
    if (i==e) { *zeta = m; return m1; }
    avma = av1;
  }
}

/* solve x^l = a mod (p), l prime
 *
 * q = p-1 = (l^e)*r, e >= 1, (r,l) = 1
 * y is not an l-th power, hence generates the l-Sylow of (Z/p)^*
 * m = y^(q/l) != 1 */
static GEN
Fp_sqrtl(GEN a, GEN l, GEN p, GEN q,long e, GEN r, GEN y, GEN m)
{
  pari_sp av = avma, tetpil,lim;
  long k;
  GEN p1, u1, u2, v, w, z, dl;

  (void)bezout(r,l,&u1,&u2);
  v = Fp_pow(a,u2,p);
  w = Fp_pow(a,modii(mulii(negi(u1),r),q),p);
  lim = stack_lim(av,1);
  while (!is_pm1(w))
  {
    k = 0;
    p1 = w;
    do
    { /* if p is not prime, this loop will not end */
      z = p1; p1 = Fp_pow(p1,l,p);
      k++;
    } while(!is_pm1(p1));
    if (k==e) { avma = av; return NULL; }
    dl = Fp_shanks(Fp_inv(z,p),m,p,l);
    p1 = Fp_pow(y, modii(mulii(dl,powiu(l,e-k-1)),q), p);
    m = Fp_pow(m,dl,p);
    e = k;
    v = modii(mulii(p1,v),p);
    y = Fp_pow(p1,l,p);
    w = modii(mulii(y,w),p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"Fp_sqrtl");
      gerepileall(av,4, &y,&v,&w,&m);
    }
  }
  tetpil=avma; return gerepile(av,tetpil,icopy(v));
}
/* a, n t_INT, p is prime. Return one solution of x^n = a mod p
*
* 1) If there is no solution, return NULL and if zetan!=NULL set *zetan=gen_0.
*
* 2) If there is a solution, there are exactly m of them [m = gcd(p-1,n) if
* a != 0, and m = 1 otherwise].
* If zetan!=NULL, *zetan is set to a primitive mth root of unity so that
* the set of solutions is { x*zetan^k; k=0..m-1 } */
GEN
Fp_sqrtn(GEN a, GEN n, GEN p, GEN *zetan)
{
  pari_sp ltop = avma, lbot = 0, lim;
  GEN m, u1, u2, q, z;

  if (typ(a) != t_INT || typ(n) != t_INT || typ(p)!=t_INT)
    err(typeer,"Fp_sqrtn");
  if (!signe(n)) err(talker,"1/0 exponent in Fp_sqrtn");
  if (gcmp1(n)) { if (zetan) *zetan = gen_1; return icopy(a);}
  a = modii(a,p);
  if (gcmp0(a)) { if (zetan) *zetan = gen_1; avma = ltop; return gen_0;}
  q = addsi(-1,p);
  m = bezout(n,q,&u1,&u2);
  z = gen_1;
  lim = stack_lim(ltop,1);
  if (!is_pm1(m))
  {
    GEN F = decomp(m);
    long i, j, e;
    GEN r, zeta, y, l;
    pari_sp av1 = avma;
    for (i = lg(F[1])-1; i; i--)
    {
      l = gcoeff(F,i,1);
      j = itos(gcoeff(F,i,2));
      e = Z_pvalrem(q,l,&r);
      y = mplgenmod(l,e,r,p,&zeta);
      if (zetan) z = modii(mulii(z, Fp_pow(y,powiu(l,e-j),p)), p);
      do
      {
	lbot = avma;
	if (!is_pm1(a) || signe(a)<0)
        {
	  a = Fp_sqrtl(a,l,p,q,e,r,y,zeta);
          if (!a) { avma = ltop; if (zetan) *zetan = gen_0; return NULL;}
        }
	else
	  a = icopy(a);
      } while (--j);
      if (low_stack(lim, stack_lim(ltop,1)))
      { /* n can have lots of prime factors*/
	if(DEBUGMEM>1) err(warnmem,"Fp_sqrtn");
        gerepileall(av1, zetan? 2: 1, &a, &z);
	lbot = av1;
      }
    }
  }
  if (!equalii(m, n))
  {
    GEN b = modii(u1,q);
    lbot = avma; a = Fp_pow(a,b,p);
  }
  if (zetan)
  {
    GEN *gptr[2];
    *zetan = icopy(z);
    gptr[0] = &a;
    gptr[1] = zetan; gerepilemanysp(ltop,lbot,gptr,2);
  }
  else
    a = gerepileuptoint(ltop, a);
  return a;
}

/*********************************************************************/
/**                                                                 **/
/**                        GCD & BEZOUT                             **/
/**                                                                 **/
/*********************************************************************/

GEN
lcmii(GEN x, GEN y)
{
  pari_sp av;
  GEN p1,p2;
  if (!signe(x)) return gen_0;
  av = avma;
  p1 = gcdii(x,y); if (!is_pm1(p1)) y = diviiexact(y,p1);
  p2 = mulii(x,y); if (signe(p2) < 0) setsigne(p2,1);
  return gerepileuptoint(av, p2);
}

/*********************************************************************/
/**                                                                 **/
/**                      CHINESE REMAINDERS                         **/
/**                                                                 **/
/*********************************************************************/

/*  P.M. & M.H.
 *
 *  Chinese Remainder Theorem.  x and y must have the same type (integermod,
 *  polymod, or polynomial/vector/matrix recursively constructed with these
 *  as coefficients). Creates (with the same type) a z in the same residue
 *  class as x and the same residue class as y, if it is possible.
 *
 *  We also allow (during recursion) two identical objects even if they are
 *  not integermod or polymod. For example, if
 *
 *    x = [1. mod(5, 11), mod(X + mod(2, 7), X^2 + 1)]
 *    y = [1, mod(7, 17), mod(X + mod(0, 3), X^2 + 1)],
 *
 *  then chinese(x, y) returns
 *
 *    [1, mod(16, 187), mod(X + mod(9, 21), X^2 + 1)]
 *
 *  Someone else may want to allow power series, complex numbers, and
 *  quadratic numbers.
 */

GEN
chinese1(GEN x) { return gassoc_proto(chinese,x,NULL); }

GEN
chinese(GEN x, GEN y)
{
  pari_sp av,tetpil;
  long i,lx, tx = typ(x);
  GEN z,p1,p2,d,u,v;

  if (!y) return chinese1(x);
  if (gequal(x,y)) return gcopy(x);
  if (tx == typ(y)) switch(tx)
  {
    case t_POLMOD:
      z = cgetg(3, t_POLMOD);
      if (gequal((GEN)x[1],(GEN)y[1]))  /* same modulus */
      {
	z[1]=lcopy((GEN)x[1]);
	z[2]=(long)chinese((GEN)x[2],(GEN)y[2]);
        return z;
      }
      av=avma;
      d=gbezout((GEN)x[1],(GEN)y[1],&u,&v);
      p2 = gadd((GEN)y[2],gneg((GEN)x[2]));
      if (!gcmp0(gmod(p2, d))) break;
      p1 = gdiv((GEN)x[1],d);
      p2 = gadd((GEN)x[2], gmul(gmul(u,p1), p2));

      tetpil=avma; z[1]=lmul(p1,(GEN)y[1]); z[2]=lmod(p2,(GEN)z[1]);
      gerepilecoeffssp(av,tetpil,z+1,2); return z;
    case t_INTMOD:
      z = cgetg(3,t_INTMOD); av = avma;
      d = bezout((GEN)x[1],(GEN)y[1],&u,&v);
      p2 = subii((GEN)y[2], (GEN)x[2]);
      if (remii(p2, d) != gen_0) break;
      p1 = diviiexact((GEN)x[1],d);
      p2 = addii((GEN)x[2], mulii(mulii(u,p1), p2));
      tetpil = avma;
      z[1] = lmulii(p1, (GEN)y[1]);
      z[2] = lmodii(p2, (GEN)z[1]);
      gerepilecoeffssp(av,tetpil,z+1,2); return z;

    case t_POL:
      lx=lg(x); z = cgetg(lx,t_POL); z[1] = x[1];
      if (lx != lg(y) || varn(x) != varn(y)) break;
      for (i=2; i<lx; i++) z[i]=(long)chinese((GEN)x[i],(GEN)y[i]);
      return z;

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); z=cgetg(lx,tx); if (lx!=lg(y)) break;
      for (i=1; i<lx; i++) z[i]=(long)chinese((GEN)x[i],(GEN)y[i]);
      return z;
  }
  err(typeer,"chinese");
  return NULL; /* not reached */
}

/* return lift(chinese(a mod A, b mod B))
 * assume(A,B)=1, a,b,A,B integers and C = A*B */
GEN
Z_chinese_coprime(GEN a, GEN b, GEN A, GEN B, GEN C)
{
  pari_sp av = avma;
  GEN c = addii(a, mulii(mulii(Fp_inv(A,B), A), subii(b,a)));
  return gerepileuptoint(av, modii(c, C));
}
/*********************************************************************/
/**                                                                 **/
/**                      INVERSE MODULO b                           **/
/**                                                                 **/
/*********************************************************************/

GEN
Fp_inv(GEN a, GEN m)
{
  GEN res;
  if (! invmod(a,m,&res))
    err(invmoder,"%Z",gmodulcp(res,m));
  return res;
}

GEN
Fp_invsafe(GEN a, GEN m)
{
  GEN res;
  if (! invmod(a,m,&res))
    return NULL;
  return res;
}

/*********************************************************************/
/**                                                                 **/
/**                    MODULAR EXPONENTIATION                       **/
/**                                                                 **/
/*********************************************************************/
static GEN _remii(GEN x, GEN y) { return remii(x,y); }

/* Montgomery reduction */

typedef struct {
  GEN N;
  ulong inv; /* inv = -N^(-1) mod B, */
} montdata;

void
init_montdata(GEN N, montdata *s)
{
  s->N = N;
  s->inv = (ulong) -invrev(modBIL(N));
}

GEN
init_remiimul(GEN M)
{
  GEN iM = ginv( itor(M, lgefint(M) + 1) ); /* 1. / M */
  return mkvec2(M, iM);
}

typedef struct {
  GEN N;
  GEN (*res)(GEN,GEN);
  GEN (*mulred)(GEN,GEN,GEN);
} muldata;

/* reduction for multiplication by 2 */
static GEN
_redsub(GEN x, GEN N)
{
  return (cmpii(x,N) >= 0)? subii(x,N): x;
}
/* Montgomery reduction */
static GEN
montred(GEN x, GEN N)
{
  return red_montgomery(x, ((montdata*)N)->N, ((montdata*)N)->inv);
}
/* 2x mod N */
static GEN
_muli2red(GEN x, GEN y/* ignored */, GEN N) {
  (void)y; return _redsub(shifti(x,1), N);
}
static GEN
_muli2montred(GEN x, GEN y/* ignored */, GEN N) {
  GEN n = ((montdata*)N)->N;
  GEN z = _muli2red(x,y, n);
  long l = lgefint(n);
  while (lgefint(z) > l) z = subii(z,n);
  return z;
}
static GEN
_muli2invred(GEN x, GEN y/* ignored */, GEN N) {
  return _muli2red(x,y, (GEN)N[1]);
}
/* xy mod N */
static GEN
_muliired(GEN x, GEN y, GEN N) { return remii(mulii(x,y), N); }
static GEN
_muliimontred(GEN x, GEN y, GEN N) { return montred(mulii(x,y), N); }
static GEN
_muliiinvred(GEN x, GEN y, GEN N) { return remiimul(mulii(x,y), N); }

static GEN
_mul(void *data, GEN x, GEN y)
{
  muldata *D = (muldata *)data;
  return D->mulred(x,y,D->N);
}
static GEN
_sqr(void *data, GEN x)
{
  muldata *D = (muldata *)data;
  return D->res(sqri(x), D->N);
}
ulong
Fl_pow(ulong x, ulong n0, ulong p)
{
  ulong y, z, n;
  if (n0 <= 2)
  { /* frequent special cases */
    if (n0 == 2) return Fl_sqr(x,p);
    if (n0 == 1) return x;
    if (n0 == 0) return 1;
  }
  y = 1; z = x; n = n0;
  for(;;)
  {
    if (n&1) y = Fl_mul(y,z,p);
    n>>=1; if (!n) return y;
    z = Fl_sqr(z,p);
  }
}

GEN
Fp_powu(GEN A, ulong k, GEN N)
{
  long lN = lgefint(N);
  int base_is_2, use_montgomery;
  muldata  D;
  montdata S;

  if (lN == 3) {
    ulong n = (ulong)N[2];
    return utoi( Fl_pow(umodiu(A, n), k, n) );
  }
  if (k <= 2)
  { /* frequent special cases */
    if (k == 2) return remii(sqri(A),N);
    if (k == 1) return A;
    if (k == 0) return gen_1;
  }

  base_is_2 = 0;
  if (lgefint(A) == 3) switch(A[2])
  {
    case 1: return gen_1;
    case 2:  base_is_2 = 1; break;
  }

  /* TODO: Move this out of here and use for general modular computations */
  use_montgomery = mod2(N) && lN < MONTGOMERY_LIMIT;
  if (use_montgomery)
  {
    init_montdata(N, &S);
    A = remii(shifti(A, bit_accuracy(lN)), N);
    D.mulred = base_is_2? &_muli2montred: &_muliimontred;
    D.res = &montred;
    D.N = (GEN)&S;
  }
  else if (lN > REMIIMUL_LIMIT && ((double)k)*expi(A) > 2 + expi(N))
  {
    D.mulred = base_is_2? &_muli2invred: &_muliiinvred;
    D.res = &remiimul;
    D.N = init_remiimul(N);
  }
  else
  {
    D.mulred = base_is_2? &_muli2red: &_muliired;
    D.res = &_remii;
    D.N = N;
  }

  A = leftright_pow_u(A, k, (void*)&D, &_sqr, &_mul);
  if (use_montgomery)
  {
    A = montred(A, (GEN)&S);
    if (cmpii(A,N) >= 0) A = subii(A,N);
  }
  return A;
}

GEN
Fp_pows(GEN A, long k, GEN N)
{
  if (lgefint(N) == 3) {
    ulong n = N[2];
    ulong a = umodiu(A, n);
    if (k < 0) {
      a = Fl_inv(a, n);
      if (!a) err(invmoder, "%Z", gmodulcp(A, N));
      k = -k;
    }
    return utoi( Fl_pow(a, (ulong)k, n) );
  }
  if (k < 0) { A = Fp_inv(A, N); k = -k; };
  return Fp_powu(A, (ulong)k, N);
}

static GEN
_Flmul(void *data, GEN x, GEN y)
{ return (GEN)Fl_mul((ulong)x,(ulong)y,(ulong)data); }

static GEN
_Flsqr(void *data, GEN x)
{ return (GEN)Fl_sqr((ulong)x,(ulong)data); }

/* A^k mod N */
GEN
Fp_pow(GEN A, GEN k, GEN N)
{
  pari_sp av = avma;
  long t,s, lN = lgefint(N);
  int base_is_2, use_montgomery;
  GEN y;
  muldata  D;
  montdata S;

  s = signe(k);
  if (!s)
  {
    t = signe(remii(A,N)); avma = av;
    return t? gen_1: gen_0;
  }
  if (lN == 3)
  {
    ulong n = N[2];
    ulong a = umodiu(A, n);
    if (s < 0) {
      a = Fl_inv(a, n);
      if (!a) err(invmoder, "%Z", gmodulcp(A, N));
    }
    if (lgefint(k) == 3) return utoi(Fl_pow(a, (ulong)k[2], n));
    /* should not occur */
    err(warner, "multiword exponent in Fl_pow");
    return utoi( (ulong)leftright_pow((GEN)a, k, (void*)n, &_Flsqr, &_Flmul) );
  }

  if (s < 0) y = Fp_inv(A,N);
  else
  {
    y = modii(A,N);
    if (!signe(y)) { avma = av; return gen_0; }
  }
  if (lgefint(k) == 3) return gerepileuptoint(av, Fp_powu(y, k[2], N));

  base_is_2 = 0;
  if (lgefint(y) == 3) switch(y[2])
  {
    case 1: avma = av; return gen_1;
    case 2:  base_is_2 = 1; break;
  }

  /* TODO: Move this out of here and use for general modular computations */
  use_montgomery = mod2(N) && lN < MONTGOMERY_LIMIT;
  if (use_montgomery)
  {
    init_montdata(N, &S);
    y = remii(shifti(y, bit_accuracy(lN)), N);
    D.mulred = base_is_2? &_muli2montred: &_muliimontred;
    D.res = &montred;
    D.N = (GEN)&S;
  }
  else if (lN > REMIIMUL_LIMIT)
  {
    D.mulred = base_is_2? &_muli2invred: &_muliiinvred;
    D.res = &remiimul;
    D.N = init_remiimul(N);
  }
  else
  {
    D.mulred = base_is_2? &_muli2red: &_muliired;
    D.res = &_remii;
    D.N = N;
  }

  y = leftright_pow(y, k, (void*)&D, &_sqr, &_mul);
  if (use_montgomery)
  {
    y = montred(y, (GEN)&S);
    if (cmpii(y,N) >= 0) y = subii(y,N);
  }
  return gerepileuptoint(av,y);
}

/*********************************************************************/
/**                                                                 **/
/**                NEXT / PRECEDING (PSEUDO) PRIME                  **/
/**                                                                 **/
/*********************************************************************/
GEN
gnextprime(GEN n) { return garith_proto(nextprime,n,0); }

GEN
gprecprime(GEN n) { return garith_proto(precprime,n,0); }

GEN
gisprime(GEN x, long flag)
{
  switch (flag)
  {
    case 0: return arith_proto(isprime,x,1);
    case 1: return garith_proto2gs(plisprime,x,1);
    case 2: return arith_proto(isprimeAPRCL,x,1);
  }
  err(flagerr,"gisprime");
  return 0;
}

long
isprimeSelfridge(GEN x) { return (plisprime(x,0)==gen_1); }

/* assume x BSW pseudoprime. Check whether it's small enough to be certified
 * prime */
int
BSW_isprime_small(GEN x)
{
  long l = lgefint(x);
  if (l < 4) return 1;
  if (l == 4)
  {
    pari_sp av = avma;
    long t = cmpii(x, u2toi(0x918UL, 0x4e72a000UL)); /* 10^13 */
    avma = av;
    if (t < 0) return 1;
  }
  return 0;
}

/* assume x a BSW pseudoprime */
int
BSW_isprime(GEN x)
{
  pari_sp av = avma;
  long l, res;
  GEN F, p;

  if (BSW_isprime_small(x)) return 1;
  F = (GEN)auxdecomp(subis(x,1), 0)[1];
  l = lg(F); p = (GEN)F[l-1];
  if (BSW_psp(p))
    res = isprimeSelfridge(mkvec2(x,F)); /* smooth */
  else
    res = isprimeAPRCL(x);
  avma = av; return res;
}

long
isprime(GEN x)
{
  return BSW_psp(x) && BSW_isprime(x);
}

GEN
gispseudoprime(GEN x, long flag)
{
  if (flag == 0) return arith_proto(BSW_psp,x,1);
  return gmillerrabin(x, flag);
}

long
ispseudoprime(GEN x, long flag)
{
  if (flag == 0) return BSW_psp(x);
  return millerrabin(x, flag);
}

GEN
gispsp(GEN x) { return arith_proto(ispsp,x,1); }

long
ispsp(GEN x) { return millerrabin(x,1); }

GEN
gmillerrabin(GEN n, long k) { return arith_proto2gs(millerrabin,n,k); }

/*********************************************************************/
/**                                                                 **/
/**                    FUNDAMENTAL DISCRIMINANTS                    **/
/**                                                                 **/
/*********************************************************************/
GEN
gisfundamental(GEN x) { return arith_proto(isfundamental,x,1); }

long
isfundamental(GEN x)
{
  long r;
  if (!signe(x)) return 0;
  r = mod16(x);
  if (!r) return 0;
  if ((r & 3) == 0)
  {
    pari_sp av;
    r >>= 2; /* |x|/4 mod 4 */
    if (signe(x) < 0) r = 4-r;
    if (r == 1) return 0;
    av = avma;
    r = Z_issquarefree( shifti(x,-2) );
    avma = av; return r;
  }
  r &= 3; /* |x| mod 4 */
  if (signe(x) < 0) r = 4-r;
  return (r==1) ? Z_issquarefree(x) : 0;
}

GEN
quaddisc(GEN x)
{
  const pari_sp av = avma;
  long i,r,tx=typ(x);
  GEN p1,p2,f,s;

  if (!is_rational_t(tx)) err(arither1);
  f=factor(x); p1=(GEN)f[1]; p2=(GEN)f[2];
  s = gen_1;
  for (i=1; i<lg(p1); i++)
    if (odd(mael(p2,i,2))) s = gmul(s,(GEN)p1[i]);
  r=mod4(s); if (gsigne(x)<0) r=4-r;
  if (r>1) s = shifti(s,2);
  return gerepileuptoint(av, s);
}

/*********************************************************************/
/**                                                                 **/
/**                              FACTORIAL                          **/
/**                                                                 **/
/*********************************************************************/
/* return a * (a+1) * ... * b. Assume a <= b  [ note: factoring out powers of 2
 * first is slower ... ] */
GEN
seq_umul(ulong a, ulong b)
{
  pari_sp av = avma;
  ulong k, l, N, n = b - a + 1;
  long lx;
  GEN x;

  if (n < 61)
  {
    x = utoi(a);
    for (k=a+1; k<=b; k++) x = mului(k,x);
    return gerepileuptoint(av, x);
  }
  lx = 1; x = cgetg(2 + n/2, t_VEC);
  N = b + a;
  for (k = a;; k++)
  {
    l = N - k; if (l <= k) break;
    x[lx++] = (long)muluu(k,l);
  }
  if (l == k) x[lx++] = lutoi(k);
  setlg(x, lx);
  return gerepileuptoint(av, divide_conquer_prod(x, mulii));
}

GEN
mpfact(long n)
{
  if (n < 2)
  {
    if (n < 0) err(talker,"negative argument in factorial function");
    return gen_1;
  }
  return seq_umul(2UL, (ulong)n);
}

/*******************************************************************/
/**                                                               **/
/**                      LUCAS & FIBONACCI                        **/
/**                                                               **/
/*******************************************************************/
static void
lucas(ulong n, GEN *a, GEN *b)
{
  GEN z, t, zt;
  if (!n) { *a = gen_2; *b = gen_1; return; }
  lucas(n >> 1, &z, &t); zt = mulii(z, t);
  switch(n & 3) {
    case  0: *a = addsi(-2,sqri(z)); *b = addsi(-1,zt); break;
    case  1: *a = addsi(-1,zt);      *b = addsi(2,sqri(t)); break;
    case  2: *a = addsi(2,sqri(z));  *b = addsi(1,zt); break;
    case  3: *a = addsi(1,zt);       *b = addsi(-2,sqri(t));
  }
}

GEN
fibo(long n)
{
  pari_sp av = avma;
  GEN a, b;
  if (!n) return gen_0;
  lucas((ulong)(labs(n)-1), &a, &b);
  a = diviuexact(addii(shifti(a,1),b), 5);
  if (n < 0 && !odd(n)) setsigne(a, -1);
  return gerepileuptoint(av, a);
}

/*******************************************************************/
/*                                                                 */
/*                      CONTINUED FRACTIONS                        */
/*                                                                 */
/*******************************************************************/
static GEN
icopy_lg(GEN x, long l)
{
  long lx = lgefint(x);
  GEN y;

  if (lx >= l) return icopy(x);
  y = cgeti(l); affii(x, y); return y;
}

/* if y != NULL, stop as soon as partial quotients differ from y */
static GEN
Qsfcont(GEN x, GEN y, long k)
{
  GEN  z, a, b, c;
  long i, l, ly = lgefint(x[2]);

  /* / log2( (1+sqrt(5)) / 2 )  */
  l = (long)(3 + bit_accuracy_mul(ly, 1.44042009041256));
  if (k > 0 && ++k > 0 && l > k) l = k; /* beware overflow */
  if ((ulong)l > LGBITS) l = LGBITS;

  a = (GEN)x[1];
  b = (GEN)x[2];
  z = cgetg(l,t_VEC);
  l--;
  if (y) {
    pari_sp av = avma;
    if (l >= lg(y)) l = lg(y)-1;
    for (i = 1; i <= l; i++)
    {
      z[i] = y[i];
      c = b; if (!gcmp1((GEN)z[i])) c = mulii((GEN)z[i], b);
      c = subii(a, c);
      if (signe(c) < 0)
      { /* partial quotient too large */
        c = addii(c, b);
        if (signe(c) >= 0) i++; /* by 1 */
        break;
      }
      if (cmpii(c, b) >= 0)
      { /* partial quotient too small */
        c = subii(c, b);
        if (cmpii(c, b) < 0) i++; /* by 1 */
        break;
      }
      if ((i & 0xff) == 0) gerepileall(av, 2, &b, &c);
      a = b; b = c;
    }
  } else {
    a = icopy_lg(a, ly);
    b = icopy(b);
    for (i = 1; i <= l; i++)
    {
      z[i] = (long)truedvmdii(a,b,&c);
      if (c == gen_0) { i++; break; }
      affii(c, a); cgiv(c); c = a;
      a = b; b = c;
    }
  }
  i--;
  if (i > 1 && gcmp1((GEN)z[i]))
  {
    cgiv((GEN)z[i]); --i;
    z[i] = laddsi(1, (GEN)z[i]); /* unclean: leave old z[i] on stack */
  }
  setlg(z,i+1); return z;
}

static GEN
sfcont(GEN x, long k)
{
  pari_sp av;
  long lx, tx = typ(x), e, i, l;
  GEN y, a, b, c;

  if (is_scalar_t(tx))
  {
    if (gcmp0(x)) return mkvec(gen_0);
    switch(tx)
    {
      case t_INT: return mkveccopy(x);
      case t_REAL:
        av = avma; lx = lg(x);
        e = bit_accuracy(lx)-1-expo(x);
        if (e < 0) err(talker,"integral part not significant in sfcont");
        c = ishiftr_lg(x,lx,0);
        y = int2n(e);
	a = Qsfcont(mkfrac(c, y), NULL, k);
        b = mkfrac(addsi(signe(x), c), y);
	return gerepilecopy(av, Qsfcont(b,a,k));

      case t_FRAC:
        av = avma;
        return gerepileupto(av, Qsfcont(x, NULL, k));
    }
    err(typeer,"sfcont");
  }

  switch(tx)
  {
    case t_POL: return mkveccopy(x);
    case t_SER:
      av = avma;
      return gerepileupto(av, sfcont(gtrunc(x), k));
    case t_RFRAC:
      av = avma;
      l = typ(x[1]) == t_POL? lg(x[1]): 3;
      if (lg(x[2]) > l) l = lg(x[2]);
      if (k > 0 && l > k+1) l = k+1;
      y = cgetg(l,t_VEC);
      a = (GEN)x[1];
      b = (GEN)x[2];
      for (i=1; i<l; i++)
      {
	y[i] = (long)poldivrem(a,b,&c);
        if (gcmp0(c)) { i++; break; }
	a = b; b = c;
      }
      setlg(y, i); return gerepilecopy(av, y);
  }
  err(typeer,"sfcont");
  return NULL; /* not reached */
}

static GEN
sfcont2(GEN b, GEN x, long k)
{
  pari_sp av = avma;
  long l1 = lg(b), tx = typ(x), i;
  GEN y,p1;

  if (k)
  {
    if (k>=l1) err(talker,"list of numerators too short in sfcontf2");
    l1 = k+1;
  }
  y=cgetg(l1,t_VEC);
  if (l1==1) return y;
  if (is_scalar_t(tx))
  {
    if (!is_intreal_t(tx) && tx != t_FRAC) err(typeer,"sfcont2");
  }
  else if (tx == t_SER) x = gtrunc(x);

  if (!gcmp1((GEN)b[1])) x = gmul((GEN)b[1],x);
  i = 2; y[1] = lfloor(x); p1 = gsub(x,(GEN)y[1]);
  for (  ; i<l1 && !gcmp0(p1); i++)
  {
    x = gdiv((GEN)b[i],p1);
    if (tx == t_REAL)
    {
      long e = expo(x);
      if (e>0 && (e>>TWOPOTBITS_IN_LONG)+3 > lg(x)) break;
    }
    y[i] = lfloor(x);
    p1 = gsub(x,(GEN)y[i]);
  }
  setlg(y,i);
  return gerepilecopy(av,y);
}


GEN
gcf(GEN x)
{
  return sfcont(x,0);
}

GEN
gcf2(GEN b, GEN x)
{
  return contfrac0(x,b,0);
}

GEN
gboundcf(GEN x, long k)
{
  return sfcont(x,k);
}

GEN
contfrac0(GEN x, GEN b, long flag)
{
  long lb, tb, i;
  GEN y;

  if (!b || gcmp0(b)) return sfcont(x,flag);
  tb = typ(b);
  if (tb == t_INT) return sfcont(x,itos(b));
  if (! is_matvec_t(tb)) err(typeer,"contfrac0");

  lb = lg(b); if (lb==1) return cgetg(1,t_VEC);
  if (tb != t_MAT) return sfcont2(b,x,flag);
  if (lg(b[1])==1) return sfcont(x,flag);
  y = cgetg(lb, t_VEC); for (i=1; i<lb; i++) y[i] = mael(b,i,1);
  x = sfcont2(y,x,flag); return x;
}

GEN
pnqn(GEN x)
{
  pari_sp av = avma;
  long i, lx, ly, tx = typ(x);
  GEN p0, p1, q0, q1, a, b, p2, q2;

  if (! is_matvec_t(tx)) err(typeer,"pnqn");
  lx=lg(x); if (lx==1) return idmat(2);
  p0=gen_1; q0=gen_0;
  if (tx != t_MAT)
  {
    p1 = (GEN)x[1]; q1 = gen_1;
    for (i=2; i<lx; i++)
    {
      a = (GEN)x[i];
      p2 = gadd(gmul(a,p1),p0); p0=p1; p1=p2;
      q2 = gadd(gmul(a,q1),q0); q0=q1; q1=q2;
    }
  }
  else
  {
    ly = lg(x[1]);
    if (ly==2)
    {
      p1 = cgetg(lx,t_VEC); for (i=1; i<lx; i++) p1[i] = mael(x,i,1);
      return pnqn(p1);
    }
    if (ly!=3) err(talker,"incorrect size in pnqn");
    p1=gcoeff(x,2,1); q1=gcoeff(x,1,1);
    for (i=2; i<lx; i++)
    {
      a = gcoeff(x,2,i); b = gcoeff(x,1,i);
      p2 = gadd(gmul(a,p1),gmul(b,p0)); p0=p1; p1=p2;
      q2 = gadd(gmul(a,q1),gmul(b,q0)); q0=q1; q1=q2;
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(p1,q1), mkcol2(p0,q0)));
}

/* x t_INTMOD. Look for coprime integers a<=A and b<=B, such that a/b = x */
GEN
bestappr_mod(GEN x, GEN A, GEN B)
{
  long i,lx,tx;
  GEN y;
  tx = typ(x);
  switch(tx)
  {
    case t_INTMOD:
    {
      pari_sp av = avma;
      GEN a,b,d, t = cgetg(3, t_FRAC);
      if (! ratlift((GEN)x[2], (GEN)x[1], &a,&b,A,B)) return NULL;
      if (is_pm1(b)) return icopy_av(a, (GEN)av);
      d = gcdii(a,b);
      if (!is_pm1(d)) { avma = av; return NULL; }
      cgiv(d);
      t[1] = (long)a;
      t[2] = (long)b; return t;
    }
    case t_COMPLEX: case t_POL: case t_SER: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      y = init_gen_op(x, tx, &lx, &i);
      for (; i<lx; i++)
      {
        GEN t = bestappr_mod((GEN)x[i],A,B);
        if (!t) return NULL;
        y[i] = (long)t;
      }
      return y;
  }
  err(typeer,"bestappr0");
  return NULL; /* not reached */
}

GEN
bestappr(GEN x, GEN k)
{
  pari_sp av = avma;
  long tx = typ(x), tk = typ(k), lx, i;
  GEN p0, p1, p, q0, q1, q, a, y;

  if (tk != t_INT)
  {
    long e;
    if (tk != t_REAL && tk != t_FRAC)
      err(talker,"incorrect bound type in bestappr");
    k = gcvtoi(k,&e);
  }
  if (signe(k) <= 0) k = gen_1;
  switch(tx)
  {
    case t_INT:
      avma = av; return icopy(x);

    case t_FRAC:
      if (cmpii((GEN)x[2],k) <= 0) { avma = av; return gcopy(x); }
      y = x;
      p1 = gen_1; a = p0 = gfloor(x); q1 = gen_0; q0 = gen_1;
      while (cmpii(q0,k) <= 0)
      {
	x = gsub(x,a); /* 0 <= x < 1 */
	if (gcmp0(x)) { p1 = p0; q1 = q0; break; }

	x = ginv(x); /* > 1 */
        a = typ(x)==t_INT? x: divii((GEN)x[1], (GEN)x[2]);
        if (cmpii(a,k) > 0)
        { /* next partial quotient will overflow limits */
          GEN n, d;
          a = divii(subii(k, q1), q0);
	  p = addii(mulii(a,p0), p1); p1=p0; p0=p;
          q = addii(mulii(a,q0), q1); q1=q0; q0=q;
          /* compare |y-p0/q0|, |y-p1/q1| */
          n = (GEN)y[1];
          d = (GEN)y[2];
          if (absi_cmp(mulii(q1, subii(mulii(q0,n), mulii(d,p0))),
                       mulii(q0, subii(mulii(q1,n), mulii(d,p1)))) < 0)
                       { p1 = p0; q1 = q0; }
          break;
        }
	p = addii(mulii(a,p0), p1); p1=p0; p0=p;
        q = addii(mulii(a,q0), q1); q1=q0; q0=q;
      }
      return gerepileupto(av, gdiv(p1,q1));

    case t_REAL: {
      GEN kr;

      if (!signe(x)) return gen_0; /* faster. Besides itor crashes on x = 0 */
      kr = itor(k, lg(x));
      y = x;
      p1 = gen_1; a = p0 = floorr(x); q1 = gen_0; q0 = gen_1;
      while (cmpii(q0,k) <= 0)
      {
	x = mpsub(x,a); /* 0 <= x < 1 */
	if (!signe(x)) { p1 = p0; q1 = q0; break; }

	x = ginv(x); /* > 1 */
        if (cmprr(x,kr) > 0)
        { /* next partial quotient will overflow limits */
          a = divii(subii(k, q1), q0);
	  p = addii(mulii(a,p0), p1); p1=p0; p0=p;
          q = addii(mulii(a,q0), q1); q1=q0; q0=q;
          /* compare |y-p0/q0|, |y-p1/q1| */
          if (absr_cmp(mpmul(q1, mpsub(mulir(q0,y), p0)),
                       mpmul(q0, mpsub(mulir(q1,y), p1))) < 0)
                       { p1 = p0; q1 = q0; }
          break;
        }
        a = mptrunc(x); /* mptrunc(x) may raise precer */
	p = addii(mulii(a,p0), p1); p1=p0; p0=p;
        q = addii(mulii(a,q0), q1); q1=q0; q0=q;
      }
      return gerepileupto(av, gdiv(p1,q1));
   }
   case t_COMPLEX: case t_POL: case t_SER: case t_RFRAC:
   case t_VEC: case t_COL: case t_MAT:
      y = init_gen_op(x, tx, &lx, &i);
      for (; i<lx; i++) y[i] = (long)bestappr((GEN)x[i],k);
      return y;
  }
  err(typeer,"bestappr");
  return NULL; /* not reached */
}

GEN
bestappr0(GEN x, GEN a, GEN b)
{
  pari_sp av;
  GEN t;
  if (!b) return bestappr(x,a);
  av = avma;
  t = bestappr_mod(x,a,b);
  if (!t) { avma = av; return gen_m1; }
  return t;
}

/***********************************************************************/
/**                                                                   **/
/**         FUNDAMENTAL UNIT AND REGULATOR (QUADRATIC FIELDS)         **/
/**                                                                   **/
/***********************************************************************/

GEN
gfundunit(GEN x) { return garith_proto(fundunit,x,1); }

static GEN
get_quad(GEN f, GEN pol, long r)
{
  GEN y = cgetg(4,t_QUAD), c = (GEN)f[2], p1 = (GEN)c[1], q1 = (GEN)c[2];

  y[1] = (long)pol;
  y[2] = r? lsubii(p1,q1): (long)p1;
  y[3] = (long)q1; return y;
}

/* replace f by f * [a,1; 1,0] */
static void
update_f(GEN f, GEN a)
{
  GEN p1;
  p1 = gcoeff(f,1,1);
  coeff(f,1,1) = laddii(mulii(a,p1), gcoeff(f,1,2));
  coeff(f,1,2) = (long)p1;

  p1 = gcoeff(f,2,1);
  coeff(f,2,1) = laddii(mulii(a,p1), gcoeff(f,2,2));
  coeff(f,2,2) = (long)p1;
}

GEN
fundunit(GEN x)
{
  pari_sp av = avma, av2, lim;
  long r, flp, flq;
  GEN pol, y, a, u, v, u1, v1, sqd, f;

  check_quaddisc_real(x, &r, "fundunit");
  sqd = sqrti(x); av2 = avma; lim = stack_lim(av2,2);
  a = shifti(addsi(r,sqd),-1);
  f = mkmat2(mkcol2(a, gen_1), mkcol2(gen_1, gen_0));
  u = stoi(r); v = gen_2;
  for(;;)
  {
    u1 = subii(mulii(a,v),u);       flp = equalii(u,u1); u = u1;
    v1 = divii(subii(x,sqri(u)),v); flq = equalii(v,v1); v = v1;
    if (flq) break; a = divii(addii(sqd,u),v);
    if (flp) break; update_f(f,a);
    if (low_stack(lim, stack_lim(av2,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"fundunit");
      gerepileall(av2,4, &a,&f,&u,&v);
    }
  }
  pol = quadpoly(x);
  y = get_quad(f,pol,r);
  if (!flq) v1 = y; else { update_f(f,a); v1 = get_quad(f,pol,r); }

  y = gdiv(v1, gconj(y));
  if (signe(y[3]) < 0) y = gneg(y);
  return gerepileupto(av, y);
}

GEN
gregula(GEN x, long prec) { return garith_proto2gs(regula,x,prec); }

GEN
regula(GEN x, long prec)
{
  pari_sp av = avma, av2, lim;
  long r, fl, rexp;
  GEN reg, rsqd, y, u, v, u1, v1, sqd = sqrti(x);

  check_quaddisc_real(x, &r, "regula");
  rsqd = gsqrt(x,prec);
  rexp = 0; reg = stor(2, prec);
  av2 = avma; lim = stack_lim(av2,2);
  u = stoi(r); v = gen_2;
  for(;;)
  {
    u1 = subii(mulii(divii(addii(u,sqd),v), v), u);
    v1 = divii(subii(x,sqri(u1)),v); fl = equalii(v,v1);
    if (fl || equalii(u,u1)) break;
    reg = mulrr(reg, divri(addir(u1,rsqd),v));
    rexp += expo(reg); setexpo(reg,0);
    u = u1; v = v1;
    if (rexp & ~EXPOBITS) err(talker,"exponent overflow in regula");
    if (low_stack(lim, stack_lim(av2,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"regula");
      gerepileall(av2,3, &reg,&u,&v);
    }
  }
  reg = gsqr(reg); setexpo(reg,expo(reg)-1);
  if (fl) reg = mulrr(reg, divri(addir(u1,rsqd),v));
  y = logr_abs(divri(reg,v));
  if (rexp)
  {
    u1 = mulsr(rexp, mplog2(prec));
    setexpo(u1, expo(u1)+1);
    y = addrr(y,u1);
  }
  return gerepileupto(av, y);
}

/*************************************************************************/
/**                                                                     **/
/**                            CLASS NUMBER                             **/
/**                                                                     **/
/*************************************************************************/

static GEN
gclassno(GEN x) { return garith_proto(classno,x,1); }

static GEN
gclassno2(GEN x) { return garith_proto(classno2,x,1); }

GEN
qfbclassno0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return gclassno(x);
    case 1: return gclassno2(x);
    default: err(flagerr,"qfbclassno");
  }
  return NULL; /* not reached */
}

/* f^h = 1, return order(f) */
static GEN
find_order(GEN f, GEN h)
{
  GEN fh, p,e;
  long i,j,lim;

  p = decomp(h);
  e =(GEN)p[2];
  p =(GEN)p[1];
  for (i=1; i<lg(p); i++)
  {
    lim = itos((GEN)e[i]);
    for (j=1; j<=lim; j++)
    {
      GEN p1 = diviiexact(h,(GEN)p[i]);
      fh = powgi(f,p1);
      if (!is_pm1(fh[1])) break;
      h = p1;
    }
  }
  return h;
}

static GEN
end_classno(GEN h, GEN hin, GEN forms, long lform)
{
  long i,com;
  GEN a,b,p1,q,fh,fg, f = (GEN)forms[0];

  h = find_order(f,h); /* H = <f> */
  q = diviiround(hin, h); /* approximate order of G/H */
  for (i=1; i < lform; i++)
  {
    pari_sp av = avma;
    fg = powgi((GEN)forms[i], h);
    fh = powgi(fg, q);
    a = (GEN)fh[1];
    if (is_pm1(a)) continue;
    b = (GEN)fh[2]; p1 = fg;
    for (com=1; ; com++, p1 = gmul(p1,fg))
      if (equalii((GEN)p1[1], a) && absi_equal((GEN)p1[2], b)) break;
    if (signe(p1[2]) == signe(b)) com = -com;
    /* f_i ^ h(q+com) = 1 */
    q = addsi(com,q);
    if (gcmp0(q))
    { /* f^(ih) != 1 for all 0 < i <= oldq. Happen if the original upper bound
         for h was wrong */
      long c;
      p1 = fh;
      for (c=1; ; c++, p1 = gmul(p1,fh))
        if (gcmp1((GEN)p1[1])) break;
      q = mulsi(-com, find_order(fh, utoipos((ulong)c)));
    }
    q = gerepileuptoint(av, q);
  }
  return mulii(q,h);
}

/* r = x mod 4 */
static GEN
conductor_part(GEN x, long r, GEN *ptD, GEN *ptreg, GEN *ptfa)
{
  long n,i,k,s=signe(x),fl2;
  GEN e,p,H,d,D,fa,reg;

  fa = auxdecomp(absi(x),1);
  e = gtovecsmall((GEN)fa[2]);
  fa = (GEN)fa[1];
  n = lg(fa); d = gen_1;
  for (i=1; i<n; i++)
    if (e[i] & 1) d = mulii(d,(GEN)fa[i]);
  if (r) fl2 = 0; else { fl2 = 1; d = shifti(d,2); }
  H = gen_1; D = (s<0)? negi(d): d; /* d = abs(D) */
  /* f \prod_{p|f}  [ 1 - (D/p) p^-1 ] */
  for (i=1; i<n; i++)
  {
    p = (GEN)fa[i];
    k = e[i];
    if (fl2 && i==1) k -= 2; /* p = 2 */
    if (k >= 2)
    {
      H = mulii(H, subis(p, kronecker(D,p)));
      if (k>=4) H = mulii(H, powiu(p,(k>>1)-1));
    }
  }

  /* divide by [ O^* : O_K^* ] */
  if (s < 0)
  {
    reg = NULL;
    switch(itos_or_0(d))
    {
      case 4: H = divis(H,2); break;
      case 3: H = divis(H,3); break;
    }
  } else {
    reg = regula(D,DEFAULTPREC);
    if (!equalii(x,D))
      H = divii(H, ground(gdiv(regula(x,DEFAULTPREC), reg)));
  }
  if (ptreg) *ptreg = reg;
  if (ptfa)  *ptfa = fa;
  *ptD = D; return H;
}

static long
two_rank(GEN x)
{
  GEN p = (GEN)decomp(absi(x))[1];
  long l = lg(p)-1;
#if 0 /* positive disc not needed */
  if (signe(x) > 0)
  {
    long i;
    for (i=1; i<=l; i++)
      if (mod4((GEN)p[i]) == 3) { l--; break; }
  }
#endif
  return l-1;
}

static GEN
sqr_primeform(GEN x, long f) { return redimag(gsqr(primeform_u(x, f))); }

#define MAXFORM 11
#define _low(to, x) { GEN __x = (GEN)(x); to = signe(__x)?modBIL(__x):0; }

/* h(x) for x<0 using Baby Step/Giant Step.
 * Assumes G is not too far from being cyclic.
 *
 * Compute G^2 instead of G so as to kill most of the non-cyclicity */
GEN
classno(GEN x)
{
  pari_sp av = avma, av2, lim;
  long r2,c,lforms,k,l,i,j,com,s, forms[MAXFORM];
  GEN count,index,tabla,tablb,hash,p1,p2,hin,h,f,fh,fg,ftest;
  GEN Hf, D;
  byteptr p = diffptr;

  if (signe(x) >= 0) return classno2(x);

  check_quaddisc(x, &s, &k, "classno");
  if (cmpiu(x,12) <= 0) return gen_1;

  Hf = conductor_part(x, k, &D, NULL, NULL);
  if (cmpiu(D,12) <= 0) return gerepilecopy(av, Hf);

  p2 = gsqrt(absi(D),DEFAULTPREC);
  p1 = mulrr(divrr(p2,mppi(DEFAULTPREC)), dbltor(1.005)); /*overshoot by 0.5%*/
  s = itos_or_0( truncr(shiftr(sqrtr(p2), 1)) );
  if (!s) err(talker,"discriminant too big in classno");
  if (s < 10) s = 200;
  else if (s < 20) s = 1000;
  else if (s < 5000) s = 5000;

  c = lforms = 0; maxprime_check(s);
  while (c <= s)
  {
    long d;
    NEXT_PRIME_VIADIFF(c,p);

    k = krois(D,c); if (!k) continue;
    if (k > 0)
    {
      if (lforms < MAXFORM) forms[lforms++] = c;
      d = c - 1;
    }
    else
      d = c + 1;
    av2 = avma;
    divrsz(mulsr(c,p1),d, p1);
    avma = av2;
  }
  r2 = two_rank(D);
  h = hin = ground(gmul2n(p1, -r2));
  s = 2*itos(gceil(sqrtnr(p1, 4)));
  if (s > 10000) s = 10000;

  count = new_chunk(256); for (i=0; i<=255; i++) count[i]=0;
  index = new_chunk(257);
  tabla = new_chunk(10000);
  tablb = new_chunk(10000);
  hash  = new_chunk(10000);
  f = sqr_primeform(D, forms[0]);
  p1 = fh = powgi(f, h);
  for (i=0; i<s; i++, p1 = compimag(p1,f))
  {
    _low(tabla[i], p1[1]);
    _low(tablb[i], p1[2]); count[tabla[i]&255]++;
  }
  /* follow the idea of counting sort to avoid maintaining linked lists in
   * hashtable */
  index[0]=0; for (i=0; i< 255; i++) index[i+1] = index[i]+count[i];
  /* index[i] = # of forms hashing to <= i */
  for (i=0; i<s; i++) hash[ index[tabla[i]&255]++ ] = i;
  index[0]=0; for (i=0; i<=255; i++) index[i+1] = index[i]+count[i];
  /* hash[index[i-1]..index[i]-1] = forms hashing to i */

  fg = gpowgs(f,s); av2 = avma; lim = stack_lim(av2,2);
  ftest = gpowgs(p1,0);
  for (com=0; ; com++)
  {
    long j1, j2;
    GEN a, b;
    a = (GEN)ftest[1]; _low(k, a);
    b = (GEN)ftest[2]; _low(l, b); j = k&255;
    for (j1=index[j]; j1 < index[j+1]; j1++)
    {
      j2 = hash[j1];
      if (tabla[j2] == k && tablb[j2] == l)
      {
        p1 = gmul(gpowgs(f,j2),fh);
        if (equalii((GEN)p1[1], a) && absi_equal((GEN)p1[2], b))
        { /* p1 = ftest or ftest^(-1), we are done */
          if (signe(p1[2]) == signe(b)) com = -com;
          h = addii(addis(h,j2), mulss(s,com));
          forms[0] = (long)f;
          for (i=1; i<lforms; i++)
            forms[i] = (long)sqr_primeform(D, forms[i]);
          h = end_classno(h,hin,forms,lforms);
          h = mulii(h,Hf);
          return gerepileuptoint(av, shifti(h, r2));
        }
      }
    }
    ftest = gmul(ftest,fg);
    if (is_pm1(ftest[1])) err(impl,"classno with too small order");
    if (low_stack(lim, stack_lim(av2,2))) ftest = gerepileupto(av2,ftest);
  }
}

/* use Euler products */
GEN
classno2(GEN x)
{
  pari_sp av = avma;
  const long prec = DEFAULTPREC;
  long n, i, k, r, s;
  GEN p1, p2, S, p4, p5, p7, Hf, Pi, reg, logd, d, dr, D, half;

  check_quaddisc(x, &s, &r, "classno2");
  if (s < 0 && cmpiu(x,12) <= 0) return gen_1;

  Hf = conductor_part(x, r, &D, &reg, NULL);
  if (s < 0 && cmpiu(D,12) <= 0) return gerepilecopy(av, Hf); /* |D| < 12*/

  Pi = mppi(prec);
  d = absi(D); dr = itor(d, prec);
  logd = logr_abs(dr);
  p1 = sqrtr(divrr(mulir(d,logd), gmul2n(Pi,1)));
  if (s > 0)
  {
    p2 = subsr(1, gmul2n(divrr(logr_abs(reg),logd),1));
    if (cmprr(gsqr(p2), divsr(2,logd)) >= 0) p1 = mulrr(p2,p1);
  }
  n = itos_or_0( mptrunc(p1) );
  if (!n) err(talker,"discriminant too large in classno");

  p4 = divri(Pi,d);
  p7 = ginv(sqrtr_abs(Pi));
  p1 = sqrtr_abs(dr);
  S = gen_0;
  half = real2n(-1, prec);
  if (s > 0)
  {
    for (i=1; i<=n; i++)
    {
      k = krois(D,i); if (!k) continue;
      p2 = mulir(sqru(i), p4);
      p5 = subsr(1, mulrr(p7,incgamc(half,p2,prec)));
      p5 = addrr(divrs(mulrr(p1,p5),i), eint1(p2,prec));
      S = (k>0)? addrr(S,p5): subrr(S,p5);
    }
    S = shiftr(divrr(S,reg),-1);
  }
  else
  {
    p1 = gdiv(p1,Pi);
    for (i=1; i<=n; i++)
    {
      k = krois(D,i); if (!k) continue;
      p2 = mulir(sqru(i), p4);
      p5 = subsr(1, mulrr(p7,incgamc(half,p2,prec)));
      p5 = addrr(p5, divrr(divrs(p1,i), mpexp(p2)));
      S = (k>0)? addrr(S,p5): subrr(S,p5);
    }
  }
  return gerepileuptoint(av, mulii(Hf, roundr(S)));
}

GEN
hclassno(GEN x)
{
  long d, a, b, h, b2, f;

  if (typ(x) != t_INT) err(typeer,"hclassno");

  d = -itos(x); if (d>0 || (d & 3) > 1) return gen_0;
  if (!d) return gdivgs(gen_1,-12);
  if (-d > (VERYBIGINT>>1))
    err(talker,"discriminant too big in hclassno. Use quadclassunit");
  h = 0; b = d&1; b2 = (1-d)>>2; f=0;
  if (!b)
  {
    for (a=1; a*a<b2; a++)
      if (b2%a == 0) h++;
    f = (a*a==b2); b=2; b2=(4-d)>>2;
  }
  while (b2*3+d<0)
  {
    if (b2%b == 0) h++;
    for (a=b+1; a*a < b2; a++)
      if (b2%a == 0) h += 2;
    if (a*a == b2) h++;
    b += 2; b2 = (b*b-d)>>2;
  }
  if (b2*3+d==0)
  {
    GEN y = cgetg(3,t_FRAC);
    y[1] = (long)utoipos(3*h+1);
    y[2] = (long)utoipos(3); return y;
  }
  if (f)
  {
    GEN y = cgetg(3,t_FRAC);
    y[1] = (long)utoipos(2*h+1);
    y[2] = (long)gen_2; return y;
  }
  return utoipos(h);
}

