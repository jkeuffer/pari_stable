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

/*******************************************************************/
/*                                                                 */
/*                       BASIC NF OPERATIONS                       */
/*                          (continued 2)                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
extern GEN mul_content(GEN cx, GEN cy);
extern long polegal_spec(GEN x, GEN y);
extern GEN mulmat_pol(GEN A, GEN x);
extern GEN idealsqrtn(GEN nf, GEN x, GEN gn, int strict);
extern GEN lift_if_rational(GEN x);
extern GEN get_mul_table(GEN x,GEN basden,GEN invbas);
extern GEN rnfallbase(GEN nf, GEN pol, GEN *pD, GEN *pd, GEN *pfi);

GEN
matbasistoalg(GEN nf,GEN x)
{
  long i, j, li, lx = lg(x);
  GEN c, z = cgetg(lx,t_MAT);

  if (typ(x) != t_MAT) err(talker,"argument must be a matrix in matbasistoalg");
  if (lx == 1) return z;
  li = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    c = cgetg(li,t_COL); z[j] = (long)c;
    for (i=1; i<li; i++) c[i] = (long)basistoalg(nf,gcoeff(x,i,j));
  }
  return z;
}

GEN
matalgtobasis(GEN nf,GEN x)
{
  long i, j, li, lx = lg(x);
  GEN c, z = cgetg(lx, t_MAT);

  if (typ(x) != t_MAT) err(talker,"argument must be a matrix in matalgtobasis");
  if (lx == 1) return z;
  li = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    c = cgetg(li,t_COL); z[j] = (long)c;
    for (i=1; i<li; i++) c[i] = (long)_algtobasis_cp(nf, gcoeff(x,i,j));
  }
  return z;
}

GEN
_checkrnfeq(GEN x)
{
  if (typ(x) == t_VEC)
    switch(lg(x))
    {
      case 13: /* checkrnf(x); */ return (GEN)x[11];
      case  4: return x;
    }
  return NULL;
}

GEN
checkrnfeq(GEN x)
{
  x = _checkrnfeq(x);
  if (!x) err(talker,"please apply rnfequation(,,1)");
  return x;
}

GEN
eltreltoabs(GEN rnfeq, GEN x)
{
  long i, k, va;
  pari_sp av = avma;
  GEN polabs, teta, alpha, s;

  rnfeq = checkrnfeq(rnfeq);
  polabs= (GEN)rnfeq[1];
  alpha = (GEN)rnfeq[2];
  k     = itos((GEN)rnfeq[3]);

  va = varn(polabs);
  if (gvar(x) > va) x = scalarpol(x,va);
  /* Mod(X + k alpha, polabs(X)), alpha root of the polynomial defining base */
  teta = gmodulcp(gsub(polx[va], gmulsg(k,lift_intern(alpha))), polabs);
  s = gzero;
  for (i=lgef(x)-1; i>1; i--)
  {
    GEN c = (GEN)x[i];
    long tc = typ(c);
    switch(tc)
    {
      case t_POLMOD: c = (GEN)c[2]; /* fall through */
      case t_POL:    c = poleval(c, alpha); break;
      default:
        if (!is_const_t(tc)) err(talker, "incorrect data in eltreltoabs");
    }
    s = gadd(c, gmul(teta,s));
  }
  return gerepileupto(av, s);
}

#if 0
extern GEN get_roots(GEN x,long r1,long prec);
extern GEN quicktrace(GEN x, GEN sym);
static GEN
rnfmakematrices(GEN rnf)
{
  long i, j, k, n, ru, vnf;
  GEN nf, pol, sym, ro, w, ronf, z, vecM, T;

  pol = (GEN)rnf[1]; n = degpol(pol); sym = polsym(pol, n-1);
  ro  = (GEN)rnf[6];
  w   = (GEN)rnf[7]; w = (GEN)w[1];
  nf  = (GEN)rnf[10]; vnf = varn(nf[1]);
  T = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    GEN c = cgetg(n+1,t_COL); T[j] = (long)c;
    for (i=1; i<=n; i++)
    {
      GEN d = gres(gmul((GEN)w[i],(GEN)w[j]), pol);
      c[i] = (long)lift_if_rational( quicktrace(d, sym) );
    }
  }
  w = lift(w); ru = lg(ro)-1; ronf = (GEN)nf[6];
  vecM = cgetg(ru+1,t_VEC);
  for (k=1; k<=ru; k++)
  {
    GEN rok = (GEN)ro[k], M = cgetg(n+1,t_MAT);
    long l = lg(rok);
    vecM[k] = (long)M;
    for (j=1; j<=n; j++)
    {
      GEN a, c = cgetg(l,t_COL); M[j] = (long)c;
      a = gsubst((GEN)w[j], vnf, (GEN)ronf[k]);
      for (i=1; i<l; i++) c[i] = (long)poleval(a, (GEN)rok[i]);
    }
  }

  z = cgetg(8,t_VEC);
  z[1] = (long)vecM;
  z[4] = (long)T;
  /* dummies */
  z[2] = lgetg(1, t_VEC);
  z[3] = lgetg(1, t_VEC);
  z[5] = lgetg(1,t_MAT);
  z[6] = lgetg(1,t_MAT);
  z[7] = lgetg(1,t_MAT); return z;
}
static GEN
vec2s(long a, long b)
{
  GEN z = cgetg(3, t_VEC);
  z[1] = (long)stoi(a);
  z[2] = (long)stoi(b); return z;
}

static GEN
rnf_roots(GEN nf, GEN pol, long prec, GEN *pts)
{
  long r1, r2, j, v = varn(nf[1]), n = degpol(pol);
  GEN s, r, ro;

  nf_get_sign(nf, &r1, &r2);
  s = cgetg(r1+r2+1,t_VEC);
  r = cgetg(r1+r2+1,t_VEC);
  ro = (GEN)nf[6];
  for (j=1; j<=r1; j++)
  {
    long r1j = 0;
    ro = roots(gsubst(pol,v,(GEN)ro[j]), prec);
    while (r1j<n && gcmp0(gimag((GEN)ro[r1j+1]))) r1j++;
    s[j] = (long)vec2s(r1j, (n-r1j)>>1);
    r[j] = (long)get_roots(ro, r1j, 0);
  }
  for (; j<=r1+r2; j++)
  {
    ro = roots(gsubst(pol,v,(GEN)ro[j]), prec);
    s[j] = (long)vec2s(0, n);
    r[j] = (long)ro;
  }
  *pts = s; return r;
}

#else /* dummies */
static GEN rnfmakematrices(GEN rnf) { (void)rnf; return cgetg(1, t_VEC); }
static GEN
rnf_roots(GEN nf, GEN pol, long prec, GEN *pts) {
  (void)nf; (void)pol; (void)prec;
  *pts = cgetg(1,t_VEC); return cgetg(1, t_VEC);
}
#endif

static GEN
modulereltoabs(GEN rnf, GEN x)
{
  GEN w = (GEN)x[1], I = (GEN)x[2], nf = (GEN)rnf[10], rnfeq = (GEN)rnf[11];
  GEN M, basnf, cobasnf, T = (GEN)nf[1];
  long i, j, k, n = lg(w)-1, m = degpol(T);

  M = cgetg(n*m+1, t_VEC);
  basnf = gsubst((GEN)nf[7], varn(T), (GEN)rnfeq[2]);
  basnf = Q_primitive_part(basnf, &cobasnf); /* remove denom. --> faster */
  for (k=i=1; i<=n; i++)
  {
    GEN c0, om = (GEN)w[i], id = (GEN)I[i];

    om = Q_primitive_part(eltreltoabs(rnfeq, om), &c0);
    c0 = mul_content(c0, cobasnf);
    for (j=1; j<=m; j++)
    {
      GEN c, z = Q_primitive_part(gmul(basnf,(GEN)id[j]), &c);
      z = lift_intern(gmul(om, z));
      c = mul_content(c, c0); if (c) z = gmul(c, z);
      M[k++] = (long)z;
    }
  }
  return M;
}

GEN
hnfcenter_ip(GEN M)
{
  long i, j, k, N = lg(M)-1;
  GEN a, Mj, Mk;

  for (j=N-1; j>0; j--)
  {
    Mj = (GEN)M[j]; a = (GEN)Mj[j];
    if (cmpis(a, 2) <= 0) continue;
    a = shifti(a, -1);
    for (k = j+1; k <= N; k++)
    {
      Mk = (GEN)M[k];
      if (cmpii((GEN)Mk[j],a) > 0)
        for (i = 1; i <= j; i++) Mk[i] = lsubii((GEN)Mk[i], (GEN)Mj[i]);
    }
  }
  return M;
}

static GEN
makenfabs(GEN rnf)
{
  GEN M, d, rnfeq, pol, nf, NF = zerovec(9);
  long n;

  rnfeq = (GEN)rnf[11]; pol = (GEN)rnfeq[1];
  nf = (GEN)rnf[10];

  M = modulereltoabs(rnf, (GEN)rnf[7]);
  n = lg(M)-1;
  M = vecpol_to_mat(Q_remove_denom(M, &d), n);
  if (d) M = gdiv(hnfcenter_ip(hnfmodid(M, d)), d);
  else   M = idmat(n);

  NF[1] = (long)pol;
  NF[3] = (long)mulii(gpowgs((GEN)nf[3], degpol(rnf[1])),
                      idealnorm(nf, (GEN)rnf[3]));
  NF[7] = (long)lift_intern( mat_to_vecpol(M,varn(pol)) );
  NF[8] = (long)linvmat(M);
  NF[9] = (long)get_mul_table(pol, (GEN)NF[7], (GEN)NF[8]);
  /* possibly wrong, but correct prime divisors [for primedec] */
  NF[4] = (long)Q_denom((GEN)NF[7]);
  return NF;
}

#define NFABS 1
#define NORMS 2
GEN
check_and_build_nfabs(GEN rnf) {
  return check_and_build_obj(rnf, NFABS, &makenfabs);
}
static GEN makenorms(GEN rnf);
GEN
check_and_build_norms(GEN rnf) {
  return check_and_build_obj(rnf, NORMS, &makenorms);
}

GEN
rnfinitalg(GEN nf, GEN pol, long prec)
{
  pari_sp av = avma;
  long vpol;
  GEN rnf, delta, bas, D,d,f, B;

  if (typ(pol)!=t_POL) err(notpoler,"rnfinitalg");
  nf = checknf(nf); vpol = varn(pol);
  pol = fix_relative_pol(nf,pol,0);
  if (vpol >= varn(nf[1]))
    err(talker,"main variable must be of higher priority in rnfinitalg");

  bas = rnfallbase(nf,pol, &D,&d, &f);
  B = matbasistoalg(nf,(GEN)bas[1]);
  bas[1] = (long)lift_if_rational( mat_to_vecpol(B,vpol) );
  delta = cgetg(3,t_VEC);
  delta[1] = (long)D;
  delta[2] = (long)d;

  rnf = cgetg(13, t_VEC);
  rnf[1] = (long)pol;
  rnf[3] = (long)delta;
  rnf[4] = (long)f;
  rnf[6] = (long)rnf_roots(nf, lift(pol), prec, (GEN*)rnf+2);
  rnf[7] = (long)bas;
  rnf[8] = (long)lift_if_rational( invmat(B) );
  rnf[9] = lgetg(1,t_VEC); /* dummy */
  rnf[10]= (long)nf;
  rnf[11] = (long)rnfequation2(nf,pol);
  rnf[12] = zero;
  rnf[5] = (long)rnfmakematrices(rnf);
  return gerepilecopy(av, rnf);
}

GEN
rnfbasistoalg(GEN rnf,GEN x)
{
  long tx = typ(x), lx = lg(x), i;
  pari_sp av = avma;
  GEN p1, z, nf;

  checkrnf(rnf);
  switch(tx)
  {
    case t_VEC: case t_COL:
      p1 = cgetg(lx,t_COL); nf = (GEN)rnf[10];
      for (i=1; i<lx; i++) p1[i] = (long)_basistoalg(nf, (GEN)x[i]);
      p1 = gmul(gmael(rnf,7,1), p1);
      return gerepileupto(av, gmodulcp(p1,(GEN)rnf[1]));

    case t_MAT:
      z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long)rnfbasistoalg(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      return gcopy(x);

    default: z = cgetg(3,t_POLMOD);
      z[1] = lcopy((GEN)rnf[1]);
      z[2] = lmul(x,polun[varn(rnf[1])]); return z;
  }
}

/* assume x is a t_POLMOD */
GEN
lift_to_pol(GEN x)
{
  GEN y = (GEN)x[2];
  return (typ(y) != t_POL)? gtopoly(y,varn(x[1])): y;
}

GEN
rnfalgtobasis(GEN rnf,GEN x)
{
  long tx = typ(x), i, lx;
  pari_sp av = avma;
  GEN z;

  checkrnf(rnf);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfalgtobasis(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      if (!polegal_spec((GEN)rnf[1],(GEN)x[1]))
	err(talker,"not the same number field in rnfalgtobasis");
      x = lift_to_pol(x); /* fall through */
    case t_POL:
    { /* cf algtobasis_i */
      GEN P = (GEN)rnf[1];
      long N = degpol(P);
      if (degpol(x) >= N) x = gres(x,P);
      return gerepileupto(av, mulmat_pol((GEN)rnf[8], x));
    }
  }
  return gscalcol(x, degpol(rnf[1]));
}

/* x doit etre un polymod ou un polynome ou un vecteur de tels objets... */
GEN
rnfelementreltoabs(GEN rnf,GEN x)
{
  long i, lx, tx = typ(x);
  GEN z;

  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long)rnfelementreltoabs(rnf, (GEN)x[i]);
      return z;

    case t_POLMOD: x = lift_to_pol(x); /* fall through */
    case t_POL: return eltreltoabs(rnf, x);
    default: return gcopy(x);
  }
}

/* assume x,T,pol t_POL. T defines base field, pol defines rnf over T.
 * x an absolute element of the extension */
GEN
get_theta_abstorel(GEN T, GEN pol, GEN k)
{
  return gmodulcp(gadd(polx[varn(pol)],
                       gmul(k, gmodulcp(polx[varn(T)],T))), pol);
}
GEN
eltabstorel(GEN x, GEN T, GEN pol, GEN k)
{
  return poleval(x, get_theta_abstorel(T,pol,k));
}
GEN
rnf_get_theta_abstorel(GEN rnf)
{
  GEN k, nf, T, pol, rnfeq;
  rnfeq  = (GEN)rnf[11]; k = (GEN)rnfeq[3];
  nf = (GEN)rnf[10]; T = (GEN)nf[1];
  pol = (GEN)rnf[1];
  return get_theta_abstorel(T, pol, k);
}

GEN
rnfelementabstorel(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long tx, i, lx;
  GEN z;

  checkrnf(rnf); tx = typ(x);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfelementabstorel(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      x = lift_to_pol(x); /* fall through */
    case t_POL:
      return gerepileupto(av, poleval(x, rnf_get_theta_abstorel(rnf)));

    default: return gcopy(x);
  }
}

/* x t_POLMOD or t_POL or vector of such objects */
GEN
rnfelementup(GEN rnf,GEN x)
{
  long i, lx, tx;
  GEN z;

  checkrnf(rnf); tx = typ(x);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long)rnfelementup(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD: x = (GEN)x[2]; /* fall through */
    case t_POL:
      return poleval(x, gmael(rnf,11,2));

    default: return gcopy(x);
  }
}

/* x t_POLMOD or t_POL or vector of such objects */
GEN
rnfelementdown(GEN rnf,GEN x)
{
  pari_sp av;
  long i, lx, tx;
  GEN z;

  checkrnf(rnf); tx = typ(x);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long)rnfelementdown(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD: x = (GEN)x[2]; /* fall through */
    case t_POL:
      if (gcmp0(x)) return gzero;
      av = avma; z = rnfelementabstorel(rnf,x);
      if (typ(z)==t_POLMOD && varn(z[1])==varn(rnf[1])) z = (GEN)z[2];
      if (gvar(z) <= varn(rnf[1]))
      {
        if (lgef(z) > 3)
          err(talker,"element is not in the base field in rnfelementdown");
        z = (GEN)z[2];
      }
      return gerepilecopy(av, z);

    default: return gcopy(x);
  }
}

static GEN
rnfid(long n, long m)
{
  return idmat_intern(n, gscalcol_i(gun,m), zerocol(m));
}

/* x est exprime sur la base relative */
static GEN
rnfprincipaltohermite(GEN rnf,GEN x)
{
  pari_sp av = avma;
  GEN z, bas = (GEN)rnf[7], nf = (GEN)rnf[10];

  x = rnfbasistoalg(rnf,x);
  x = rnfalgtobasis(rnf, gmul(x, gmodulcp((GEN)bas[1], (GEN)rnf[1])));
  z = cgetg(3,t_VEC);
  z[1] = (long)x; settyp(x, t_MAT);
  z[2] = bas[2];
  return gerepileupto(av, nfhermite(nf,z));
}

GEN
rnfidealhermite(GEN rnf, GEN x)
{
  GEN z, nf, bas;

  checkrnf(rnf); nf = (GEN)rnf[10];
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      bas = (GEN)rnf[7]; z = cgetg(3,t_VEC);
      z[1] = (long)rnfid(degpol(rnf[1]), degpol(nf[1]));
      z[2] = lmul(x, (GEN)bas[2]); return z;

    case t_VEC:
      if (lg(x) == 3 && typ(x[1]) == t_MAT) return nfhermite(nf, x);
      return rnfidealabstorel(rnf, x);

    case t_POLMOD: case t_POL: case t_COL:
      return rnfprincipaltohermite(rnf,x);
  }
  err(typeer,"rnfidealhermite");
  return NULL; /* not reached */
}

GEN
prodid(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;
  if (l == 1) return idmat(degpol(nf[1]));
  z = (GEN)I[1];
  for (i=2; i<l; i++) z = idealmul(nf, z, (GEN)I[i]);
  return z;
}

static GEN
prodidnorm(GEN I)
{
  long i, l = lg(I);
  GEN z;
  if (l == 1) return gun;
  z = dethnf((GEN)I[1]);
  for (i=2; i<l; i++) z = gmul(z, dethnf((GEN)I[i]));
  return z;
}

static GEN
makenorms(GEN rnf)
{
  GEN f = (GEN)rnf[4];
  return typ(f) == t_INT? gun: dethnf(f);
}

GEN
rnfidealnormrel(GEN rnf, GEN id)
{
  pari_sp av = avma;
  GEN z, nf = (GEN)rnf[10];

  checkrnf(rnf);
  if (degpol(rnf[1]) == 1) return idmat(degpol(nf[1]));

  z = prodid(nf, (GEN)rnfidealhermite(rnf,id)[2]);
  return gerepileupto(av, idealmul(nf,z, (GEN)rnf[4]));
}

GEN
rnfidealnormabs(GEN rnf, GEN id)
{
  pari_sp av = avma;
  GEN z;

  checkrnf(rnf);
  if (degpol(rnf[1]) == 1) return gun;

  z = prodidnorm( (GEN)rnfidealhermite(rnf,id)[2] );
  return gerepileupto(av, gmul(z, check_and_build_norms(rnf)));
}

GEN
rnfidealreltoabs(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN w;

  x = rnfidealhermite(rnf,x);
  w = (GEN)x[1]; l = lg(w); settyp(w, t_VEC);
  for (i=1; i<l; i++) w[i] = (long)lift( rnfbasistoalg(rnf, (GEN)w[i]) );
  return gerepilecopy(av, modulereltoabs(rnf, x));
}

GEN
rnfidealabstorel(GEN rnf, GEN x)
{
  long N, m, j;
  pari_sp av = avma;
  GEN nf, A, I, z, id, invbas;

  checkrnf(rnf); nf = (GEN)rnf[10]; invbas = (GEN)rnf[8];
  m = degpol(nf[1]);
  N = m * degpol(rnf[1]);
  if (lg(x)-1 != N) err(typeer, "rnfidealabstorel");
  if (typ(x) != t_VEC) err(typeer,"rnfidealabstorel");
  z = cgetg(3,t_VEC);
  A = cgetg(N+1,t_MAT); z[1] = (long)A;
  I = cgetg(N+1,t_VEC); z[2] = (long)I; id = idmat(m);
  for (j=1; j<=N; j++)
  {
    GEN t = lift_intern( rnfelementabstorel(rnf, (GEN)x[j]) );
    A[j] = (long)mulmat_pol(invbas, t);
    I[j] = (long)id;
  }
  return gerepileupto(av, nfhermite(nf,z));
}

GEN
rnfidealdown(GEN rnf,GEN x)
{
  pari_sp av = avma; x = rnfidealhermite(rnf,x);
  return gerepilecopy(av, gmael(x,2,1));
}

/* lift ideal x to the relative extension, returns a Z-basis */
GEN
rnfidealup(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, n;
  GEN nf, bas, bas2, I, z;

  checkrnf(rnf); nf = (GEN)rnf[10];
  n = degpol(rnf[1]);
  bas = (GEN)rnf[7]; bas2 = (GEN)bas[2];

  z = cgetg(3,t_VEC); I = cgetg(n+1,t_VEC);
  z[1] = bas[1];
  z[2] = (long)I;
  for (i=1; i<=n; i++) I[i] = (long)idealmul(nf,x,(GEN)bas2[i]);
  return gerepilecopy(av, modulereltoabs(rnf, z));
}

/* x a relative HNF ---> vector of 2 generators (relative polymods) */
GEN
rnfidealtwoelement(GEN rnf, GEN x)
{
  pari_sp av = avma;
  GEN y, z, nf, NF;

  checkrnf(rnf);
  nf = (GEN)rnf[10];
  NF = check_and_build_nfabs(rnf);
  y = rnfidealreltoabs(rnf,x);
  y = algtobasis(NF, y); settyp(y, t_MAT);
  y = ideal_two_elt(NF, hnf(y));
  z = cgetg(3,t_VEC);
  z[1] = y[1];
  z[2] = (long)rnfelementabstorel(rnf, gmul((GEN)NF[7], (GEN)y[2]));
  return gerepilecopy(av, z);
}

GEN
rnfidealmul(GEN rnf,GEN x,GEN y) /* x et y sous HNF relative uniquement */
{
  pari_sp av = avma;
  GEN z, nf, x1, x2, p1, p2;

  z = rnfidealtwoelement(rnf,y);
  nf = (GEN)rnf[10];
  x = rnfidealhermite(rnf,x);
  x1 = gmodulcp(gmul(gmael(rnf,7,1), matbasistoalg(nf,(GEN)x[1])),(GEN) rnf[1]);
  x2 = (GEN)x[2];
  p1 = gmul((GEN)z[1], (GEN)x[1]);
  p2 = rnfalgtobasis(rnf, gmul((GEN)z[2], x1)); settyp(p2, t_MAT);
  z = cgetg(3,t_VEC);
  z[1] = (long)concatsp(p1, p2);
  z[2] = (long)concatsp(x2, x2);
  return gerepileupto(av, nfhermite(nf,z));
}
