/* $Id: $

Copyright (C) 2009  The PARI group.

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

/************************************************************/
/*     Computation of all the extensions of a given         */
/*               degree of a p-adic field                   */
/* Xavier Roblot                                            */
/************************************************************/

#undef CHECK_EXTENSIONS

/* cf. Math. Comp, vol. 70, No. 236, pp. 1641-1659 for more details.
   Note that n is now e (since the e from the paper is always = 1) and l
   is now f */
/* Structure for a given type of extension */
typedef struct {
  GEN p;
  long e;
  long f;
  long a;
  long b;
  long j;
  long c;
  long v;     /* auxiliary variable */
  long r;     /* pred = p^r */
  GEN pred;   /* p-adic precision for poly. reduction */
  GEN q;      /* q = p^f */
  GEN upl;    /* cyclo. pol. generating K^ur (mod pred) */
  GEN uplr;   /* upl reduced mod p */
  GEN frob;   /* Frobenius acting of the root of upl (mod pred) */
  GEN Omega;  /* vector giving the structure of the set Omega */
  GEN nbpol;  /* number of polynomials to consider = |Omega| */
  GEN nbext;  /* number of extensions */
  GEN roottable; /* table of roots of polynomials over the residue field */
} KRASNER_t;

/* Structure containing the field data (constructed with FieldData) */
typedef struct {
  GEN topx;  /* absolute polynomial (in x) with root zq + pi (mod pred) */
  GEN top;  /* absolute polynomial with root zq + pi (mod pred) */
  GEN topr; /* absolute polynomial with root zq + pi (mod pred) */
  GEN rpl;  /* relative polynomial with root zq + pi (mod pred) (y=zq) */
  GEN eis;  /* relative polynomial with root pi (mod prec) (y=zq) */
  GEN zq;   /* prim. root of unity (root of upl) (mod pred) (y=zq+pi) */
  GEN pi;   /* prime element (mod p) (y=zq+pi)*/
  GEN ipi;  /* p/pi (mod pred) (y=zq+pi) (used to divide by pi) */
  GEN ppi;  /* powers of pi (mod pred) (for GetSharp) */
} FAD_t;

static long
ceildiv(ulong a, ulong b)
{
  long c = a/b;
  if (a%b) c++;
  return c;
}

/* Eval P(x) assuming P has positive coefficients and the result is a long */
static ulong
ZX_z_eval(GEN P, ulong x)
{
  long i, l = lg(P);
  ulong z;

  if (typ(P) == t_INT) return itou(P);
  if (l == 2) return 0;

  z = itou(gel(P, l-1));
  for (i = l-2; i > 1; i--)
    z = z*x+itou(gel(P,i));

  return z;
}

/* Eval P(x, y) assuming P has positive coefficients and the result is a long */
static ulong
ZXY_z_eval(GEN P, ulong x, ulong y)
{
  long i, l = lg(P);
  ulong z;

  if (l == 2) return 0;

  z = ZX_z_eval(gel(P, l-1), y);
  for (i = l-2; i > 1; i--)
    z = z*x+ZX_z_eval(gel(P, i), y);

  return z;
}

static GEN
FqX_FpXQ_eval(GEN P, GEN x, GEN T, GEN p)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);

  Q[1] = P[1];
  for (i = 2; i < l; i++)
  {
    GEN cf = gel(P, i);
    if (typ(cf) == t_POL && degpol(cf) > 0) cf = FpX_FpXQ_eval(cf, x, T, p);
    gel(Q, i) = simplify_shallow(cf);
  }

  return Q;
}

/* Should exist, but doesn't... */
static GEN
FpXQX_translate(GEN P, GEN c, GEN T, GEN p)
{
  pari_sp av = avma, lim;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || gcmp0(c)) return gcopy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  lim = stack_lim(av, 2);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
      R[k] = Fq_add(R[k], Fq_mul(c, R[k+1], T, p), T, p);

    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FpXQX_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
    }
  }
  return gerepilecopy(av, normalizepol(Q));
}

/* Sieving routines */

static GEN
InitSieve(long lg)
{
  return zero_F2v(lg);
}

static long
NextZeroValue(GEN sv, long i)
{
  while ((i <= sv[1]) && F2v_coeff(sv, i)) i++;

  if (i <= sv[1]) return i;

  return 0; /* sieve is full or out of the sieve! */
}

static void
SetSieveValue(GEN sv, long i)
{
  if ((i < 1 ) || (i > sv[1])) return;

  F2v_set(sv, i);
}

/* return 1 if the data verify Ore condition and 0 otherwise */
static long
VerifyOre(GEN p, long e, long j)
{
  long nv, m, b, vb, nb, mn;

  m  = z_pval(e, p);
  nv = m*e;
  b  = j%e;

  if (b == 0)
    return (j == nv);

  if (j > nv) return 0;

  vb = z_pval(b, p);
  nb = vb*e;
  mn = minss(nb, nv);

  return (mn <= j);
}

/* Given [K:Q_p] = m and disc(K/Q_p) = p^d, return all the possible
   decompositions K/K^ur/Q_p as [f, e, j, c] with [K^ur:Q_p] = f and
   K^ur/Q_p unramified, [K:K^ur] = e and K/K^ur totally ramified of
   discriminant p^j (so d = f*j) */
static GEN
PossibleDecomposition(GEN p, long m, long d)
{
  GEN rep, div = divisorsu(ugcd(m, d));
  long i, ctr = 1, l = lg(div);

  rep = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    long f = div[i], e = m/f, j = d/f - e + 1;
    if (VerifyOre(p, e, j)) gel(rep, ctr++) = mkvecsmall3(e, f, j);
  }
  setlg(rep, ctr); return rep;
}

/* return the number of extensions corresponding to the data */
static GEN
NumberExtensions(KRASNER_t *data)
{
  long e, j, a, b;
  GEN p, q, s0, p1;

  e = data->e;
  p = data->p;
  q = data->q;
  j = data->j;

  b = (j%e);
  a = (j-b)/e;

  /* n*q^(n*sum(p^-i, i=1...a)) */
  s0 = gdiv(gsubsg(1, gpowgs(p, -a)), gsubgs(p, 1));
  s0 = gmulsg(e, powgi(q, gmulsg(e, s0)));

  if (b == 0) return s0;

  s0 = gmul(gsubgs(q, 1), s0);

  /* q^floor((b-1)/p^(a+1)) */
  p1 = powgi(q, gfloor(gdivsg(b-1, gpowgs(p, a+1))));

  return gmul(s0, p1);
}

/* eis is an Eisenstein polynomial (as a ZXY) over the field defined
   by upl. Return the struct FAD corresponding to the field it defines.
   If flag is zero, return only the polynomials top and rpl.
   If flag is non-zero, the GENs are created on the heap!
*/
static void
FieldData(KRASNER_t *data, FAD_t *fdata, GEN eis, long flag)
{
  GEN zq2, p1, p2;
  long j;

  /* top poly. is the minimal polynomial of root(pol) + root(upl) */
  fdata->rpl =
    FpXQX_translate(FqX_red(eis, data->upl, data->pred),
		    FpX_rem(gneg(pol_x(data->v)), data->upl, data->pred), data->upl, data->pred);

  p1 = fdata->rpl;
  p2 = fdata->rpl;
  for (j = 1; j < data->f; j++)
  {
    p1 = gsubst(p1, data->v, FpXQ_pow(pol_x(data->v),
				      data->p, data->upl, data->pred));
    p1 = FqX_red(p1, data->upl, data->pred);
    p2 = FqX_mul(p2, p1, data->upl, data->pred);
  }
  /* make the coefficients INTs */
  p2 = simplify_shallow(p2);

  fdata->topx = p2;
  fdata->top  = gsubst(p2, 0, pol_x(data->v));
  fdata->topr = FpX_red(fdata->top, data->pred);

  if (!flag) return ;

  fdata->rpl  = gclone(fdata->rpl);
  fdata->topx = gclone(fdata->topx);
  fdata->top  = gclone(fdata->top);
  fdata->topr = gclone(fdata->topr);

  if (data->e == 1)
    pari_err(talker, "unramified polynomial in FieldData");

  fdata->zq  = pol_x(data->v);
  zq2 = gen_0;
  /* FIXME: do as in CycloPol (not so easy) */
  while(!gequal(fdata->zq, zq2))
  {
    zq2 = fdata->zq;
    fdata->zq = Fq_pow(fdata->zq, data->q, fdata->top, data->pred);
  }
  fdata->zq   = gclone(fdata->zq);


  fdata->eis  = gclone(eis);

  fdata->pi   = gclone(Fq_sub(pol_x(data->v), fdata->zq,
			      FpX_red(fdata->top, data->p), data->p));

  fdata->ipi  = RgXQ_inv(fdata->pi, fdata->top);
  fdata->ipi  = RgX_Rg_mul(fdata->ipi, data->p);
  fdata->ipi  = gclone(RgX_to_FpX(fdata->ipi, mulii(data->pred, data->p)));

  /* Last one is in fact pi^e/p */
  p1 = FpXQ_powers(fdata->pi, data->e, fdata->topr, data->pred);
  gel(p1, data->e+1) = ZX_Z_divexact(gel(p1, data->e+1), data->p);
  fdata->ppi  = gclone(p1);
}

static void
FreeFieldData(FAD_t *fdata)
{
  gunclone(fdata->rpl);
  gunclone(fdata->topx);
  gunclone(fdata->top);
  gunclone(fdata->topr);
  gunclone(fdata->zq);
  gunclone(fdata->eis);
  gunclone(fdata->pi);
  gunclone(fdata->ipi);
  gunclone(fdata->ppi);
}

/* return pol*ipi/p (mod top, pp) if it has integral coefficient, NULL
   otherwise. The result is reduced mod top, pp */
static GEN
DivideByPi(KRASNER_t *data, FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  GEN p1, p2, p3, p4;
  long i, l;
  pari_sp av = avma;

  if (gcmp0(pol)) return pol;

  p1 = Fq_mul(pol, fdata->ipi, fdata->top, ppp);
  l  = lg(p1);

  for (i = 2; i < l; i++)
  {
    p2 = gel(p1, i);
    p3 = dvmdii(p2, data->p, &p4);
    if (p4 != gen_0) { avma = av; return NULL; }
    gel(p1, i) = p3;
  }

  return FqX_red(p1, fdata->topr, pp);
}

#ifdef CHECK_EXTENSIONS
static void
PrintValuations(GEN pol, GEN mod, GEN p)
{
  long i, d = degpol(pol);
  for (i = 0; i <= d; i++)
    fprintferr("%d ", Z_pval(RgXQ_norm(gel(pol, i+2), mod), p));
}
#endif

/* return pol# = pol~/pi^vpi(pol~) mod pp where pol~(x) = pol(pi.x +
   beta) has coefficients in the field defined by top, e is the
   ramification index, f is the inertia degree and pi a prime element */
static GEN
GetSharp(KRASNER_t *data, FAD_t *fdata, GEN pp, GEN ppp, GEN pol, GEN beta, long *pl)
{
  GEN p1, p2, p3;
  long d, i, v, l;
  pari_sp av = avma;

  d   = poldegree(pol, 0);

  if (!gcmp0(beta))
    p1 = FpXQX_translate(pol, beta, fdata->topr, pp);
  else
    p1 = gcopy(pol);

  v  = 0;
  p3 = p1;
  p2 = gen_1; /* needs to make sure it is not NULL! */

  while (1)
  {
    for (i = 0; i <= v; i++)
    {
      p2 = gel(p3, i+2);
      p2 = DivideByPi(data, fdata, pp, ppp, p2);
      if (!p2) break;
      gel(p3, i+2) = p2;
    }
    if (!p2) break;
    p1 = shallowcopy(p3);
    v++;
  }

  if (!v) pari_err(talker, "No division in GetSharp");

  for (l = v; l >= 0; l--)
  {
    p2 = gel(p1, l+2);
    p2 = DivideByPi(data, fdata, pp, ppp, p2);
    if (!p2) { break; }
  }

  *pl = l;
  if (l < 2) return NULL;

  /* adjust powers */
  for (i = v+1; i <= d; i++)
    gel(p1, i+2) = Fq_mul(gel(p1, i+2),
			  gel(fdata->ppi, i-v+1), fdata->topr, pp);

  return gerepilecopy(av, normalizepol(p1));
}

#ifdef CHECK_EXTENSIONS
/* Return the degree of pol mod the prime ideal of top */
static long
DegreeMod(KRASNER_t *data, FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  long d = degpol(pol); /* d should be > 0 */
  pari_sp av = avma;

  do
  {
    GEN p1 = gel(pol, d+2);
    if(!gcmp0(p1) && !DivideByPi(data, fdata, data->p, mulii(data->p, data->p), p1))
      { avma = av; return d; }
    avma = av; d--;
  }
  while (d >= 1);

  return 0;
}
#endif

/* Compute the roots of pol in the residue field, using table look-up if possible */
static GEN
Quick_FqX_roots(KRASNER_t *data, GEN pol)
{
  GEN rts;
  ulong ind = 0;

  pol = FpXQX_red(pol, data->uplr, data->p);

  if (data->roottable)
  {
    ind = ZXY_z_eval(pol, itou(data->q), itou(data->p));
    if (gel(data->roottable, ind)) return gel(data->roottable, ind);
  }

  rts = FqX_roots(pol, data->uplr, data->p);

  if (ind) gel(data->roottable, ind) = gclone(rts);
  return rts;
}

static void
FreeRootTable(KRASNER_t *data)
{
  if (data->roottable)
  {
    long j, l = lg(data->roottable);
    for (j = 1; j < l; j++)
      if (gel(data->roottable, j)) gunclone(gel(data->roottable, j));
  }
}

/* Return the number of roots of pol congruent to alpha modulo pi working
   modulo pp (all roots if alpha is NULL); if flag is non-zero, return 1
   as soon as a root is found. (Note: ppp = pp*p for DivideByPi) */
static long
RootCongruents(KRASNER_t *data, FAD_t *fdata, GEN pol, GEN alpha, GEN pp, GEN ppp, long sl, long flag)
{
  GEN R;
  long s, i, l = 0;

  if (alpha)
  {
    /* FIXME: the data used in GetSharp is not reduced */
    pol = GetSharp(data, fdata, pp, ppp, pol, alpha, &l);
    if (l <= 1) return l;
#ifdef CHECK_EXTENSIONS
    if (l > 1 && l != DegreeMod(data, fdata, pp, ppp, pol)) pari_err(talker, "Degrees do not match in RCA");
    if (l == -1) pari_err(talker, "Degree is wrong in RCA!\n");
#endif
  }

  R  = Quick_FqX_roots(data, pol);

  s = 0;

  /* decrease precision if sl gets bigger than a multiple of e */
  if ((sl+l)/data->e > sl/data->e)
  {
    pp = diviiexact(pp, data->p);
    ppp = diviiexact(ppp, data->p);
  }
  sl += l;

  for (i = 1; i < lg(R); i++)
  {
    s += RootCongruents(data, fdata, pol, gel(R, i), pp, ppp, sl, flag);
    if (flag && s) return 1;
  }

  return s;
}

/* pol is a ZXY defining a polynomial over the field defined by fdata
   (as returned by FieldData). If flag != 0, return 1 as soon as a
   root is found. Precision are done with a precision of pred. */
static long
RootCountingAlgorithm(KRASNER_t *data, FAD_t *fdata, GEN pol, long flag)
{
  long j, l, d;
  GEN p1 = cgetg_copy(pol, &l);

  p1[1] = pol[1];
  d = l-3;
  for (j = 0; j < d; j++)
  {
    GEN cf = gel(pol, j+2);
    if (typ(cf) == t_INT)
      cf = diviiexact(cf, data->p);
    else
      cf = ZX_Z_divexact(cf, data->p);
    gel(p1, j+2) = Fq_mul(cf, gel(fdata->ppi, j+1), fdata->topr, data->pred);
  }
  gel(p1, d+2) = gel(fdata->ppi, d+1); /* ppi[d] = pi^d/p */

  return RootCongruents(data, fdata, p1, NULL, diviiexact(data->pred, data->p), data->pred, 0, flag);
}

/* Return non-zero if the field given by fdata (cf. FieldData) defines
   a field isomorphic to the one defined by pol. If flag is non-zero,
   use some probabilistic argument, so might answer yes even if the fields
   are not (but not the other way around) */
static long
IsIsomorphic(KRASNER_t *data, FAD_t *fdata, GEN pol)
{
  GEN p1;
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) return RootCountingAlgorithm(data, fdata, pol, 1);

  for (j = 1; j <= data->f; j++)
  {
    p1 = FqX_FpXQ_eval(pol, fdata->zq, fdata->top, data->pred);
    nb = RootCountingAlgorithm(data, fdata, p1, 1);

    if (nb) { return nb; }

    if (j < data->f)
    {
      pol = gsubst(pol, data->v, data->frob);
      pol = gerepileupto(av, FqX_red(pol, data->upl, data->pred));
    }
  }

  avma = av;

  return 0;
}

/* Return the number of conjugates fields of the field given by fdata
   (cf. FieldData) */
static long
NbConjugateFields(KRASNER_t *data, FAD_t *fdata)
{
  GEN pol;
  long j, nb = 0;
  pari_sp av = avma;

  pol = fdata->eis;

  if (RgX_is_ZX(pol)) nb = (data->f)*RootCountingAlgorithm(data, fdata, pol, 0);
  else
  {
    for (j = 1; j <= data->f; j++)
    {
      GEN p1 = FqX_FpXQ_eval(pol, fdata->zq, fdata->top, data->pred);
      nb += RootCountingAlgorithm(data, fdata, p1, 0);

      if (j < data->f)
      {
	pol = gsubst(pol, data->v, data->frob);
	pol = FqX_red(pol, data->upl, data->pred);
      }
    }
  }

  avma = av;
  return (data->e)*(data->f)/nb;
}

/* return a minimal list of polynomials generating all the totally
   ramified extensions of K^ur of degree e and discriminant
   p^{e + j - 1} in the tamely ramified case */
static GEN
TamelyRamifiedCase(KRASNER_t *data)
{
  long av = avma, g, r, gr, ct;
  GEN qm, p1, p2, rep, sv;
  FAD_t fdata;

#ifdef CHECK_EXTENSIONS
  long nbext, cnt = 0, nb, j;
  GEN vpl;
  nbext = itos(data->nbext);
  fprintferr("Number of extensions: %ld\n", nbext);
#endif

  qm  = gsubgs(data->q, 1);

  g   = itos(ggcd(stoi(data->e), qm));
  rep = zerovec(g);

  p1 = gadd(gpowgs(pol_x(0), data->e), data->p);
#ifdef CHECK_EXTENSIONS
  vpl = zerovec(g);
  FieldData(data, &fdata, p1, 1);
  nb = NbConjugateFields(data, &fdata);
  fprintferr("Found %ld field(s)\n", nb);
  cnt += nb;
  gel(rep, 1) = gcopy(fdata.topx);
  gel(vpl, 1) = p1;
  FreeFieldData(&fdata);
#else
  FieldData(data, &fdata, p1, 0);
  gel(rep, 1) = fdata.topx;
#endif

  r = 1; ct = 1;

  if (g > 1)
  {
    sv = InitSieve(g-1);
    while (r)
    {
      p1 = FpXQ_pow(pol_x(data->v), stoi(r), data->uplr, data->p);
      ct++;
      p2 = gadd(gpowgs(pol_x(0), data->e), gmul(p1, data->p));
#ifdef CHECK_EXTENSIONS
      FieldData(data, &fdata, p2, 1);
      for (j = 1; j < ct; j++)
      {
	nb = IsIsomorphic(data, &fdata, gel(vpl, j));
	if (nb)
	  pari_err(talker,
		   "Oops, fields are isomorphic in TamelyRamifiedCase!\n");
      }
      nb = NbConjugateFields(data, &fdata);
      fprintferr("Found %ld field(s)\n", nb);
      cnt += nb;
      gel(rep, ct) = gcopy(fdata.topx);
      gel(vpl, ct) = gcopy(fdata.eis);
      FreeFieldData(&fdata);
#else
      FieldData(data, &fdata, p2, 0);
      gel(rep, ct) = fdata.topx;
#endif
      gr = r;
      do
      {
	SetSieveValue(sv, gr);
	gr = smodis(mulsi(gr, data->p), g);
      }
      while (gr != r);
      r  = NextZeroValue(sv, r);
    }
  }

#ifdef CHECK_EXTENSIONS
  if (nbext == cnt)
    fprintferr("Hurray! I found exactly the right number of fields!\n");
  else
    pari_err(talker,"Number of fields incorrect in TamelyRamifiedCase\n");
#endif
  setlg(rep, ct+1);

  return gerepilecopy(av, rep);
}

static long
function_l(GEN p, long a, long b, long i)
{
  long l = 1 + a - z_pval(i, p);
  if (i < b) l++;
  return (l < 1)? 1: l;
}

/* Structure of the coefficients set Omega
   Each coefficient is a smallvec [v_start, v_end, zero, nbcf] meaning
   all the numbers of the form:
   zeta_0 * p^v_start + ... + zeta_s * p^v_end (s = v_end - v_start)
   with zeta_i roots of unity (powers of zq + zero), zeta_0 = 0 is
   possible iff zero = 1, and nbcf the number of such coefficients
*/
static void
InitStructureOmega(KRASNER_t *data)
{
  long i, l;
  GEN cf, p1, nbpol, rep;

  rep = zerovec(data->e);
  nbpol = gen_1;

  for (i = 0; i < data->e; i++)
  {
    cf = const_vecsmall(4, 0);
    cf[2] = data->c;
    if (i == 0)
    {
      cf[1] = 1;
      cf[4] = itos(mulii(gsubgs(data->q, 1), gpowgs(data->q, (data->c)-1)));
    }
    else
    {
      l = function_l(data->p, data->a, data->b, i);
      cf[1] = l;
      p1 = gpowgs(data->q, (data->c)-l);
      if (i == data->b)
	p1 = mulii(p1, gsubgs(data->q, 1));
      else
      {
	p1 = mulii(p1, data->q);
	cf[3] = 1;
      }
      cf[4] = itos(p1);
    }
    gel(rep, i+1) = cf;
    nbpol = mulis(nbpol, cf[4]);
  }

  data->Omega = rep;
  data->nbpol = nbpol;
}

/* Return an element of the finite field; possible zero if zr != 0 */
static GEN
RandomFF(KRASNER_t *data, long zr)
{
  long i, f = data->f, p = itou(data->p);
  GEN c = zerovec(f);

  for (i = 0; i < f; i++) gel(c, i+1) = utoi(random_Fl(p));

  if (!zr && gcmp0(c)) return RandomFF(data, zr);

  return gtopoly(c, data->v);
}

static GEN
RandomPol(KRASNER_t *data)
{
  long i, j;
  GEN pol, Omg = data->Omega;

  pol = zerovec((data->e)+1);
  gel(pol, (data->e)+1) = gen_1;
  for (i = 0; i < data->e; i++)
  {
    long st = mael(Omg, i+1, 1), ed = mael(Omg, i+1, 2), zr = mael(Omg, i+1, 3);
    GEN pp = data->p, cf = RandomFF(data, zr);
    for (j = 1; j <= ed-st; j++)
    {
      cf = gadd(cf, ZX_Z_mul(RandomFF(data, 1), pp));
      pp = mulii(data->p, pp);
    }
    gel(pol, i+1) = ZX_Z_mul(cf, powis(data->p, st));
  }

  return gtopolyrev(pol, 0);
}

static GEN
WildlyRamifiedCase(KRASNER_t *data)
{
  long nbext, ct, fd, nb = 0, j;
  GEN nbpol, rpl, rep;
  FAD_t **vfd;
  pari_timer T;
  pari_sp av = avma, av2;

  InitStructureOmega(data);

  nbpol = data->nbpol;
  nbext = itos(data->nbext);

  if (DEBUGLEVEL>0) {
    fprintferr("There are %ld extensions to find and %Ps polynomials to consider\n", nbext, nbpol);
    TIMERstart(&T);
  }

  vfd = (FAD_t**)new_chunk(nbext);
  for (j = 0; j < nbext; j++) vfd[j] = (FAD_t*)new_chunk(sizeof(FAD_t));

  ct = 0;
  fd = 0;

  av2 = avma;

  while (fd < nbext)
  {
    /* The best thing seems to be to jump randomly among the polynomials... */
    rpl = RandomPol(data);

    if (DEBUGLEVEL>3)
      fprintferr("considering polynomial %Ps\n", rpl);

#ifdef CHECK_EXTENSIONS
    {
      GEN disc = poldisc0(rpl, 0);
      long e = data->e, f = data->f, j = data->j;
      disc = RgXQ_norm(disc, data->upl);
      if (Z_pval(disc, data->p) != f*(e+j-1))
	pari_err(talker, "incorrect discriminant in WildlyRamifiedCase\n");
    }
#endif

    for (j = 0; j < ct; j++)
    {
      nb = IsIsomorphic(data, vfd[j], rpl);
      if (nb) break;
    }
    if (!nb)
    {
      FieldData(data, (FAD_t*)vfd[ct], rpl, 1);
      nb = NbConjugateFields(data, (FAD_t*)vfd[ct]);
      fd += nb;
      ct++;
      if (DEBUGLEVEL>1)
	msgTIMER(&T, "new pol., generating %ld extension%s (total: %ld/%ld)",
                 nb, (nb == 1)? "": "s", fd, nbext);
    }
    avma = av2;
  }

  rep = cgetg(ct+1, t_VEC);
  for (j = 0; j < ct; j++)
  {
    gel(rep, j+1) = gcopy(((FAD_t*)vfd[j])->topx);
    FreeFieldData((FAD_t*)vfd[j]);
  }

  FreeRootTable(data);

  return gerepileupto(av, rep);
}

/* return a cyclotomic polynomial (mod pred) of degree f and variable v */
static GEN
CycloPol(KRASNER_t *data)
{
  GEN p1, p2, p3;

  p1 = ffinit(data->p, data->f, data->v);
  p2 = FF_to_FpXQ(ffprimroot(ffgen(p1, data->v), NULL));
  p1 = lift(p1);

  p3 = ZpXQ_sqrtnlift(gen_1, gsubgs(data->q, 1), p2, p1, data->p, data->r);

  return RgX_to_FpX(ZXQ_charpoly(p3, p1, data->v), data->pred);
}

/* Compute an absolute polynomial for all the totally ramified
   extensions of Q_p(z) of degree e and discriminant p^{e + j - 1}
   where z is a root of upl defining an unramified extension of Q_p */
/* See padicfields for the meaning of flag */
static GEN
GetRamifiedPol(GEN p, GEN efj, long v, long flag)
{
  long r, e = efj[1], f = efj[2], j = efj[3];
  GEN pols;
  KRASNER_t data;
  pari_sp av = avma;

  if (DEBUGLEVEL>1)
    fprintferr("  Computing extensions with decomposition [e, f, j] = [%ld, %ld, %ld]\n", e,f,j);
  data.p   = p;
  data.e   = e;
  data.f   = f;
  data.j   = j;
  data.a   = j/e;
  data.b   = j%e;
  data.c   = (e+2*j)/e+1;
  data.q   = powis(p, f);
  data.v   = v;
  /* This should be enough precision */
  r = 1+2*data.a+ceildiv(2*data.b+3, e);
  data.r     = r;
  data.pred  = powiu(p, r);
  data.nbext = NumberExtensions(&data);

  if (flag == 2) return data.nbext;

  data.upl   = CycloPol(&data);
  data.uplr  = FpX_red(data.upl, data.p);
  data.frob  = FpXQ_pow(pol_x(v), p, data.upl, data.pred);
  if (DEBUGLEVEL>1) fprintferr("  Unramified part %Ps\n", data.upl);
  data.roottable = NULL;

  if (e == 1) pols = mkvec(gsubst(data.upl, v, pol_x(0)));

  if (dvdsi(e, p))
  {
    GEN npol = mulii(powis(data.q, data.e), data.q);
    if (cmpiu(npol, 2<<18) < 0 && lgefint(data.p) <= 3)
    {
      long i, l = itou(npol);
      data.roottable = cgetg(l+1, t_POL);
      for (i = 1; i <= l; i++) gel(data.roottable, i) = NULL;
    }
    pols = WildlyRamifiedCase(&data);
  }
  else
    pols = TamelyRamifiedCase(&data);

  if (flag == 1)
  {
    long i, l;
    GEN p1 = cgetg_copy(pols, &l);
    for (i = 1; i < l; i++)
      gel(p1, i) = mkvec4(gcopy(gel(pols, i)), stoi(data.e), stoi(data.f), stoi(data.f*(data.e+data.j-1)));
    pols = gerepileupto(av, p1);
  }
  else
    pols = gerepilecopy(av, pols);

  return pols;
}

/* return a minimal list of polynomials generating all the extensions of
   Q_p of given degree N; if N is a t_VEC [n,d], return extensions of degree n
   and discriminant p^d. */
/* Return only the polynomials if flag = 0 (default), also the ramification
   degree, the residual degree and the discriminant if flag = 1 and only the
   number of extensions if flag = 2 */
GEN
padicfields0(GEN p, GEN N, long flag)
{
  long m, d = -1, av = avma;

  if (typ(p) != t_INT) pari_err(arither1);
  switch(typ(N))
  {
    case t_VEC:
      if (lg(N) != 3) pari_err(typeer, "padicfields");
      if (typ(gel(N,2)) != t_INT) pari_err(typeer,"padicfields");
      d = itos(gel(N,2));
      N = gel(N,1); /* fall through */
    case t_INT:
      m = itos(N);
      if (m <= 0) pari_err(talker,"non-positive degree in padicfields()");
      break;
  }

  if (d < 0)
  { /* maximal possible discriminant valuation: m*(1+log(m)/log(p)) */
    long ds = m * logint(stoi(m), p, NULL);
    GEN L = cgetg(ds + 2, t_VEC);
    for (d = 0; d <= ds; d++) gel(L, d+1) = padicfields(p, m, d, flag);
    if (flag == 2)
      return gerepileuptoint(av, ZV_sum(L));
    return gerepilecopy(av, shallowconcat1(L));
  }
  return padicfields(p, m, d, flag);
}

GEN
padicfields(GEN p, long m, long d, long flag)
{
  long j, l, av = avma, v = fetch_user_var("y");
  GEN L;

  L = PossibleDecomposition(p, m, d);
  l = lg(L);
  if( DEBUGLEVEL>0)
  {
    fprintferr("Extension(s) of degree %ld and discriminant %Ps^%ld of Q_%Ps\n",
               m, p, d, p);
    if (DEBUGLEVEL>1)
      fprintferr("Possible decomposition(s) [e, f, j] = %Ps\n", L);
  }
  for (j = 1; j < l; j++) gel(L,j) = GetRamifiedPol(p, gel(L,j), v, flag);
  if (flag == 2)
    return gerepileuptoint(av, ZV_sum(L));
  if (l == 1) { avma = av; return cgetg(1, t_VEC); }
  return gerepilecopy(av, shallowconcat1(L));
}
