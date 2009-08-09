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
  long e, f, j;
  long a, b, c;
  long v;     /* auxiliary variable */
  long r;     /* pred = p^r */
  GEN pred;   /* p-adic precision for poly. reduction */
  GEN q, qm1; /* p^f, q - 1 */
  GEN upl;    /* cyclo. pol. generating K^ur (mod pred) */
  GEN uplr;   /* upl reduced mod p */
  GEN frob;   /* Frobenius acting of the root of upl (mod pred) */
  GEN nbext;  /* number of extensions */
  GEN roottable; /* table of roots of polynomials over the residue field */
} KRASNER_t;

/* Structure containing the field data (constructed with FieldData) */
typedef struct {
  GEN p;
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
  for (i = l-2; i > 1; i--) z = z*x + itou(gel(P,i));
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
  for (i = l-2; i > 1; i--) z = z*x + ZX_z_eval(gel(P, i), y);
  return z;
}

/* P an Fq[X], where Fq = Fp[Y]/(T(Y)), a an FpX representing the automorphism
 * y -> a(y). Return a(P), applying a() coefficientwise. */
static GEN
FqX_FpXQ_eval(GEN P, GEN a, GEN T, GEN p)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);

  Q[1] = P[1];
  for (i = 2; i < l; i++)
  {
    GEN cf = gel(P, i);
    if (typ(cf) == t_POL) {
      switch(degpol(cf))
      {
        case -1: cf = gen_0; break;
        case 0:  cf = gel(cf,2); break;
        default:
          cf = FpX_FpXQ_eval(cf, a, T, p);
          cf = simplify_shallow(cf);
          break;
      }
    }
    gel(Q, i) = cf;
  }

  return Q;
}

/* Sieving routines */
static GEN
InitSieve(long l) { return zero_F2v(l); }
static long
NextZeroValue(GEN sv, long i)
{
  for(; i <= sv[1]; i++)
    if (!F2v_coeff(sv, i)) return i;
  return 0; /* sieve is full or out of the sieve! */
}
static void
SetSieveValue(GEN sv, long i)
{ if (i >= 1 && i <= sv[1]) F2v_set(sv, i); }

/* return 1 if the data verify Ore condition and 0 otherwise */
static long
VerifyOre(GEN p, long e, long j)
{
  long nv, m, b, vb, nb;

  m  = z_pval(e, p);
  nv = m*e;
  b  = j%e;
  if (b == 0) return (j == nv);
  if (j > nv) return 0;

  vb = z_pval(b, p);
  nb = vb*e;
  return (minss(nb, nv) <= j);
}

/* Given [K:Q_p] = m and disc(K/Q_p) = p^d, return all the possible
   decompositions K/K^ur/Q_p as [e, f, j] with [K^ur:Q_p] = f and
   K^ur/Q_p unramified, [K:K^ur] = e and K/K^ur totally ramified of
   discriminant p^j (thus d = f*j) */
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

/* return the number of extensions corresponding to (e,f,j) */
static GEN
NumberExtensions(KRASNER_t *data)
{
  ulong pp, pa;
  long e, j, a, b;
  GEN p, q, s0, p1;

  e = data->e;
  p = data->p;
  q = data->q;
  j = data->j;
  a = data->a; /* floor(j/e) <= v_p(e), hence p^a | e */
  b = data->b; /* j % e */
  if (is_bigint(p)) /* implies a = 0 */
    return b == 0? utoipos(e): mulsi(e, data->qm1);

  pp = p[2];
  switch(a)
  {
    case 0:  pa = 1;  s0 = utoipos(e); break;
    case 1:  pa = pp; s0 = mulsi(e, powis(q, e / pa)); break;
    default:
      pa = upowuu(pp, a); /* p^a */
      s0 = mulsi(e, powis(q, (e / pa) * ((pa - 1) / (pp - 1))));
  }
  /* s0 = e * q^(e*sum(p^-i, i=1...a)) */
  if (b == 0) return s0;

  /* q^floor((b-1)/p^(a+1)) */
  p1 = powis(q, sdivsi(b-1, muluu(pa, pp)));
  return mulii(mulii(data->qm1, s0), p1);
}

/* eis is an Eisenstein polynomial (as a ZXY) over the field defined
 * by upl. Return the struct FAD corresponding to the field it defines.
 * If flag is zero, return only the polynomials top and rpl.
 * If flag is non-zero, assume e > 1; the GENs are created on the heap */
static void
FieldData(KRASNER_t *data, FAD_t *fdata, GEN eis, long flag)
{
  GEN p1, p2;
  long j;

  fdata->p = data->p;

  /* top poly. is the minimal polynomial of root(pol) + root(upl) */
  fdata->rpl =
    FqX_translate(FqX_red(eis, data->upl, data->pred),
		  FpX_rem(gneg(pol_x(data->v)), data->upl, data->pred), data->upl, data->pred);

  p1 = fdata->rpl;
  p2 = fdata->rpl;
  for (j = 1; j < data->f; j++)
  {
    p1 = FqX_FpXQ_eval(p1, data->frob, data->upl, data->pred);
    p2 = FqX_mul(p2, p1, data->upl, data->pred);
  }
  p2 = simplify_shallow(p2); /* ZX */

  fdata->topx = p2;
  fdata->top  = gsubst(p2, 0, pol_x(data->v));
  fdata->topr = FpX_red(fdata->top, data->pred);

  if (!flag) return;

  /* From now on, assume data->e > 1 */
  fdata->rpl  = gclone(fdata->rpl);
  fdata->topx = gclone(fdata->topx);
  fdata->top  = gclone(fdata->top);
  fdata->topr = gclone(fdata->topr);

  fdata->zq  = pol_x(data->v);
  /* FIXME: do as in CycloPol (not so easy) */
  for(;;)
  {
    GEN zq2 = fdata->zq;
    fdata->zq = Fq_pow(fdata->zq, data->q, fdata->top, data->pred);
    if (gequal(fdata->zq, zq2)) break;
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
DivideByPi(FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  GEN P;
  long i, l;
  pari_sp av = avma;

  /* "pol" is a t_INT or an FpX: signe() works for both */
  if (!signe(pol)) return pol;

  P = Fq_mul(pol, fdata->ipi, fdata->top, ppp); /* FpX */
  l  = lg(P);
  for (i = 2; i < l; i++)
  {
    GEN r;
    gel(P,i) = dvmdii(gel(P,i), fdata->p, &r);
    if (r != gen_0) { avma = av; return NULL; }
  }
  return FpX_red(P, pp);
}

/* return pol# = pol~/pi^vpi(pol~) mod pp where pol~(x) = pol(pi.x + beta)
 * has coefficients in the field defined by top and pi is a prime element */
static GEN
GetSharp(FAD_t *fdata, GEN pp, GEN ppp, GEN pol, GEN beta, long *pl)
{
  GEN p1, p2;
  long i, v, l, d = degpol(pol);
  pari_sp av = avma;

  if (!gequal0(beta))
    p1 = FqX_translate(pol, beta, fdata->topr, pp);
  else
    p1 = shallowcopy(pol);
  p2 = p1;
  for (v = 0;; v++)
  {
    for (i = 0; i <= v; i++)
    {
      GEN c = gel(p2, i+2);
      c = DivideByPi(fdata, pp, ppp, c);
      if (!c) break;
      gel(p2, i+2) = c;
    }
    if (i <= v) break;
    p1 = shallowcopy(p2);
  }
  if (!v) pari_err(talker, "No division in GetSharp");

  for (l = v; l >= 0; l--)
  {
    GEN c = gel(p1, l+2);
    c = DivideByPi(fdata, pp, ppp, c);
    if (!c) { break; }
  }

  *pl = l; if (l < 2) return NULL;

  /* adjust powers */
  for (i = v+1; i <= d; i++)
    gel(p1, i+2) = Fq_mul(gel(p1, i+2),
			  gel(fdata->ppi, i-v+1), fdata->topr, pp);

  return gerepilecopy(av, normalizepol(p1));
}

#ifdef CHECK_EXTENSIONS
static void
PrintValuations(GEN pol, GEN mod, GEN p)
{
  long i, d = degpol(pol);
  for (i = 0; i <= d; i++)
    fprintferr("%d ", Z_pval(RgXQ_norm(gel(pol, i+2), mod), p));
}

/* Return the degree of pol mod the prime ideal of top */
static long
DegreeMod(FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  long d = degpol(pol); /* should be > 0 */
  pari_sp av = avma;
  GEN pp = sqri(fdata->p);

  do
  {
    GEN c = gel(pol, d+2);
    if (!gequal0(c) && !DivideByPi(fdata, fdata->p, pp, c))
      return d;
  }
  while (--d >= 1);
  avma = av; return 0;
}
#endif

/* Compute roots of pol in the residue field. Use table look-up if possible */
static GEN
Quick_FqX_roots(KRASNER_t *data, GEN pol)
{
  GEN rts;
  ulong ind = 0;

  pol = FpXQX_red(pol, data->uplr, data->p);

  if (data->roottable)
  {
    ind = ZXY_z_eval(pol, data->q[2], data->p[2]);
    if (gel(data->roottable, ind)) return gel(data->roottable, ind);
  }
  rts = FqX_roots(pol, data->uplr, data->p);

  if (ind) gel(data->roottable, ind) = gclone(rts);
  return rts;
}

static void
FreeRootTable(GEN T)
{
  if (T)
  {
    long j, l = lg(T);
    for (j = 1; j < l; j++)
      if (gel(T,j)) gunclone(gel(T,j));
  }
}

/* Return the number of roots of pol congruent to alpha modulo pi working
   modulo pp (all roots if alpha is NULL); if flag is non-zero, return 1
   as soon as a root is found. (Note: ppp = pp*p for DivideByPi) */
static long
RootCongruents(KRASNER_t *data, FAD_t *fdata, GEN pol, GEN alpha, GEN pp, GEN ppp, long sl, long flag)
{
  GEN R;
  long s, i;

  if (alpha)
  { /* FIXME: the data used in GetSharp is not reduced */
    long l;
    pol = GetSharp(fdata, pp, ppp, pol, alpha, &l);
    if (l <= 1) return l;
#ifdef CHECK_EXTENSIONS
    if (l != DegreeMod(fdata, pp, ppp, pol))
      pari_err(talker, "Degrees do not match in RCA");
#endif
    /* decrease precision if sl gets bigger than a multiple of e */
    sl += l;
    if (sl >= data->e)
    {
      sl -= data->e;
      pp = diviiexact(pp, data->p);
      ppp = mulii(pp, data->p); /* update */
    }
  }

  R  = Quick_FqX_roots(data, pol);
  for (s = 0, i = 1; i < lg(R); i++)
  {
    s += RootCongruents(data, fdata, pol, gel(R, i), pp, ppp, sl, flag);
    if (flag && s) return 1;
  }
  return s;
}

/* pol is a ZXY defining a polynomial over the field defined by fdata
   If flag != 0, return 1 as soon as a root is found. Precision are done with
   a precision of pred. */
static long
RootCountingAlgorithm(KRASNER_t *data, FAD_t *fdata, GEN pol, long flag)
{
  long j, l, d;
  GEN P = cgetg_copy(pol, &l);

  P[1] = pol[1];
  d = l-3;
  for (j = 0; j < d; j++)
  {
    GEN cf = gel(pol, j+2);
    if (typ(cf) == t_INT)
      cf = diviiexact(cf, data->p);
    else
      cf = ZX_Z_divexact(cf, data->p);
    gel(P, j+2) = Fq_mul(cf, gel(fdata->ppi, j+1), fdata->topr, data->pred);
  }
  gel(P, d+2) = gel(fdata->ppi, d+1); /* ppi[d] = pi^d/p */

  return RootCongruents(data, fdata, P, NULL, diviiexact(data->pred, data->p), data->pred, 0, flag);
}

/* Return non-zero if the field given by fdata defines a field isomorphic to
 * the one defined by pol. If flag is non-zero, use some probabilistic
 * argument, so might answer yes even if the fields are not (but not the
 * other way around) */
static long
IsIsomorphic(KRASNER_t *data, FAD_t *fdata, GEN pol)
{
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) return RootCountingAlgorithm(data, fdata, pol, 1);

  for (j = 1; j <= data->f; j++)
  {
    GEN p1 = FqX_FpXQ_eval(pol, fdata->zq, fdata->top, data->pred);
    nb = RootCountingAlgorithm(data, fdata, p1, 1);
    if (nb) { avma = av; return nb; }
    if (j < data->f)
      pol = FqX_FpXQ_eval(pol, data->frob, data->upl, data->pred);
  }
  avma = av; return 0;
}

/* Return the number of conjugates fields of the field given by fdata */
static long
NbConjugateFields(KRASNER_t *data, FAD_t *fdata)
{
  GEN pol = fdata->eis;
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) { /* split for efficiency; contains the case f = 1 */
    nb = data->e / RootCountingAlgorithm(data, fdata, pol, 0);
    avma = av; return nb;
  }

  nb = 0;
  for (j = 1; j <= data->f; j++)
  {
    GEN p1 = FqX_FpXQ_eval(pol, fdata->zq, fdata->top, data->pred);
    nb += RootCountingAlgorithm(data, fdata, p1, 0);
    if (j < data->f)
      pol = FqX_FpXQ_eval(pol, data->frob, data->upl, data->pred);
  }
  avma = av;
  return data->e * data->f / nb;
}

/* return a minimal list of polynomials generating all the totally
   ramified extensions of K^ur of degree e and discriminant
   p^{e + j - 1} in the tamely ramified case */
static GEN
TamelyRamifiedCase(KRASNER_t *data)
{
  long av = avma, g;
  GEN p1, p2, rep;
  FAD_t fdata;

#ifdef CHECK_EXTENSIONS
  long cnt = 0, nb, j;
  GEN vpl;
  fprintferr("Number of extensions: %ld\n", itos(data->nbext));
#endif

  g   = ugcd(data->e, umodiu(data->qm1, data->e));
  rep = zerovec(g);

  p1 = gadd(gpowgs(pol_x(0), data->e), data->p);
#ifdef CHECK_EXTENSIONS
  vpl = zerovec(g);
  if (data->e == 1)
  {
    FieldData(data, &fdata, p1, 0);
    nb = 1;
  }
  else
  {
    FieldData(data, &fdata, p1, 1);
    nb = NbConjugateFields(data, &fdata);
  }
  fprintferr("Found %ld field(s)\n", nb);
  cnt += nb;
  gel(rep, 1) = gcopy(fdata.topx);
  gel(vpl, 1) = p1;
  if (data->e != 1) FreeFieldData(&fdata);
#else
  FieldData(data, &fdata, p1, 0);
  gel(rep, 1) = fdata.topx;
#endif

  if (g > 1)
  {
    ulong pmodg = umodiu(data->p, g);
    long r = 1, ct = 1;
    GEN sv = InitSieve(g-1);
    while (r)
    {
      long gr;
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
	gr = Fl_mul(gr, pmodg, g);
      }
      while (gr != r);
      r  = NextZeroValue(sv, r);
    }
    setlg(rep, ct+1);
  }

#ifdef CHECK_EXTENSIONS
  if (!equalis(data->nbext, cnt))
    pari_err(talker,"Number of fields incorrect in TamelyRamifiedCase\n");
#endif

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
static GEN
StructureOmega(KRASNER_t *data, GEN *pnbpol)
{
  GEN nbpol, O = cgetg(data->e + 1, t_VEC);
  long i;

  nbpol = gen_1;
  for (i = 0; i < data->e; i++)
  {
    long v_start, v_end, zero, nbcf;
    v_end = data->c;
    zero = 0;
    if (i == 0)
    {
      v_start = 1;
      nbcf = itos(mulii(data->qm1, powiu(data->q, data->c - 1)));
    }
    else
    {
      GEN p1;
      v_start = function_l(data->p, data->a, data->b, i);
      p1 = powis(data->q, data->c - v_start);
      if (i == data->b)
	p1 = mulii(p1, data->qm1);
      else
      {
	p1 = mulii(p1, data->q);
	zero = 1;
      }
      nbcf = itos(p1);
    }
    gel(O, i+1) = mkvecsmall4(v_start, v_end, zero, nbcf);
    nbpol = muliu(nbpol, nbcf);
  }
  *pnbpol = nbpol; return O;
}

/* a random element of the finite field */
static GEN
RandomFF(KRASNER_t *data)
{
  long i, l = data->f + 2, p = itou(data->p);
  GEN c = cgetg(l, t_POL);
  c[1] = evalvarn(data->v);
  for (i = 2; i < l; i++) gel(c, i) = utoi(random_Fl(p));
  return ZX_renormalize(c, l);
}
static GEN
RandomPol(KRASNER_t *data, GEN Omega)
{
  long i, j, l = data->e + 3;
  GEN pol = cgetg(l, t_POL);
  pol[1] = evalsigne(1) | evalvarn(0);
  for (i = 1; i <= data->e; i++)
  {
    GEN cf = gel(Omega, i);
    long st = cf[1], ed = cf[2], zr = cf[3];
    GEN pp = data->p, c;
    for (;;) {
      c = RandomFF(data);
      if (zr || signe(c)) break;
    } /* if (!zr) insist on c != 0 */
    for (j = 1; j <= ed-st; j++)
    {
      c = gadd(c, ZX_Z_mul(RandomFF(data), pp));
      pp = mulii(data->p, pp);
    }
    gel(pol, i+1) = ZX_Z_mul(c, powiu(data->p, st));
  }
  gel(pol, i+1) = gen_1; /* monic */
  return pol;
}

static GEN
WildlyRamifiedCase(KRASNER_t *data)
{
  long nbext, ct, fd, nb = 0, j;
  GEN nbpol, rpl, rep, Omega;
  FAD_t **vfd;
  pari_timer T;
  pari_sp av = avma, av2;

  /* Omega = vector giving the structure of the set Omega */
  /* nbpol = number of polynomials to consider = |Omega| */
  Omega = StructureOmega(data, &nbpol);
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
    rpl = RandomPol(data, Omega);
    if (DEBUGLEVEL>3) fprintferr("considering polynomial %Ps\n", rpl);

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
	fprintferr("%ld more extension%s\t(%ld/%ld, %ldms)\n",
                   nb, (nb == 1)? "": "s", fd, nbext, TIMER(&T));
    }
    avma = av2;
  }

  rep = cgetg(ct+1, t_VEC);
  for (j = 0; j < ct; j++)
  {
    gel(rep, j+1) = gcopy(((FAD_t*)vfd[j])->topx);
    FreeFieldData((FAD_t*)vfd[j]);
  }
  FreeRootTable(data->roottable);
  return gerepileupto(av, rep);
}

/* return a cyclotomic polynomial (mod pred) of degree f and variable v */
static GEN
CycloPol(KRASNER_t *data)
{
  GEN p1, p2, p3;
  p1 = init_Fq(data->p, data->f, data->v);
  p2 = gener_FpXQ(p1, data->p, NULL);
  p3 = ZpXQ_sqrtnlift(gen_1, data->qm1, p2, p1, data->p, data->r);

  return RgX_to_FpX(ZXQ_charpoly(p3, p1, data->v), data->pred);
}

/* Compute an absolute polynomial for all the totally ramified
   extensions of Q_p(z) of degree e and discriminant p^{e + j - 1}
   where z is a root of upl defining an unramified extension of Q_p */
/* See padicfields for the meaning of flag */
static GEN
GetRamifiedPol(GEN p, GEN efj, long v, long flag)
{
  long e = efj[1], f = efj[2], j = efj[3];
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
  data.q   = powiu(p, f);
  data.qm1 = subis(data.q, 1);
  data.v   = v;
  data.r   = 1 + 2*data.a + ceildiv(2*data.b+3, e); /* enough precision */
  data.pred  = powiu(p, data.r);
  data.nbext = NumberExtensions(&data);

  if (flag == 2) return data.nbext;

  data.upl   = CycloPol(&data);
  data.uplr  = FpX_red(data.upl, data.p);
  data.frob  = FpXQ_pow(pol_x(v), p, data.upl, data.pred);
  if (DEBUGLEVEL>1) fprintferr("  Unramified part %Ps\n", data.upl);
  data.roottable = NULL;
  if (dvdsi(e, p))
  {
    GEN npol = powis(data.q, e+1);
    if (lgefint(data.p) == 3 && expi(npol) < 19)
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
      gel(p1, i) = mkvec4(gcopy(gel(pols, i)), stoi(e), stoi(f), stoi(f*(e+j-1)));
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
  long m = 0, d = -1, av = avma;

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
  { /* maximal possible discriminant valuation: m * (1+v_p(m)) - 1 */
    long ds = m * (1 + u_pval(m, p)) - 1;
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
