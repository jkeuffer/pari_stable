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
/*                  COMPUTATION OF STARK UNITS                     */
/*                    OF TOTALLY REAL FIELDS                       */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"

#define EXTRA_PREC (DEFAULTPREC-1)
#define ADD_PREC   (DEFAULTPREC-2)*3

extern GEN roots_to_pol_intern(GEN L, GEN a, long v, int plus);
extern GEN bnrGetSurj(GEN bnr1, GEN bnr2);

/* ComputeCoeff */
typedef struct {
  GEN L0, L1, L11, L2; /* VECSMALL of p */
  GEN *L1ray, *L11ray; /* precomputed isprincipalray(pr), pr | p */
  GEN *rayZ; /* recomputed isprincipalray(i), i < condZ */
  long condZ; /* generates cond(bnr) \cap Z, assumed small */
} LISTray;

/* Char evaluation */
typedef struct {
  long ord; 
  GEN *val, chi;
} CHI_t;

/* RecCoeff */
typedef struct {
  GEN M, beta, B, U, nB;
  long v, G, N;
} RC_data;

/********************************************************************/
/*                    Miscellaneous functions                       */
/********************************************************************/
/* exp(2iPi/den), assume den a t_INT */
GEN
InitRU(GEN den, long prec)
{
  GEN c,s, z;
  if (egalii(den, gdeux)) return stoi(-1);
  gsincos(divri(gmul2n(mppi(prec),1), den), &s, &c, prec);
  z = cgetg(3, t_COMPLEX);
  z[1] = (long)c;
  z[2] = (long)s; return z;
}
/* Compute the image of logelt by chi as a complex number
   see InitChar in part 3 */
static GEN
ComputeImagebyChar(GEN chi, GEN logelt)
{
  GEN gn = gmul((GEN)chi[1], logelt), x = (GEN)chi[2];
  long d = itos((GEN)chi[3]), n = smodis(gn, d);
  /* x^d = 1 and, if d even, x^(d/2) = -1 */
  if ((d & 1) == 0)
  {
    d /= 2;
    if (n >= d) return gneg(gpowgs(x, n-d));
  }
  return gpowgs(x, n);
}

/* return n such that C(elt) = z^n */
static long
EvalChar_n(CHI_t *C, GEN logelt)
{
  GEN n = gmul(C->chi, logelt);
  return smodis(n, C->ord);
}
/* return C(elt) */
static GEN
EvalChar(CHI_t *C, GEN logelt)
{
  return C->val[EvalChar_n(C, logelt)];
}

static void
init_CHI(CHI_t *c, GEN CHI, GEN z)
{
  long i, d = itos((GEN)CHI[3]);
  GEN *v = (GEN*)new_chunk(d);
  v[1] = z;
  for (i=2; i<d; i++)
  {
    v[i] = gmul(v[i-1], z);
  }
  v[0] = gmul(v[i-1], z);
  c->chi = (GEN)CHI[1];
  c->ord = d; 
  c->val = v;
}

/* as t_COMPLEX */
static void
init_CHI_alg(CHI_t *c, GEN CHI) {
  GEN z = gmodulcp(polx[0], cyclo(itos((GEN)CHI[3]), 0));
  init_CHI(c,CHI,z);
}
/* as t_POLMOD */
static void
init_CHI_C(CHI_t *c, GEN CHI) {
  init_CHI(c,CHI, (GEN)CHI[2]);
}

/* Compute the conjugate character */
static GEN
ConjChar(GEN chi, GEN cyc)
{
  long i, l = lg(chi);
  GEN p1 = cgetg(l, t_VEC);

  for (i = 1; i < l; i++)
    if (!signe((GEN)chi[i]))
      p1[i] = zero;
    else
      p1[i] = lsubii((GEN)cyc[i], (GEN)chi[i]);

  return p1;
}

typedef struct {
  long r; /* rank = lg(gen) */
  GEN j; /* current elt is gen[1]^j[1] ... gen[r]^j[r] */
  GEN cyc; /* t_VECSMALL of elementary divisors */
} GROUP_t;

static int
NextElt(GROUP_t *G)
{
  long i = 1;
  if (G->r == 0) return 0; /* no more elt */
  while (++G->j[i] == G->cyc[i]) /* from 0 to cyc[i]-1 */
  {
    G->j[i] = 0;
    if (++i > G->r) return 0; /* no more elt */
  }
  return i; /* we have multiplied by gen[i] */
}

/* Compute all the elements of a group given by its SNF */
static GEN
EltsOfGroup(long order, GEN cyc)
{
  long i;
  GEN rep;
  GROUP_t G;

  G.cyc = gtovecsmall(cyc);
  G.r = lg(cyc)-1;
  G.j = vecsmall_const(G.r, 0);

  rep = cgetg(order + 1, t_VEC);
  rep[order] = (long)small_to_col(G.j);

  for  (i = 1; i < order; i++)
  {
    (void)NextElt(&G);
    rep[i] = (long)small_to_col(G.j);
  }
  return rep;
}

/* Let dataC as given by InitQuotient0, compute a system of
   representatives of the quotient */
static GEN
ComputeLift(GEN dataC)
{
  long order, i, av = avma;
  GEN cyc, surj, eltq, elt;

  order = itos((GEN)dataC[1]);
  cyc   = (GEN)dataC[2];
  surj  = (GEN)dataC[3];

  eltq = EltsOfGroup(order, cyc);

  elt = cgetg(order + 1, t_VEC);

  for (i = 1; i <= order; i++)
    elt[i] = (long)inverseimage(surj, (GEN)eltq[i]);

  return gerepileupto(av, elt);
}

/* A character is given by a vector [(c_i), z, d, pm] such that
   chi(id) = z ^ sum(c_i * a_i) where
     a_i= log(id) on the generators of bnr
     z  = exp(2i * Pi / d) */
static GEN
get_Char(GEN chi, GEN cyc, long prec)
{
  GEN d, C, chic;
  long i, l = lg(chi);

  chic = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
    chic[i] = ldiv((GEN)chi[i], (GEN)cyc[i]);

  C = cgetg(4, t_VEC);
  d = denom(chic);
  C[1] = lmul(d, chic);
  C[2] = (long)InitRU(d, prec);
  C[3] = (long)d;
  return C;
}

/* Let chi a character defined over bnr and primitive over bnrc,
   compute the corresponding primitive character and the vectors of
   prime ideals dividing bnr but not bnrc. Returns NULL if bnr = bnrc */
static GEN
GetPrimChar(GEN chi, GEN bnr, GEN bnrc, long prec)
{
  long i, l, av = avma, nd;
  GEN cyc, U, M, p1, cond, condc, p2, nf;
  GEN prdiff, Mrc;

  cond  = gmael(bnr, 2, 1);
  condc = gmael(bnrc, 2, 1);
  if (gegal(cond, condc)) return NULL;

  cyc   = gmael(bnr, 5, 2);
  Mrc   = diagonal(gmael(bnrc, 5, 2));
  nf    = gmael(bnr, 1, 7);

  M = bnrGetSurj(bnr, bnrc);
  U = (GEN)hnfall(concatsp(M, Mrc))[2];
  l = lg(chi);
  U = vecextract_i(U, l, lg(U)-1);
  U = rowextract_i(U, 1, l-1); /* upper right = projector to image */
  chi = gmul(chi, U);

  cond  = (GEN)cond[1];
  condc = (GEN)condc[1];
  p2 = (GEN)idealfactor(nf, cond)[1];
  l  = lg(p2);

  prdiff = cgetg(l, t_COL);
  for (nd=1, i=1; i < l; i++)
    if (!idealval(nf, condc, (GEN)p2[i])) prdiff[nd++] = p2[i];
  setlg(prdiff, nd);

  p1  = cgetg(3, t_VEC);
  p1[1] = (long)get_Char(chi,cyc,prec);
  p1[2] = lcopy(prdiff);

  return gerepileupto(av,p1);
}

static GEN
GetDeg(GEN dataCR)
{
  long i, l = lg(dataCR);
  GEN degs = cgetg(l, t_VECSMALL);

  for (i = 1; i < l; i++)
    degs[i] = itos(phi(gmael3(dataCR, i, 5, 3)));
  return degs;
}

/********************************************************************/
/*                    1rst part: find the field K                   */
/********************************************************************/

static GEN AllStark(GEN data,  GEN nf,  long flag,  long prec);
static GEN InitChar0(GEN dataD, long prec);

/* Let A be a finite abelian group given by its relation and let C
   define a subgroup of A, compute the order of A / C, its structure and
   the matrix expressing the generators of A on those of A / C */
static GEN
InitQuotient0(GEN DA, GEN C)
{
  GEN D, MQ, MrC, H, U, rep;

  H = gcmp0(C)? DA: C;
  MrC  = gauss(H, DA);
  (void)smithall(hnf(MrC), &U, NULL);
  MQ   = concatsp(gmul(H, U), DA);
  D = smithall(hnf(MQ), &U, NULL);

  rep = cgetg(5, t_VEC);
  rep[1] = (long)dethnf_i(D);
  rep[2] = (long)mattodiagonal(D);
  rep[3] = lcopy(U);
  rep[4] = lcopy(C);

  return rep;
}

/* Let m be a modulus et C a subgroup of Clk(m), compute all the data
 * needed to work with the quotient Clk(m) / C namely
 * 1) bnr(m)
 * 2.1) its order
 * 2.2) its structure
 * 2.3) the matrix Clk(m) ->> Clk(m)/C
 * 2.4) the group C */
static GEN
InitQuotient(GEN bnr, GEN C)
{
  GEN Mrm, dataquo = cgetg(3, t_VEC);
  long av;

  dataquo[1] = lcopy(bnr);
  av = avma;  Mrm = diagonal(gmael(bnr, 5, 2));
  dataquo[2] = lpileupto(av, InitQuotient0(Mrm, C));

  return dataquo;
}

/* Let s: A -> B given by P, and let DA, DB be resp. the matrix of the
   relations of A and B, compute the kernel of s. If DA = 0 then A is free */
static GEN
ComputeKernel0(GEN P, GEN DA, GEN DB)
{
  ulong av = avma;
  long nbA = lg(DA)-1, rk;
  GEN herm, U;

  herm  = hnfall(concatsp(P, DB));
  rk = nbA + lg(DB) - lg(herm[1]);
  U = (GEN)herm[2];
  U = vecextract_i(U, 1,rk);
  U = rowextract_i(U, 1,nbA);

  if (!gcmp0(DA)) U = concatsp(U, DA);
  return gerepileupto(av, hnf(U));
}

/* Let m and n be two moduli such that n|m and let C be a congruence
   group modulo n, compute the corresponding congruence group modulo m
   ie the kernel of the map Clk(m) ->> Clk(n)/C */
static GEN
ComputeKernel(GEN bnrm, GEN dataC)
{
  long av = avma, i, nbm;
  GEN bnrn, Mrm, genm, Mrq, mgq, P;

  bnrn = (GEN)dataC[1];
  Mrm  = diagonal(gmael(bnrm, 5, 2));
  Mrq  = diagonal(gmael(dataC, 2, 2));
  genm = gmael(bnrm, 5, 3);
  nbm  = lg(genm) - 1;
  mgq  = gmael(dataC, 2, 3);

  P = cgetg(nbm + 1, t_MAT);
  for (i = 1; i <= nbm; i++)
    P[i] = lmul(mgq, isprincipalray(bnrn, (GEN)genm[i]));

  return gerepileupto(av, ComputeKernel0(P, Mrm, Mrq));
}

/* Let C a congruence group in bnr, compute its subgroups of index 2 as
   subgroups of Clk(bnr) */
static GEN
ComputeIndex2Subgroup(GEN bnr, GEN C)
{
  ulong av = avma;
  long nb, i;
  GEN D, Mr, U, T, subgrp;

  disable_dbg(0);

  Mr = diagonal(gmael(bnr, 5, 2));
  D = smithall(gauss(C, Mr), &U, NULL);
  T = gmul(C,ginv(U));
  subgrp  = subgrouplist(D, gdeux);
  nb = lg(subgrp) - 1;
  setlg(subgrp, nb); /* skip Id which comes last */
  for (i = 1; i < nb; i++)
    subgrp[i] = (long)hnf(concatsp(gmul(T, (GEN)subgrp[i]), Mr));

  disable_dbg(-1);
  return gerepilecopy(av, subgrp);
}

GEN
Order(GEN cyc, GEN x)
{
  ulong av = avma;
  long i, l = lg(cyc);
  GEN c,o,f = gun;
  for (i = 1; i < l; i++)
  {
    o = (GEN)cyc[i];
    c = mppgcd(o, (GEN)x[i]);
    if (!is_pm1(c)) o = diviiexact(o,c);
    f = mpppcm(f, o);
  }
  return gerepileuptoint(av, f);
}

/* Let pr be a prime (pr may divide mod(bnr)), compute the indexes
   e,f of the splitting of pr in the class field nf(bnr/subgroup) */
static GEN
GetIndex(GEN pr, GEN bnr, GEN subgroup)
{
  long av = avma, v, e, f;
  GEN bnf, mod, mod0, bnrpr, subpr, M, dtQ, p1;
  GEN rep, cycpr, cycQ;

  bnf  = (GEN)bnr[1];
  mod  = gmael(bnr, 2, 1);
  mod0 = (GEN)mod[1];

  v = idealval(bnf, mod0, pr);
  if (v == 0)
  {
    bnrpr = bnr;
    subpr = subgroup;
    e = 1;
  }
  else
  {
    GEN mpr = cgetg(3, t_VEC);
    GEN mpr0 = idealdivpowprime(bnf, mod0, pr, stoi(v));
    mpr[1] = (long)mpr0; /* part of mod coprime to pr */
    mpr[2] = mod[2];
    bnrpr = buchrayinitgen(bnf, mpr);
    cycpr = gmael(bnrpr, 5, 2);
    M = bnrGetSurj(bnr, bnrpr);
    M = gmul(M, subgroup);
    subpr = hnf(concatsp(M, diagonal(cycpr)));
    /* e = #(bnr/subgroup) / #(bnrpr/subpr) */
    e = itos( divii(dethnf_i(subgroup), dethnf_i(subpr)) );
  }

  /* f = order of [pr] in bnrpr/subpr */
  dtQ  = InitQuotient(bnrpr, subpr);
  p1   = isprincipalray(bnrpr, pr);
  p1   = gmul(gmael(dtQ, 2, 3), p1);
  cycQ = gmael(dtQ, 2, 2);
  f  = itos( Order(cycQ, p1) );

  rep = cgetg(3, t_VECSMALL);
  rep[1] = (long)e;
  rep[2] = (long)f;

  return gerepileupto(av, rep);
}


/* Given a conductor and a subgroups, return the corresponding
   complexity and precision required using quickpol */
static GEN
CplxModulus(GEN data, long *newprec, long prec)
{
  long av = avma, av2, pr, dprec;
  GEN nf, cpl, pol, p1;

  nf = gmael3(data, 1, 1, 7);

  p1 = cgetg(6, t_VEC);

  p1[1] = data[1];
  p1[2] = data[2];
  p1[3] = data[3];
  p1[4] = data[4];

  if (DEBUGLEVEL >= 2)
    fprintferr("\nTrying modulus = %Z and subgroup = %Z\n",
	       mael3(p1, 1, 2, 1), (GEN)p1[2]);

  dprec = DEFAULTPREC;

  av2 = avma;
  for (;;)
  {
    p1[5] = (long)InitChar0((GEN)data[3], dprec);
    pol   = gerepileupto(av2, AllStark(p1, nf, -1, dprec));
    if (!gcmp0(leading_term(pol)))
    {
      cpl = gnorml2(gtovec(pol));
      if (!gcmp0(cpl)) break;
    }
    pr = gexpo(pol)>>(TWOPOTBITS_IN_LONG+1);
    if (pr < 0) pr = 0;
    dprec = max(dprec, pr) + EXTRA_PREC;

    if (DEBUGLEVEL >= 2) err(warnprec, "CplxModulus", dprec);
  }

  if (DEBUGLEVEL >= 2) fprintferr("cpl = %Z\n", cpl);

  pr = gexpo(pol)>>TWOPOTBITS_IN_LONG;
  if (pr < 0) pr = 0;
  *newprec = max(prec, pr + EXTRA_PREC);

  return gerepileupto(av, cpl);
}

/* Let f be a conductor without infinite part and let C be a
   congruence group modulo f, compute (m,D) such that D is a
   congruence group of conductor m where m is a multiple of f
   divisible by all the infinite places but one, D is a subgroup of
   index 2 of Im(C) in Clk(m), no prime dividing f splits in the
   corresponding quadratic extension and m is of minimal norm. Return
   bnr(m), D, quotient Ck(m) / D and Clk(m) / C */
/* If fl != 0, try bnd extra moduli */
static GEN
FindModulus(GEN dataC, long fl, long *newprec, long prec, long bnd)
{
  long n, i, narch, nbp, maxnorm, minnorm, N, nbidnn, s, c, j, nbcand;
  long limnorm, first = 1, pr;
  ulong av = avma, av1, av0;
  GEN bnr, rep, bnf, nf, f, arch, m, listid, idnormn, bnrm, ImC;
  GEN candD, D, bpr, indpr, sgp, p1, p2, rb;

  bnr = (GEN)dataC[1];
  sgp = gmael(dataC, 2, 4);
  bnf = (GEN)bnr[1];
  nf  = (GEN)bnf[7];
  N   = degpol(nf[1]);
  f   = gmael3(bnr, 2, 1, 1);

  rep = cgetg(6, t_VEC);
  for (i = 1; i <= 5; i++) rep[i] = zero;

  /* if cpl < rb, it is not necessary to try another modulus */
  rb = powgi(gmul((GEN)nf[3], det(f)), gmul2n(gmael(bnr, 5, 1), 3));

  bpr = (GEN)idealfactor(nf, f)[1];
  nbp = lg(bpr) - 1;

  indpr = cgetg(nbp + 1,t_VECSMALL);
  for (i = 1; i <= nbp; i++)
  {
    p1 = GetIndex((GEN)bpr[i], bnr, sgp);
    indpr[i] = p1[1] * p1[2];
  }

  /* Initialization of the possible infinite part */
  arch = cgetg(N+1, t_VEC);
  for (i = 1; i <= N; i++) arch[i] = un;

  /* narch = (N == 2)? 1: N; -- if N=2, only one case is necessary */
  narch = N;

  m = cgetg(3, t_VEC);
  m[2] = (long)arch;

  /* we go from minnorm up to maxnorm, if necessary we increase these values.
     If we cannot find a suitable conductor of norm < limnorm, we stop */
  maxnorm = 50;
  minnorm = 1;
  limnorm = 400;

  if (DEBUGLEVEL >= 2)
    fprintferr("Looking for a modulus of norm: ");

  av0 = avma;
  for(;;)
  {
    /* compute all ideals of norm <= maxnorm */
    disable_dbg(0);
    listid = ideallist(nf, maxnorm);
    disable_dbg(-1);
    av1 = avma;

    for (n = minnorm; n <= maxnorm; n++)
    {
      if (DEBUGLEVEL >= 2) fprintferr(" %ld", n);

      idnormn = (GEN)listid[n];
      nbidnn  = lg(idnormn) - 1;
      for (i = 1; i <= nbidnn; i++)
      {
	rep = gerepilecopy(av1, rep);

        /* finite part of the conductor */
	m[1] = (long)idealmul(nf, f, (GEN)idnormn[i]);

	for (s = 1; s <= narch; s++)
	{
	  /* infinite part */
	  arch[N+1-s] = zero;

          /* compute Clk(m), check if m is a conductor */
	  disable_dbg(0);
	  bnrm = buchrayinitgen(bnf, m);
	  p1   = conductor(bnrm, gzero, -1);
	  disable_dbg(-1);
          arch[N+1-s] = un;
	  if (!signe(p1)) continue;

          /* compute Im(C) in Clk(m)... */
          ImC = ComputeKernel(bnrm, dataC);

          /* ... and its subgroups of index 2 */
          candD  = ComputeIndex2Subgroup(bnrm, ImC);
          nbcand = lg(candD) - 1;
          for (c = 1; c <= nbcand; c++)
          {
            /* check if m is the conductor */
            D  = (GEN)candD[c];
            disable_dbg(0);
            p1 = conductor(bnrm, D, -1);
            disable_dbg(-1);
            if (!signe(p1)) continue;

            /* check the splitting of primes */
            for (j = 1; j <= nbp; j++)
            {
              p1 = GetIndex((GEN)bpr[j], bnrm, D);
              if (p1[1] * p1[2] == indpr[j]) break; /* no good */
            }
            if (j <= nbp) continue;

            p2 = cgetg(6, t_VEC);
            p2[1] = (long)bnrm;
            p2[2] = (long)D;
            p2[3] = (long)InitQuotient(bnrm, D);
            p2[4] = (long)InitQuotient(bnrm, ImC);

            p1 = CplxModulus(p2, &pr, prec);

            if (first == 1 || gcmp(p1, (GEN)rep[5]) < 0)
            {
              *newprec = pr;
              for (j = 1; j <= 4; j++) rep[j] = p2[j];
              rep[5] = (long)p1;
            }

            if (!fl || gcmp(p1, rb) < 0)
            {
              rep[5] = (long)InitChar0((GEN)rep[3], *newprec);
              return gerepilecopy(av, rep);
            }
            if (DEBUGLEVEL>1) fprintferr("Trying to find another modulus...");
            first--;
          }
	}
        if (first <= bnd)
	{
	  if (DEBUGLEVEL>1)
	    fprintferr("No, we're done!\nModulus = %Z and subgroup = %Z\n",
		       gmael3(rep, 1, 2, 1), rep[2]);
	  rep[5] = (long)InitChar0((GEN)rep[3], *newprec);
	  return gerepilecopy(av, rep);
	}
      }
    }
    /* if necessary compute more ideals */
    rep = gerepilecopy(av0, rep);

    minnorm = maxnorm;
    maxnorm <<= 1;
    if (maxnorm > limnorm)
      err(talker, "Cannot find a suitable modulus in FindModulus");
  }
}

/********************************************************************/
/*                      2nd part: compute W(X)                      */
/********************************************************************/

/* compute W(chi) such that Ld(s,chi) = W(chi) Ld(1 - s, chi*),
   if flag != 0 do not check the result */
static GEN
ComputeArtinNumber(GEN dtcr, long flag, long prec)
{
  long av = avma, av2, i,j, nz, q, N, lim;
  GEN CHI, nc, dc, cond, condZ, cond0, cond1, lambda, nf, T;
  GEN cyc, vN, *vB, diff, vt, idg, mu, idh, zid, *gen, z, nchi;
  GEN classe, bnr, s, tr, den, muslambda, beta2, sarch;
  CHI_t C;
  GROUP_t G;

  CHI   = (GEN)dtcr[8];
  /* trivial case */
  if (cmpsi(2, (GEN)CHI[3]) >= 0) return gun;
  init_CHI_C(&C, CHI);

  bnr   = (GEN)dtcr[3];
  nf    = gmael(bnr, 1, 7);
  diff  = gmael(nf, 5, 5);
  T     = gmael(nf,5,4);
  cond  =  gmael(bnr, 2, 1);
  cond0 = (GEN)cond[1]; condZ = gcoeff(cond0,1,1);
  cond1 = (GEN)cond[2];
  N     = degpol(nf[1]);

  nc  = idealnorm(nf, cond0);
  dc  = idealmul(nf, diff, cond0);
  den = idealnorm(nf, dc);
  z   = InitRU(den, prec);

  q = 0;
  for (i = 1; i < lg(cond1); i++)
    if (gcmp1((GEN)cond1[i])) q++;

  /* compute a system of elements congru to 1 mod cond0 and giving all
     possible signatures for cond1 */
  sarch = zarchstar(nf, cond0, cond1, q);

  /* find lambda in diff.cond such that gcd(lambda.(diff.cond)^-1,cond0) = 1
     and lambda >> 0 at cond1 */
  lambda = idealappr(nf, dc);
  lambda = set_sign_mod_idele(nf, NULL, lambda, cond,sarch);
  idg = idealdivexact(nf, lambda, dc);

  /* find mu in idg such that idh=(mu) / idg is coprime with cond0 and
     mu >> 0 at cond1 */
  if (!gcmp1(gcoeff(idg, 1, 1)))
  {
    GEN p1 = idealfactor(nf, idg);
    GEN p2 = idealfactor(nf, cond0);
    p2[2] = (long)zerocol(lg(p2[1])-1);
    p1 = concat_factor(p1,p2);

    mu = idealapprfact(nf, p1);
    mu = set_sign_mod_idele(nf, NULL,mu, cond,sarch);
    idh = idealdivexact(nf, mu, idg);
  }
  else
  {
    mu  = gun;
    idh = idg;
  }

  muslambda = gmul(den, element_div(nf, mu, lambda));

  /* compute a system of generators of (Ok/cond)^* cond1-positive */
  zid = zidealstarinitgen(nf, cond0);
  cyc = gmael(zid, 2, 2);
  gen = (GEN*)gmael(zid, 2, 3);
  nz = lg(gen) - 1;

  nchi = cgetg(nz + 1, t_VECSMALL);
  for (i = 1; i <= nz; i++)
  {
    gen[i] = set_sign_mod_idele(nf, NULL,gen[i], cond,sarch);
    classe = isprincipalray(bnr, gen[i]);
    nchi[i] = (long)EvalChar_n(&C, classe);
  }

  /* Sum CHI(beta) * exp(2i * Pi * Tr(beta * mu / lambda) where beta
     runs through the classes of (Ok/cond0)^* and beta cond1-positive */

  vt = cgetg(N + 1, t_VEC); /* Tr(w_i) */
  for (i = 1; i <= N; i++) vt[i] = coeff(T,i,1);

  G.cyc = gtovecsmall(cyc);
  G.r = nz;
  G.j = vecsmall_const(nz, 0);

  vN = vecsmall_const(nz, 0);

  av2 = avma; lim = stack_lim(av2, 1);
  vB = (GEN*)cgetg(nz+1, t_VEC);
  for (i=1; i<=nz; i++) vB[i] = gun;

  tr = gmod(gmul(vt, muslambda), den); /* for beta = 1 */
  s = powgi(z, tr);

  for (;;)
  {
    if (! (i = NextElt(&G)) ) break;

    vB[i] = FpV_red(element_mul(nf, vB[i], gen[i]), condZ);
    vN[i] = addssmod(vN[i], nchi[i], C.ord);
    for (j=1; j<i; j++) { vN[j] = vN[i]; vB[j] = vB[i]; }
    
    vB[i]= set_sign_mod_idele(nf, NULL,vB[i], cond,sarch);
    beta2 = element_mul(nf, vB[i], muslambda);
    tr = gmod(gmul(vt, beta2), den);

    s = gadd(s, gmul((GEN)C.val[vN[i]], powgi(z,tr)));

    if (low_stack(lim, stack_lim(av2, 1)))
    {
      GEN *gptr[2]; gptr[0] = &s; gptr[1] = (GEN*)&vB;
      if (DEBUGMEM > 1) err(warnmem,"ComputeArtinNumber");
      gerepilemany(av2, gptr, 2);
    }
  }

  classe = isprincipalray(bnr, idh);
  s = gmul(s, EvalChar(&C, classe));
  s = gdiv(s, gsqrt(nc, prec));

  if (!flag &&  - expo(subrs(gnorm(s), 1)) < bit_accuracy(prec) >> 1)
    err(bugparier, "ComputeArtinNumber");

  return gerepileupto(av, gmul(s, gpowgs(gneg_i(gi),q)));
}

/* compute the constant W of the functional equation of
   Lambda(chi). If flag = 1 then chi is assumed to be primitive */
GEN
bnrrootnumber(GEN bnr, GEN chi, long flag, long prec)
{
  long av = avma, l;
  GEN cond, condc, bnrc, cyc, p1, p2, dtcr;

  if (flag < 0 || flag > 1) err(flagerr,"bnrrootnumber");

  checkbnr(bnr);

  cond = gmael(bnr, 2, 1);
  l    = lg(gmael(bnr, 5, 2));

  if ((typ(chi) != t_VEC) || (lg(chi) != l))
    err(talker, "incorrect character in bnrrootnumber");

  if (!flag)
  {
    condc = bnrconductorofchar(bnr, chi);
    if (gegal(cond, condc)) flag = 1;
  }
  else condc = cond;

  if (flag)
    bnrc = bnr;
  else
    bnrc = buchrayinitgen((GEN)bnr[1], condc);

  cyc  = gmael(bnr, 5, 2);
  p2 = get_Char(chi,cyc, prec);

  dtcr = cgetg(9, t_VEC);
  dtcr[1] = (long)chi;
  dtcr[2] = zero;
  dtcr[3] = (long)bnrc;
  dtcr[4] = (long)bnr;
  dtcr[5] = (long)p2;
  dtcr[6] = zero;
  dtcr[7] = (long)condc;

  p1 = GetPrimChar(chi, bnr, bnrc, prec);

  if (!p1)
    dtcr[8] = (long)p2;
  else
    dtcr[8] = p1[1];

  return gerepileupto(av, ComputeArtinNumber(dtcr, 0, prec));
}

/********************************************************************/
/*               3rd part: initialize the characters                */
/********************************************************************/

static GEN
LiftChar(GEN cyc, GEN Mat, GEN chi)
{
  long lm, l, i, j, av;
  GEN lchi, s;

  lm = lg(cyc) - 1;
  l  = lg(chi) - 1;

  lchi = cgetg(lm + 1, t_VEC);
  for (i = 1; i <= lm; i++)
  {
    av = avma;
    s  = gzero;

    for (j = 1; j <= l; j++)
      s = gadd(s, gmul((GEN)chi[j], gcoeff(Mat, j, i)));

    lchi[i] = (long)gerepileupto(av, gmod(gmul(s, (GEN)cyc[i]), (GEN)cyc[i]));
  }

  return lchi;
}

/* Let chi be a character, A(chi) corresponding to the primes dividing diff
   at s = flag. If s = 0, returns [r, A] where r is the order of vanishing
   at s = 0 corresponding to diff. No Garbage collector */
static GEN
ComputeAChi(GEN dtcr, long flag, long prec)
{
  long l, i, r;
  GEN p1, ray, A, rep, diff, chi, bnrc, nf;

  diff = (GEN)dtcr[6];
  bnrc = (GEN)dtcr[3]; nf = checknf(bnrc);
  chi  = (GEN)dtcr[8];
  l    = lg(diff) - 1;

  A = gun;
  r = 0;

  for (i = 1; i <= l; i++)
  {
    GEN B;
    ray = isprincipalray(bnrc, (GEN)diff[i]);
    p1  = ComputeImagebyChar(chi, ray);

    if (flag)
      B = gsub(gun, gdiv(p1, idealnorm(nf, (GEN)diff[i])));
    else if (gcmp1(p1))
    {
      B = glog(idealnorm(nf, (GEN)diff[i]), prec);
      r++;
    }
    else
      B = gsub(gun, p1);
    A = gmul(A, B);
  }

  if (flag) return A;

  rep = cgetg(3, t_VEC);
  rep[1] = lstoi(r);
  rep[2] = (long)A;

  return rep;
}

static GEN
_data9(GEN arch, long r1, long r2)
{
  GEN z = cgetg(5, t_VECSMALL);
  long i, b, q = 0;
 
  for (i=1; i<=r1; i++) if (signe(arch[i])) q++;
  z[1] = q; b = r1 - q;
  z[2] = b;
  z[3] = r2;
  z[4] = max(b+r2+1, r2+q);
  return z;
}

/* Given a list [chi, cond(chi)] of characters over Cl(bnr), compute a
   vector dataCR containing for each character:
   1: chi
   2: the constant C(chi)
   3: bnr(cond(chi))
   4: bnr(m)
   5: [(c_i), z, d, pm] in bnr(m)
   6: diff(chi) primes dividing m but not cond(chi)
   7: finite part of cond(chi)
   8: [(c_i), z, d, pm] in bnr(cond(chi))
   9: [q, r1 - q, r2, rc] where
        q = number of real places in cond(chi)
        rc = max{r1 + r2 - q + 1, r2 + q} */
static GEN
InitChar(GEN bnr, GEN listCR, long prec)
{
  GEN bnf = checkbnf(bnr), nf = checknf(bnf);
  GEN modul, dk, C, dataCR, chi, cond, Mr, z1, p1;
  long N, r1, r2, prec2, h, i, j, av = avma;

  modul = gmael(bnr, 2, 1);
  Mr    = gmael(bnr, 5, 2);
  dk    = (GEN)nf[3];
  N     = degpol(nf[1]);
  nf_get_sign(nf, &r1,&r2);
  prec2 = ((prec-2) << 1) + EXTRA_PREC;
  C     = gmul2n(gsqrt(gdiv(absi(dk), gpowgs(mppi(prec2),N)), prec2), -r2);

  disable_dbg(0);

  h = lg(listCR) - 1;
  dataCR = cgetg(h + 1, t_VEC);
  for (i = 1; i <= h ;i++)
    dataCR[i] = lgetg(10, t_VEC);

  z1 = _data9((GEN)modul[2],r1,r2);

  for (i = 1; i <= h; i++)
  {
    GEN olddata, data = (GEN)dataCR[i];

    chi  = gmael(listCR, i, 1);
    cond = gmael(listCR, i, 2);

    /* do we already know about the invariants of chi? */
    olddata = NULL;
    for (j = 1; j < i; j++)
      if (gegal(cond, gmael(listCR, j, 2)))
       { olddata = (GEN)dataCR[j]; break; }

    /* if cond(chi) = cond(bnr) */
    if (!olddata && gegal(cond, modul))
    {
      data[2] = lmul(C, gsqrt(det((GEN)cond[1]), prec2));
      data[3] = (long)bnr;
      data[6] = lgetg(1, t_VEC);
      data[7] = modul[1];
      data[9] = (long)z1;

      olddata = data;
    }

    data[1] = (long)chi; /* the character */
    if (!olddata)
    {
      data[2] = lmul(C, gsqrt(det((GEN)cond[1]), prec2));
      data[3] = (long)buchrayinitgen(bnf, cond);
    }
    else
    {
      data[2] = olddata[2]; /* constant C(chi) */
      data[3] = olddata[3]; /* bnr(cond(chi)) */
    }
    data[4] = (long)bnr; /* bnr(m) */
    data[5] = (long)get_Char(chi,Mr,prec); /* char associated to bnr(m) */

    /* compute diff(chi) and the corresponding primitive character */
    data[7] = cond[1];
    p1 = GetPrimChar(chi, bnr, (GEN)data[3], prec2);
    if (p1)
    {
      data[6] = p1[2];
      data[8] = p1[1];
    }
    else
    {
      data[6] = lgetg(1, t_VEC);
      data[8] = data[5];
    }
    data[9] = olddata? olddata[9]: (long)_data9((GEN)cond[2],r1,r2);
  }

  disable_dbg(-1);
  return gerepilecopy(av, dataCR);
}

/* compute the list of characters to consider for AllStark and
   initialize the data to compute with them */
static GEN
InitChar0(GEN dataD, long prec)
{
  GEN MrD, listCR, p1, chi, lchi, Surj, cond, bnr, p2, Mr, d, allCR;
  long hD, h, nc, i, j, lD, tnc, av = avma;

  Surj = gmael(dataD, 2, 3);
  MrD  = gmael(dataD, 2, 2);
  bnr  = (GEN)dataD[1];
  Mr   = gmael(bnr, 5, 2);
  hD   = itos(gmael(dataD, 2, 1));
  h    = hD >> 1;
  lD   = lg(MrD)-1;

  disable_dbg(0);

  listCR = cgetg(h + 1, t_VEC); /* non-conjugate characters */
  nc  = 1;
  allCR  = cgetg(h + 1, t_VEC); /* all characters, including conjugates */
  tnc = 1;

  p1 = EltsOfGroup(hD, MrD);

  for (i = 1; tnc <= h; i++)
  {
    /* lift a character of D in Clk(m) */
    chi = (GEN)p1[i];
    for (j = 1; j <= lD; j++) chi[j] = ldiv((GEN)chi[j], (GEN)MrD[j]);
    lchi = LiftChar(Mr, Surj, chi);

    for (j = 1; j < tnc; j++)
      if (gegal(lchi, (GEN)allCR[j])) break;
    if (j != tnc) continue;

    cond = bnrconductorofchar(bnr, lchi);
    if (gcmp0((GEN)cond[2])) continue;

    /* the infinite part of chi is non trivial */
    p2 = cgetg(3, t_VEC);
    p2[1] = (long)lchi;
    p2[2] = (long)cond;
    listCR[nc++] = (long)p2;
    allCR[tnc++] = (long)lchi;

    /* if chi is not real, add its conjugate character to allCR */
    d = Order(Mr, lchi);
    if (!egalii(d, gdeux))
      allCR[tnc++] = (long)ConjChar(lchi, Mr);
  }

  setlg(listCR, nc);
  disable_dbg(-1);
  return gerepileupto(av, InitChar(bnr, listCR, prec));
}

/* recompute dataCR with the new precision */
static GEN
CharNewPrec(GEN dataCR, GEN nf, long prec)
{
  GEN dk, C, p1;
  long N, l, j, prec2;

  dk    =  (GEN)nf[3];
  N     =  degpol((GEN)nf[1]);
  prec2 = ((prec - 2)<<1) + EXTRA_PREC;

  C = mpsqrt(gdiv(dk, gpowgs(mppi(prec2), N)));

  l = lg(dataCR);
  for (j = 1; j < l; j++)
  {
    GEN dtcr = (GEN)dataCR[j];
    dtcr[2] = lmul(C, gsqrt(dethnf_i((GEN)dtcr[7]), prec2));

    mael3(dtcr, 3, 1, 7) = (long)nf;

    p1 = (GEN)dtcr[5]; p1[2] = (long)InitRU((GEN)p1[3], prec2);
    p1 = (GEN)dtcr[8]; p1[2] = (long)InitRU((GEN)p1[3], prec2);
  }

  return dataCR;
}

/********************************************************************/
/*             4th part: compute the coefficients an(chi)           */
/*                                                                  */
/* matan entries are arrays of ints containing the coefficients of  */
/* an(chi) as a polmod modulo cyclo(order(chi))                     */
/********************************************************************/

static void
_0toCoeff(int *rep, long deg)
{
  long i;
  for (i=0; i<deg; i++) rep[i] = 0;
}

/* transform a polmod into coeff */
static void
Polmod2Coeff(int *rep, GEN polmod, long deg)
{
  GEN pol = (GEN)polmod[2];
  long i,d = degpol(pol);

  pol += 2;
  for (i=0; i<=d; i++) rep[i] = itos((GEN)pol[i]);
  for (   ; i<deg; i++) rep[i] = 0;
}

/* initialize a deg * n matrix of ints */
static int**
InitMatAn(long n, long deg, long flag)
{
  long i, j;
  int *a, **A = (int**)gpmalloc((n+1)*sizeof(int*));
  A[0] = NULL;
  for (i = 1; i <= n; i++)
  {
    a = (int*)gpmalloc(deg*sizeof(int));
    A[i] = a; a[0] = (i == 1 || flag);
    for (j = 1; j < deg; j++) a[j] = 0;
  }
  return A;
}

static void
FreeMat(int **A, long n)
{
  long i;
  for (i = 0; i <= n; i++)
    if (A[i]) free((void*)A[i]);
  free((void*)A);
}

/* initialize coeff reduction */
static int**
InitReduction(GEN CHI, long deg)
{
  long av = avma,j;
  int **A;
  GEN d,polmod,pol, x = polx[0];

  A   = (int**)gpmalloc(deg*sizeof(int*));
  d   = (GEN)CHI[3];
  pol = cyclo(itos(d), 0);
  for (j = 0; j < deg; j++)
  {
    A[j] = (int*)gpmalloc(deg*sizeof(int));
    polmod = gmodulcp(gpowgs(x, deg + j), pol);
    Polmod2Coeff(A[j], polmod, deg);
  }

  avma = av; return A;
}

#if 0
void
pan(int **an, long n, long deg)
{
  long i,j;
  for (i = 1; i <= n; i++)
  {
    fprintferr("n = %ld: ",i);
    for (j = 0; j < deg; j++) fprintferr("%d ",an[i][j]);
    fprintferr("\n");
  }
}
#endif

/* returns 0 if c is zero, 1 otherwise. */
static int
IsZero(int* c, long deg)
{
  long i;
  for (i = 0; i < deg; i++)
    if (c[i]) return 0;
  return 1;
}

/* set c0 <-- c0 * c1 */
static void
MulCoeff(int *c0, int* c1, int** reduc, long deg)
{
  long i,j;
  int c, *T;

  if (IsZero(c0,deg)) return;

  T = (int*)new_chunk(2*deg);
  for (i = 0; i < 2*deg; i++)
  {
    c = 0;
    for (j = 0; j <= i; j++)
      if (j < deg && j > i - deg) c += c0[j] * c1[i-j];
    T[i] = c;
  }
  for (i = 0; i < deg; i++)
  {
    c = T[i];
    for (j = 0; j < deg; j++) c += reduc[j][i] * T[deg+j];
    c0[i] = c;
  }
}

/* c0 <- c0 + c1 * c2 */
static void
AddMulCoeff(int *c0, int *c1, int* c2, int** reduc, long deg)
{
  long av,i,j;
  int c, *t;

  if (IsZero(c2,deg)) return;
  if (!c1) /* c1 == 1 */
  {
    for (i = 0; i < deg; i++) c0[i] += c2[i];
    return;
  }
  av = avma;
  t = (int*)new_chunk(2*deg); /* = c1 * c2, not reduced */
  for (i = 0; i < 2*deg; i++)
  {
    c = 0;
    for (j = 0; j <= i; j++)
      if (j < deg && j > i - deg) c += c1[j] * c2[i-j];
    t[i] = c;
  }
  for (i = 0; i < deg; i++)
  {
    c = t[i];
    for (j = 0; j < deg; j++) c += reduc[j][i] * t[deg+j];
    c0[i] += c;
  }
  avma = av;
}

/* evaluate the coeff. No Garbage collector */
static GEN
EvalCoeff(GEN z, int* c, long deg)
{
  long i,j;
  GEN e, r;

  if (!c) return gzero;
#if 0
  /* standard Horner */
  e = stoi(c[deg - 1]);
  for (i = deg - 2; i >= 0; i--)
    e = gadd(stoi(c[i]), gmul(z, e));
#else
  /* specific attention to sparse polynomials */
  e = NULL;
  for (i = deg-1; i >=0; i=j-1)
  {
    for (j=i; c[j] == 0; j--)
      if (j==0)
      {
        if (!e) return NULL;
        if (i!=j) z = gpuigs(z,i-j+1);
        return gmul(e,z);
      }
    if (e)
    {
      r = (i==j)? z: gpuigs(z,i-j+1);
      e = gadd(gmul(e,r), stoi(c[j]));
    }
    else
      e = stoi(c[j]);
  }
#endif
  return e;
}

/* copy the n * (m+1) array matan */
static void
CopyCoeff(int** a, int** a2, long n, long m)
{
  long i,j;

  for (i = 1; i <= n; i++)
  {
    int *b = a[i], *b2 = a2[i];
    for (j = 0; j < m; j++) b2[j] = b[j];
  }
}

/* return q*p if <= n. Beware overflow */
static long
next_pow(long q, long p, long n)
{
  const GEN x = muluu((ulong)q, (ulong)p);
  const ulong qp = (ulong)x[2];
  return (lgefint(x) > 3 || qp > (ulong)n)? 0: qp;
}

static void
an_AddMul(int **an,int **an2, long np, long n, long deg, GEN chi, int **reduc)
{
  GEN chi2 = chi;
  long q, qk, k;
  int *c, *c2 = (int*)new_chunk(deg);

  CopyCoeff(an, an2, n/np, deg);
  for (q=np;;)
  {
    if (gcmp1(chi2)) c = NULL; else { Polmod2Coeff(c2, chi2, deg); c = c2; }
    for(k = 1, qk = q; qk <= n; k++, qk += q)
      AddMulCoeff(an[qk], c, an2[k], reduc, deg);
    if (! (q = next_pow(q,np, n)) ) break;

    chi2 = gmul(chi2, chi);
  }
}

/* correct the coefficients an(chi) according with diff(chi) in place */
static void
CorrectCoeff(GEN dtcr, int** an, int** reduc, long n, long deg)
{
  ulong av = avma;
  long lg, av1, j, np;
  int **an2;
  GEN bnrc, diff, ray, chi, CHI, pr;
  CHI_t C;

  diff =  (GEN)dtcr[6];
  lg   =  lg(diff) - 1;
  if (!lg) return;

  bnrc =  (GEN)dtcr[3];
  CHI  =  (GEN)dtcr[8]; init_CHI_alg(&C, CHI);

  if (DEBUGLEVEL > 2) fprintferr("diff(CHI) = %Z", diff);

  an2 = InitMatAn(n, deg, 0);
  av1 = avma;
  for (j = 1; j <= lg; j++)
  {
    pr  = (GEN)diff[j];
    np = itos(powgi((GEN)pr[1], (GEN)pr[4]));

    ray = isprincipalray(bnrc, pr);
    chi  = EvalChar(&C,ray);

    an_AddMul(an,an2,np,n,deg,chi,reduc);
    avma = av1;
  }
  FreeMat(an2, n); avma = av;
}

/* compute the coefficients an in the general case */
static int**
ComputeCoeff(GEN dtcr, LISTray *R, long n, long deg)
{
  ulong av = avma, av2;
  long i, l, np;
  int **an, **reduc, **an2;
  GEN L, CHI, ray, chi;
  CHI_t C;

  CHI = (GEN)dtcr[5]; init_CHI_alg(&C, CHI);

  an  = InitMatAn(n, deg, 0);
  an2 = InitMatAn(n, deg, 0);
  reduc  = InitReduction(CHI, deg);
  av2 = avma;

  L = R->L1; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    np = L[i]; ray = R->L1ray[i];
    chi  = EvalChar(&C, ray);
    an_AddMul(an,an2,np,n,deg,chi,reduc);
  }
  FreeMat(an2, n);

  CorrectCoeff(dtcr, an, reduc, n, deg);
  FreeMat(reduc, deg-1);
  avma = av; return an;
}

/********************************************************************/
/*              5th part: compute L-functions at s=1                */
/********************************************************************/
static void
_append(GEN L, GEN z)
{
  long l = lg(L);
  L[l] = (long)z; setlg(L,l+1);
}

static void
deg11(LISTray *R, long p, GEN bnr, GEN pr) {
  GEN z = isprincipalray(bnr, pr); 
  _append(R->L1, (GEN)p);
  _append((GEN)R->L1ray, z);
}
static void
deg12(LISTray *R, long p, GEN bnr, GEN Lpr) {
  GEN z = isprincipalray(bnr, (GEN)Lpr[1]); 
  _append(R->L11, (GEN)p);
  _append((GEN)R->L11ray, z);
}
static void
deg0(LISTray *R, long p) {
  _append(R->L0, (GEN)p);
}
static void
deg2(LISTray *R, long p) {
  _append(R->L2, (GEN)p);
}

/* pi(x) <= ?? */
static long
PiBound(long x)
{
  double lx = log((double)x);
  return 1 + (long) x/lx * (1 + 3/(2*lx));
}

static GEN
_alloc(long n, long t)
{
  GEN z = new_chunk(n);
  z[0] = evaltyp(t) | evallg(1);
  return z;
}

static void
InitPrimesQuad(GEN bnr, long nmax, LISTray *R)
{
  ulong av = avma;
  GEN bnf = (GEN)bnr[1], cond = gmael3(bnr,2,1,1);
  long p,i,l, condZ = itos(gcoeff(cond,1,1)), contZ = itos(content(cond));
  GEN prime, pr, nf = checknf(bnf), dk = (GEN)nf[3];
  byteptr d = diffptr + 1;
  GEN *gptr[7];

  l = 1 + PiBound(nmax);
  R->L0  = _alloc(l, t_VECSMALL);
  R->L2  = _alloc(l, t_VECSMALL); R->condZ = condZ;
  R->L1 = _alloc(l, t_VECSMALL); R->L1ray = (GEN*)_alloc(l, t_VEC);
  R->L11 = _alloc(l, t_VECSMALL); R->L11ray = (GEN*)_alloc(l, t_VEC);
  prime = stoi(2);
  for (p = 2; p <= nmax; p += *d++, prime[2] = p)
    switch (krogs(dk, p))
    {
    case -1: /* inert */
      if (condZ % p == 0) deg0(R,p); else deg2(R,p);
      break;
    case 1: /* split */
      pr = primedec(nf, prime);
      if      (condZ % p != 0) deg12(R, p, bnr, pr);
      else if (contZ % p == 0) deg0(R,p);
      else
      {
        pr = idealval(nf, cond, (GEN)pr[1])? (GEN)pr[2]: (GEN)pr[1];
        deg11(R, p, bnr, pr);
      }
      break;
    default: /* ramified */
      if (condZ % p == 0) deg0(R,p);
      else
      {
        pr = (GEN)primedec(nf, prime)[1];
        deg11(R, p, bnr, pr);
      }
      break;
    }
  /* precompute isprincipalray(x), x in Z */
  R->rayZ = (GEN*)cgetg(condZ, t_VEC);
  for (i=1; i<condZ; i++)
    R->rayZ[i] = (cgcd(i,condZ) == 1)? isprincipalray(bnr, stoi(i)): gzero;

  gptr[0] = &(R->L0);
  gptr[1] = &(R->L2);  gptr[2] = (GEN*)&(R->rayZ);
  gptr[3] = &(R->L1);  gptr[5] = (GEN*)&(R->L1ray);
  gptr[4] = &(R->L11); gptr[6] = (GEN*)&(R->L11ray);
  gerepilemany(av,gptr,7);
}

static void
InitPrimes(GEN bnr, long nmax, LISTray *R)
{
  ulong av = avma;
  GEN bnf = (GEN)bnr[1], cond = gmael3(bnr,2,1,1);
  long np,p,j, condZ = itos(gcoeff(cond,1,1));
  GEN Npr, tabpr, prime, pr, nf = checknf(bnf);
  byteptr d = diffptr + 1;
  GEN *gptr[7];

  R->condZ = condZ;
  R->L1 = _alloc(nmax, t_VECSMALL);
  R->L1ray = (GEN*)_alloc(nmax, t_VEC);
  prime = stoi(2);
  for (p = 2; p <= nmax; p += *d++, prime[2] = p)
  {
    tabpr = primedec(nf, prime);
    for (j = 1; j < lg(tabpr); j++)
    {
      pr  = (GEN)tabpr[j];
      Npr = powgi((GEN)pr[1], (GEN)pr[4]);
      if (is_bigint(Npr) || (np = Npr[2]) > nmax) continue;
      if (condZ % p == 0 && idealval(nf, cond, pr)) continue;

      _append(R->L1, (GEN)np);
      _append((GEN)R->L1ray, isprincipalray(bnr, pr));
    }

  }
  gptr[0] = &(R->L1);  gptr[1] = (GEN*)&(R->L1ray);
  gerepilemany(av,gptr,2);
}

static GEN
get_limx(long r1, long r2, long prec, GEN *pteps)
{
  GEN eps, p1, a, c0, A0, limx, Pi2 = gmul2n(mppi(DEFAULTPREC), 1);
  long r, N;

  N = r1 + 2*r2; r = r1 + r2;
  a = gmulgs(gpow(gdeux, gdiv(stoi(-2*r2), stoi(N)), DEFAULTPREC), N);

  eps = realun(DEFAULTPREC); setexpo(eps, -bit_accuracy(prec));
  c0 = gpowgs(mpsqrt(Pi2), r-1);
  c0 = gdivgs(gmul2n(c0,1), N);
  c0 = gmul(c0, gpow(gdeux, gdiv(stoi(r1 * (r2-1)), stoi(2*N)),
		     DEFAULTPREC));

  A0 = glog(gdiv(gmul2n(c0,1), eps), DEFAULTPREC);

  limx = gpow(gdiv(a, A0), gdiv(stoi(N), gdeux), DEFAULTPREC);
  p1   = gsub(glog(A0, DEFAULTPREC), glog(a, DEFAULTPREC));
  p1   = gmulgs(p1, N*(r+1));
  p1   = gdiv(p1, gaddgs(gmul2n(A0, 2), 2*(r+1)));

  if (pteps) *pteps = eps;
  return gmul(limx, gaddgs(p1, 1));
}

static long
GetBoundN0(GEN C,  long r1, long r2,  long prec)
{
  ulong av = avma;
  GEN limx = get_limx(r1, r2, prec, NULL);

  limx = gfloor(gdiv(C, limx));
  if (is_bigint(limx))
    err(talker, "Too many coefficients (%Z) needed in GetST: computation impossible", limx);

  avma = av; return itos(limx);
}

static long
GetBoundi0(long r1, long r2,  long prec)
{
  long av = avma, imin, i0, itest;
  GEN ftest, borneps, eps, limx = get_limx(r1, r2, prec, &eps);
  GEN sqrtPi = mpsqrt(mppi(DEFAULTPREC));

  borneps = gmul(gmul2n(gun, r2), gpowgs(sqrtPi, r2-3));
  borneps = gdiv(gmul(borneps, gpowgs(stoi(5), r1)), eps);
  borneps = gdiv(borneps, gsqrt(limx, DEFAULTPREC));

  imin = 1;
  i0   = 1400;
  while(i0 - imin >= 4)
  {
    itest = (i0 + imin) >> 1;

    ftest = gpowgs(limx, itest);
    ftest = gmul(ftest, gpowgs(mpfactr(itest/2, DEFAULTPREC), r1));
    ftest = gmul(ftest, gpowgs(mpfactr(itest  , DEFAULTPREC), r2));

    if (gcmp(ftest, borneps) >= 0)
      i0 = itest;
    else
      imin = itest;
  }
  avma = av;

  return i0 &= ~1; /* make it even */
}

static GEN /* cf polcoeff */
_sercoeff(GEN x, long n)
{
  long i = n - valp(x);
  return (i < 0)? gzero: (GEN)x[i+2];
}

typedef struct {
  GEN c1, *aij, *bij, *powracpi, *cS, *cT;
  long i0, a,b,c, r, rc1, rc2;
} ST_t;

/* compute the principal part at the integers s = 0, -1, -2, ..., -i0
   of Gamma((s+1)/2)^a Gamma(s/2)^b Gamma(s)^c / (s - z) with z = 0 and 1 */
/* NOTE: this is surely not the best way to do this, but it's fast enough! */
static void
ppgamma(ST_t *T, long prec)
{
  GEN eul, gam,gamun,gamdm, an,bn,cn_evn,cn_odd, x,x2,X,Y, cf, sqpi;
  GEN p1, p2, *aij, *bij;
  long a = T->a;
  long b = T->b;
  long c = T->c, r = T->r, i0 = T->i0;
  long i,j, s,t;
  ulong av;

  aij = (GEN*)cgetg(i0+1, t_VEC);
  bij = (GEN*)cgetg(i0+1, t_VEC);
  for (i = 1; i <= i0; i++)
  {
    aij[i] = p1 = cgetg(r+1, t_VEC);
    bij[i] = p2 = cgetg(r+1, t_VEC);
    for (j=1; j<=r; j++) { p1[j] = lgetr(prec); p2[j] = lgetr(prec); }
  }
  av = avma;

  x   = polx[0];
  x2  = gmul2n(x, -1); /* x/2 */
  eul = mpeuler(prec);
  sqpi= mpsqrt(mppi(prec)); /* Gamma(1/2) */

  /* expansion of log(Gamma(u)) at u = 1 */
  gamun = cgetg(r+3, t_SER);
  gamun[1] = evalsigne(1) | evalvalp(0) | evalvarn(0);
  gamun[2] = zero;
  gamun[3] = lneg(eul);
  for (i = 2; i <= r; i++)
  {
    p1 = gdivgs(gzeta(stoi(i),prec), i);
    if (odd(i)) p1 = gneg(p1);
    gamun[i+2] = (long)p1;
  }
  gamun = gexp(gamun, prec); /* Gamma(1 + x) */
  gam = gdiv(gamun,x); /* Gamma(x) */

  /* expansion of log(Gamma(u) / Gamma(1/2)) at u = 1/2 */
  gamdm = cgetg(r+3, t_SER);
  gamdm[1] = evalsigne(1) | evalvalp(0) | evalvarn(0);
  gamdm[2] = zero;
  gamdm[3] = lneg(gadd(gmul2n(mplog2(prec), 1), eul));
  for (i = 2; i <= r; i++)
    gamdm[i+2] = lmul((GEN)gamun[i+2], subis(shifti(gun,i), 1));
  gamdm = gmul(sqpi, gexp(gamdm, prec)); /* Gamma(1/2 + x) */

 /* We simplify to get one of the following two expressions
  * if (b > a) : sqrt{Pi}^a 2^{a-au} Gamma(u)^{a+c} Gamma(  u/2  )^{|b-a|}
  * if (b <= a): sqrt{Pi}^b 2^{b-bu} Gamma(u)^{b+c) Gamma((u+1)/2)^{|b-a|} */
  if (b > a)
  {
    t = a; s = b; X = x2; Y = gsub(x2,ghalf);
    p1 = gsubst(gam,0,x2);
    p2 = gdiv(gsubst(gamdm,0,x2), Y); /* Gamma((x-1)/2) */
  }
  else
  {
    t = b; s = a; X = gadd(x2,ghalf); Y = x2; 
    p1 = gsubst(gamdm,0,x2);
    p2 = gsubst(gam,0,x2);
  }
  cf = gpowgs(sqpi, t);
  an = gpowgs(gpow(gdeux, gsubsg(1,x), prec), t); /* 2^{t-tx} */
  bn = gpowgs(gam, t+c); /* Gamma(x)^{t+c} */
  cn_evn = gpowgs(p1, s-t); /* Gamma(X)^{s-t} */
  cn_odd = gpowgs(p2, s-t); /* Gamma(Y)^{s-t} */
  for (i = 0; i < i0/2; i++)
  {
    GEN C1,q1, A1 = aij[2*i+1], B1 = bij[2*i+1]; 
    GEN C2,q2, A2 = aij[2*i+2], B2 = bij[2*i+2];

    C1 = gmul(cf, gmul(bn, gmul(an, cn_evn)));
    p1 = gdiv(C1, gsubgs(x, 2*i));  
    q1 = gdiv(C1, gsubgs(x, 2*i+1));

    /* an(x-u-1) = 2^t an(x-u) */
    an = gmul2n(an, t);
    /* bn(x-u-1) = bn(x-u) / (x-u-1)^{t+c} */
    bn = gdiv(bn, gpowgs(gsubgs(x, 2*i+1), t+c));

    C2 = gmul(cf, gmul(bn, gmul(an, cn_odd)));
    p2 = gdiv(C2, gsubgs(x, 2*i+1));
    q2 = gdiv(C2, gsubgs(x, 2*i+2));
    for (j = 1; j <= r; j++)         
    {
      gaffect(_sercoeff(p1, -j), (GEN)A1[j]);
      gaffect(_sercoeff(q1, -j), (GEN)B1[j]);
      gaffect(_sercoeff(p2, -j), (GEN)A2[j]);
      gaffect(_sercoeff(q2, -j), (GEN)B2[j]);
    }

    an = gmul2n(an, t);
    bn = gdiv(bn, gpowgs(gsubgs(x, 2*i+2), t+c));
    /* cn_evn(x-2i-2) = cn_evn(x-2i)  / (X - (i+1))^{s-t} */
    /* cn_odd(x-2i-3) = cn_odd(x-2i-1)/ (Y - (i+1))^{s-t} */
    cn_evn = gdiv(cn_evn, gpowgs(gsubgs(X,i+1), s-t));
    cn_odd = gdiv(cn_odd, gpowgs(gsubgs(Y,i+1), s-t));
  }
  T->aij = aij;
  T->bij = bij; avma = av;
}

static GEN
_cond(GEN dtcr, int quad)
{
  GEN cond;
  if (quad) cond = (GEN)dtcr[7];
  else
  {
    cond = cgetg(3, t_VEC);
    cond[1] = dtcr[7];
    cond[2] = dtcr[9];
  }
  return cond;
}

/* sort chars according to conductor */
static GEN
sortChars(GEN dataCR, int quad)
{
  const long cl = lg(dataCR) - 1;
  GEN vCond  = cgetg(cl+1, t_VEC);
  GEN CC     = cgetg(cl+1, t_VECSMALL);
  GEN nvCond = cgetg(cl+1, t_VECSMALL);
  long j,k, ncond;
  GEN vChar;

  for (j = 1; j <= cl; j++) nvCond[j] = 0;

  ncond = 0;
  for (j = 1; j <= cl; j++)
  {
    GEN cond = _cond((GEN)dataCR[j], quad);
    for (k = 1; k <= ncond; k++)
      if (gegal(cond, (GEN)vCond[k])) break;
    if (k > ncond) vCond[++ncond] = (long)cond;
    nvCond[k]++; CC[j] = k; /* char j has conductor number k */
  }
  vChar = cgetg(ncond+1, t_VEC);
  for (k = 1; k <= ncond; k++)
  {
    vChar[k] = lgetg(nvCond[k]+1, t_VECSMALL);
    nvCond[k] = 0;
  }
  for (j = 1; j <= cl; j++)
  {
    k = CC[j]; nvCond[k]++;
    mael(vChar,k,nvCond[k]) = j;
  }
  return vChar;
}

static void
get_cS_cT(ST_t *T, long n)
{
  ulong av;
  GEN csurn, nsurc, lncsurn;
  GEN A,B,s,t,Z,*aij,*bij;
  long i,j,r,i0;

  if (T->cS[n]) return;

  av = avma;
  aij = T->aij; i0= T->i0;
  bij = T->bij; r = T->r;
  Z = cgetg(r+1, t_VEC);
  Z[1] = un;

  csurn = gdivgs(T->c1, n);
  nsurc = ginv(csurn);
  lncsurn = mplog(csurn);

  Z[2] = (long)lncsurn; /* r >= 2 */
  for (i = 3; i <= r; i++)
  {
    s = gmul((GEN)Z[i-1], lncsurn);
    Z[i] = ldivgs(s, i-1); /* Z[i] = ln^(i-1)(c1/n) / (i-1)! */
  }

  /* i = i0 */
    A = aij[i0]; t = (GEN)A[1];
    B = bij[i0]; s = (GEN)B[1];
    for (j = 2; j <= r; j++)
    {
      s = gadd(s, gmul((GEN)Z[j], (GEN)B[j]));
      t = gadd(t, gmul((GEN)Z[j], (GEN)A[j]));
    }
  for (i = i0 - 1; i > 1; i--)
  {
    A = aij[i]; t = gmul(t, nsurc);
    B = bij[i]; s = gmul(s, nsurc); 
    for (j = odd(i)? T->rc2: T->rc1; j; j--)
    {
      s = gadd(s, gmul((GEN)Z[j], (GEN)B[j]));
      t = gadd(t, gmul((GEN)Z[j], (GEN)A[j]));
    }
  }
  /* i = 1 */
    A = aij[1]; t = gmul(t, nsurc);
    B = bij[1]; s = gmul(s, nsurc);
    for (j = 1; j <= r; j++)
    {
      s = gadd(s, gmul((GEN)Z[j], (GEN)B[j]));
      t = gadd(t, gmul((GEN)Z[j], (GEN)A[j]));
    }
  s = gadd(s, gmul(csurn, T->powracpi[T->b]));
  T->cS[n] = gclone(s);
  T->cT[n] = gclone(t); avma = av;
}

static void
clear_cScT(ST_t *T, long N)
{
  GEN *cS = T->cS, *cT = T->cT;
  long i;
  for (i=1; i<=N; i++)
    if (cS[i]) { gunclone(cS[i]); gunclone(cT[i]); cS[i] = cT[i] = NULL; }
}

static void
init_cScT(ST_t *T, GEN CHI, long N, long prec)
{
  GEN p1 = (GEN)CHI[9];
  T->a = p1[1];
  T->b = p1[2];
  T->c = p1[3];
  T->rc1 = T->a + T->c;
  T->rc2 = T->b + T->c;
  T->r   = max(T->rc2+1, T->rc1); /* >= 2 */
  ppgamma(T, prec);
  clear_cScT(T, N);
}

static GEN
GetST(GEN dataCR, long prec)
{
  const long cl = lg(dataCR) - 1;
  ulong av, av1, av2;
  long ncond, n, j, k, jc, nmax, prec2, i0, r1, r2;
  GEN bnr, nf, racpi, *powracpi;
  GEN rep, vChar, N0, C, T, S, an, degs;
  LISTray LIST;
  ST_t cScT;

  if (DEBUGLEVEL) timer2();
  /* allocate memory for answer */
  rep = cgetg(3, t_VEC);
  S = cgetg(cl+1, t_VEC); rep[1] = (long)S;
  T = cgetg(cl+1, t_VEC); rep[2] = (long)T;
  for (j = 1; j <= cl; j++)
  {
    S[j] = (long)cgetc(prec);
    T[j] = (long)cgetc(prec);
  }
  av = avma;

  /* initializations */
  degs = GetDeg(dataCR);
  vChar= sortChars(dataCR,0); ncond = lg(vChar)-1;

  bnr = gmael(dataCR,1,4);
  nf  = checknf(bnr); nf_get_sign(nf,&r1,&r2);
 
  C  = cgetg(ncond+1, t_VEC);
  N0 = cgetg(ncond+1, t_VECSMALL);
  nmax = 0;
  for (j = 1; j <= ncond; j++)
  {
    C[j]  = mael(dataCR, mael(vChar,j,1), 2);
    N0[j] = GetBoundN0((GEN)C[j], r1, r2, prec);
    if (nmax < N0[j]) nmax  = N0[j];
  }
  if ((ulong)nmax > maxprime())
    err(talker, "Not enough precomputed primes (need all p <= %ld)", nmax);
  i0 = GetBoundi0(r1, r2, prec);

  if (DEBUGLEVEL>1) fprintferr("nmax = %ld, i0 = %ld\n", nmax, i0);
  InitPrimes(gmael(dataCR,1,4), nmax, &LIST);

  prec2 = ((prec-2) << 1) + EXTRA_PREC;
  racpi = mpsqrt(mppi(prec2));
  powracpi = (GEN*)cgetg(r1+2,t_VEC);
  powracpi++; powracpi[0] = gun; powracpi[1] = racpi;
  for (j=2; j<=r1; j++) powracpi[j] = mulrr(powracpi[j-1], racpi);
  cScT.powracpi = powracpi;

  cScT.cS = (GEN*)cgetg(nmax+1, t_VEC);
  cScT.cT = (GEN*)cgetg(nmax+1, t_VEC);
  for (j=1; j<=nmax; j++) cScT.cS[j] = cScT.cT[j] = NULL;

  cScT.i0 = i0;
 
  av1 = avma;
  for (jc = 1; jc <= ncond; jc++)
  {
    const GEN LChar = (GEN)vChar[jc];
    const long nChar = lg(LChar)-1, NN = N0[jc];

    if (DEBUGLEVEL>1)
      fprintferr("* conductor no %ld/%ld (N = %ld)\n\tInit: ", jc,ncond,NN);

    cScT.c1 = (GEN)C[jc];
    init_cScT(&cScT, (GEN)dataCR[LChar[1]], NN, prec2);
    av2 = avma;
    for (k = 1; k <= nChar; k++)
    {
      const long t = LChar[k], d = degs[t];
      const GEN z = gmael3(dataCR, t, 5, 2);
      GEN p1 = gzero, p2 = gzero;
      long c = 0;
      int **matan;
      
      if (DEBUGLEVEL>1)
        fprintferr("\tcharacter no: %ld (%ld/%ld)\n", t,k,nChar);
      matan = ComputeCoeff((GEN)dataCR[t], &LIST, NN, d);
      for (n = 1; n <= NN; n++)
        if ((an = EvalCoeff(z, matan[n], d)))
        {
          get_cS_cT(&cScT, n);
          p1 = gadd(p1, gmul(an,        cScT.cS[n]));
          p2 = gadd(p2, gmul(gconj(an), cScT.cT[n]));
          if (++c == 256)
          { GEN *gptr[2]; gptr[0]=&p1; gptr[1]=&p2;
            gerepilemany(av2,gptr,2); c = 0;
          }
        }
      gaffect(p1, (GEN)S[t]);
      gaffect(p2, (GEN)T[t]);
      FreeMat(matan, NN); avma = av2;
    }
    if (DEBUGLEVEL>1) fprintferr("\n");
    avma = av1;
  }
  if (DEBUGLEVEL) msgtimer("S&T");
  clear_cScT(&cScT, nmax);
  avma = av; return rep;
}

/* Given dtcr, S(chi) and T(chi), return L(1, chi) if fl = 1,
   or [r(chi), c(chi)] where r(chi) is the rank of chi and c(chi)
   is given by L(s, chi) = c(chi).s^r(chi) at s = 0 if fl = 0.
   if fl2 = 1, adjust the value to get L_S(s, chi). */
static GEN
GetValue(GEN dtcr, GEN S, GEN T, long fl, long fl2, long prec)
{
  ulong av = avma;
  GEN W, A, cf, VL, rep, racpi, p1;
  long q, b, c;
  int isreal;

  racpi = mpsqrt(mppi(prec));
  W = ComputeArtinNumber(dtcr, 0, prec);

  isreal = (itos(gmael(dtcr, 8, 3)) <= 2);

  p1 = (GEN)dtcr[9];
  q = p1[1];
  b = p1[2];
  c = p1[3];

  if (!fl)
  { /* VL = (W(chi).S(conj(chi)) + T(chi)) / (sqrt(Pi)^q 2^{r1 - q}) */
    GEN rchi = stoi(b + c);
    cf = gmul2n(gpowgs(racpi, q), b);

    VL = gadd(gmul(W, gconj(S)), gconj(T));
    if (isreal) VL = greal(VL);
    VL = gdiv(VL, cf);

    if (fl2)
    {
      A = ComputeAChi(dtcr, fl, prec);
      VL = gmul((GEN)A[2], VL);
      rchi = gadd(rchi, (GEN)A[1]);
    }

    rep = cgetg(3, t_VEC);
    rep[1] = (long)rchi;
    rep[2] = (long)VL;
  }
  else
  { /* VL = S(chi) + W(chi).T(chi)) / (C(chi) sqrt(Pi)^{r1 - q}) */
    cf = gmul((GEN)dtcr[2], gpowgs(racpi, b));

    rep = gadd(S, gmul(W, T));
    if (isreal) rep = greal(rep);
    rep = gdiv(rep, cf);

    if (fl2)
    {
      A = ComputeAChi(dtcr, fl, prec);
      rep = gmul(A, rep);
    }
  }

  return gerepilecopy(av, rep);
}

/* return the order and the first non-zero term of L(s, chi0)
   at s = 0. If flag = 1, adjust the value to get L_S(s, chi0). */
static GEN
GetValue1(GEN bnr, long flag, long prec)
{
  GEN bnf = checkbnf(bnr), nf = checknf(bnf);
  GEN hk, Rk, wk, c, rep, mod0, diff;
  long i, l, r, r1, r2, av = avma;

  r1 = nf_get_r1(nf);
  r2 = nf_get_r2(nf);
  hk = gmael3(bnf, 8, 1, 1);
  Rk = gmael(bnf, 8, 2);
  wk = gmael3(bnf, 8, 4, 1);

  c = gneg_i(gdiv(gmul(hk, Rk), wk));
  r = r1 + r2 - 1;

  if (flag)
  {
    mod0 = gmael3(bnr, 2, 1, 1);
    diff = (GEN)idealfactor(nf, mod0)[1];

    l = lg(diff) - 1; r += l;
    for (i = 1; i <= l; i++)
      c = gmul(c, glog(idealnorm(nf, (GEN)diff[i]), prec));
  }

  rep = cgetg(3, t_VEC);
  rep[1] = lstoi(r);
  rep[2] = (long)c;

  return gerepilecopy(av, rep);
}

/********************************************************************/
/*                6th part: recover the coefficients                */
/********************************************************************/
static long
TestOne(GEN plg, RC_data *d)
{
  long j, v = d->v;
  GEN p1;

  p1 = gsub(d->beta, (GEN)plg[v]);
  if (expo(p1) >= d->G) return 0;

  for (j = 1; j <= d->N; j++)
    if (j != v)
    {
      p1 = gabs((GEN)plg[j], DEFAULTPREC);
      if (gcmp(p1, d->B) > 0) return 0;
    }
  return 1;
}

static GEN
chk_reccoeff_init(FP_chk_fun *chk, GEN nf, GEN gram, GEN mat, long *ptprec)
{
  RC_data *d = (RC_data*)chk->data;
  d->U = mat; return d->nB;
}

static GEN
chk_reccoeff(void *data, GEN x)
{
  RC_data *d = (RC_data*)data;
  long N = d->N, j;
  GEN p1 = gmul(d->U, x), sol, plg;

  if (!gcmp1((GEN)p1[1])) return NULL;

  sol = cgetg(N + 1, t_COL);
  for (j = 1; j <= N; j++)
    sol[j] = lmulii((GEN)p1[1], (GEN)p1[j + 1]);
  plg = gmul(d->M, sol);

  if (TestOne(plg, d)) return sol;
  return NULL;
}

static GEN
chk_reccoeff_post(void *data /* unused */, GEN res)
{
  return res;
}

/* Using Cohen's method */
static GEN
RecCoeff3(GEN nf, RC_data *d, long prec)
{
  GEN A, M, nB, cand, p1, B2, C2, tB, beta2, eps, nf2, Bd;
  GEN beta = d->beta, B = d->B;
  long N = d->N, v = d->v;
  long i, j, k, l, ct = 0, av = avma, prec2;
  FP_chk_fun *chk;

  d->G = min(-10, -bit_accuracy(prec) >> 4);
  eps = gpowgs(stoi(10), min(-8, (d->G >> 1)));
  tB  = gpow(gmul2n(eps, N), gdivgs(gun, 1-N), DEFAULTPREC);

  Bd    = gmin(B, tB);
  p1    = gceil(gdiv(glog(Bd, DEFAULTPREC), dbltor(2.3026)));
  prec2 = max((prec << 1) - 2, (long)(itos(p1) * pariK1 + BIGDEFAULTPREC));
  nf2   = nfnewprec(nf, prec2);
  beta2 = gprec_w(beta, prec2);

 LABrcf: ct++;
  B2 = sqri(Bd);
  C2 = gdiv(B2, gsqr(eps));

  M = gmael(nf2, 5, 1);
  d->M = M;

  A = cgetg(N+2, t_MAT);
  for (i = 1; i <= N+1; i++)
    A[i] = lgetg(N+2, t_COL);

  coeff(A, 1, 1) = ladd(gmul(C2, gsqr(beta2)), B2);
  for (j = 2; j <= N+1; j++)
  {
    p1 = gmul(C2, gmul(gneg_i(beta2), gcoeff(M, v, j-1)));
    coeff(A, 1, j) = coeff(A, j, 1) = (long)p1;
  }
  for (i = 2; i <= N+1; i++)
    for (j = 2; j <= N+1; j++)
    {
      p1 = gzero;
      for (k = 1; k <= N; k++)
      {
        GEN p2 = gmul(gcoeff(M, k, j-1), gcoeff(M, k, i-1));
        if (k == v) p2 = gmul(C2, p2);
        p1 = gadd(p1,p2);
      }
      coeff(A, i, j) = coeff(A, j, i) = (long)p1;
    }

  nB = mulsi(N+1, B2);
  d->nB = nB;

  chk = (FP_chk_fun*)new_chunk(sizeof(FP_chk_fun));
  chk->f         = &chk_reccoeff;
  chk->f_init    = &chk_reccoeff_init;
  chk->f_post    = &chk_reccoeff_post;
  chk->data      = (void*)d;
  chk->skipfirst = 0;

  cand = fincke_pohst(A, nB, 20000, 3, prec2, chk);

  if (!cand)
  {
    if (ct > 3) { avma = av; return NULL; }

    prec2 = (prec2 << 1) - 2;
    if (DEBUGLEVEL >= 2) err(warnprec,"RecCoeff", prec2);
    nf2 = nfnewprec(nf2, prec2);
    beta2 = gprec_w(beta2, prec2);
    goto LABrcf;
  }

  cand = (GEN)cand[1];
  l = lg(cand) - 1;

  if (l == 1) return gerepileupto(av, basistoalg(nf, (GEN)cand[1]));

  if (DEBUGLEVEL >= 2)
    fprintferr("RecCoeff3: no solution found!\n");

  avma = av; return NULL;
}

/* Using linear dependance relations */
static GEN
RecCoeff2(GEN nf,  RC_data *d,  long prec)
{
  long i, bacmin, bacmax, av = avma, av2;
  GEN vec, velt, p1, cand, M, plg, pol, cand2;
  GEN beta = d->beta;

  d->G = min(-20, -bit_accuracy(prec) >> 4);
  M    = gmael(nf, 5, 1);
  pol  = (GEN)nf[1];
  vec  = gtrans((GEN)gtrans(M)[d->v]);
  velt = (GEN)nf[7];

  p1 = cgetg(2, t_VEC);
  p1[1] = lneg(beta);
  vec = concat(p1, vec);

  p1[1] = zero;
  velt = concat(p1, velt);

  bacmin = (long)(.225 * bit_accuracy(prec));
  bacmax = (long)(.315 * bit_accuracy(prec));

  av2 = avma;

  for (i = bacmax; i >= bacmin; i-=16)
  {
    p1 = lindep2(vec, i);

    if (signe((GEN)p1[1]))
    {
      p1    = ground(gdiv(p1, (GEN)p1[1]));
      cand  = gmodulcp(gmul(velt, gtrans(p1)), pol);
      cand2 = algtobasis(nf, cand);
      plg   = gmul(M, cand2);

      if (TestOne(plg, d)) return gerepilecopy(av, cand);
    }
    avma = av2;
  }
  /* failure */
  return RecCoeff3(nf,d,prec);
}

/* Attempts to find a polynomial with coefficients in nf such that
   its coefficients are close to those of pol at the place v and
   less than B at all the other places */
GEN
RecCoeff(GEN nf,  GEN pol,  long v, long prec)
{
  long av = avma, j, md, G, cl = degpol(pol);
  GEN p1, beta;
  RC_data d;

  /* if precision(pol) is too low, abort */
  for (j = 2; j <= cl+1; j++)
  {
    p1 = (GEN)pol[j];
    G  = bit_accuracy(gprecision(p1)) - gexpo(p1);
    if (G < 34) { avma = av; return NULL; }
  }

  md = cl/2;
  pol = dummycopy(pol);

  d.N = degpol(nf[1]);
  d.v = v;

  for (j = 1; j <= cl; j++)
  { /* start with the coefficients in the middle,
       since they are the harder to recognize! */
    long cf = md + (j%2? j/2: -j/2);
    GEN bound = binome(stoi(cl), cf);

    bound = shifti(bound, cl - cf);

    if (DEBUGLEVEL > 1)
      fprintferr("In RecCoeff with cf = %ld and B = %Z\n", cf, bound);

    beta = greal((GEN)pol[cf+2]);
    d.beta = beta;
    d.B    = bound;
    if (! (p1 = RecCoeff2(nf, &d, prec)) ) return NULL;
    pol[cf+2] = (long)p1;
  }
  pol[cl+2] = un;
  return gerepilecopy(av, pol);
}

/*******************************************************************/
/*                                                                 */
/*                   Computation of class fields of                */
/*	          real quadratic fields using Stark units          */
/*                                                                 */
/*******************************************************************/

/* an[q * i] *= chi for all (i,p)=1 */
static void
an_mul(int **an, long p, long q, long n, long deg, GEN chi, int **reduc)
{
  ulong av;
  long c,i;
  int *T;

  if (gcmp1(chi)) return;
  av = avma;
  T = (int*)new_chunk(deg); Polmod2Coeff(T,chi, deg);
  for (c = 1, i = q; i <= n; i += q, c++)
    if (c == p) c = 0; else MulCoeff(an[i], T, reduc, deg);
  avma = av;
}
/* an[q * i] = 0 for all (i,p)=1 */
static void
an_set0_coprime(int **an, long p, long q, long n, long deg)
{
  long c,i;
  for (c = 1, i = q; i <= n; i += q, c++)
    if (c == p) c = 0; else _0toCoeff(an[i], deg);
}
/* an[q * i] = 0 for all i */
static void
an_set0(int **an, long p, long n, long deg)
{
  long i;
  for (i = p; i <= n; i += p) _0toCoeff(an[i], deg);
}

/* compute the coefficients an for the quadratic case */
static int**
computean(GEN dtcr, LISTray *R, long n, long deg)
{
  ulong av = avma, av2;
  long i, p, q, condZ, l;
  int **an, **reduc;
  GEN L, CHI, chi, chi1, ray;
  CHI_t C;

  CHI = (GEN)dtcr[5]; init_CHI_alg(&C, CHI);
  condZ= R->condZ;

  an = InitMatAn(n, deg, 1);
  reduc = InitReduction(CHI, deg);
  av2 = avma;

  /* all pr | p divide cond */
  L = R->L0; l = lg(L);
  for (i=1; i<l; i++) an_set0(an,L[i],n,deg);

  /* 1 prime of degree 2 */
  L = R->L2; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    p = L[i];
    ray = R->rayZ[p % condZ];
    chi  = EvalChar(&C, ray);
    chi1 = chi;
    for (q=p;;)
    {
      an_set0_coprime(an, p,q,n,deg); /* v_p(q) odd */
      if (! (q = next_pow(q,p, n)) ) break;

      an_mul(an,p,q,n,deg,chi,reduc);
      if (! (q = next_pow(q,p, n)) ) break;
      chi = gmul(chi, chi1);
    }
  }
    
  /* 1 prime of degree 1 */
  L = R->L1; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    p = L[i]; ray = R->L1ray[i];
    chi  = EvalChar(&C, ray);
    chi1 = chi;
    for(q=p;;)
    {
      an_mul(an,p,q,n,deg,chi,reduc);
      if (! (q = next_pow(q,p, n)) ) break;
      chi = gmul(chi, chi1);
    }
  }

  /* 2 primes of degree 1 */
  L = R->L11; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    GEN ray1, ray2, chi11, chi12, chi2;

    p = L[i]; ray1 = R->L11ray[i]; /* use pr1 pr2 = (p) */
    ray2 = gsub(R->rayZ[p % condZ],  ray1);
    chi11 = EvalChar(&C, ray1);
    chi12 = EvalChar(&C, ray2);

    chi1 = gadd(chi11, chi12);
    chi2 = chi12;
    for(q=p;;)
    {
      an_mul(an,p,q,n,deg,chi1,reduc);
      if (! (q = next_pow(q,p, n)) ) break;
      chi2 = gmul(chi2, chi12);
      chi1 = gadd(chi2, gmul(chi1, chi11));
    }
  }

  CorrectCoeff(dtcr, an, reduc, n, deg);
  FreeMat(reduc, deg-1);
  avma = av; return an;
}

/* compute S and T for the quadratic case */
static GEN
QuadGetST(GEN dataCR, long prec)
{
  const long cl  = lg(dataCR) - 1;
  ulong av, av1, av2;
  long ncond, n, j, k, nmax;
  GEN rep, vChar, N0, C, T, S, cf, cfh, an, degs;
  LISTray LIST;

  /* allocate memory for answer */
  rep = cgetg(3, t_VEC);
  S = cgetg(cl+1, t_VEC); rep[1] = (long)S;
  T = cgetg(cl+1, t_VEC); rep[2] = (long)T;
  for (j = 1; j <= cl; j++)
  {
    S[j] = (long)cgetc(prec);
    T[j] = (long)cgetc(prec);
  }
  av = avma;

  /* initializations */
  degs = GetDeg(dataCR);
  vChar= sortChars(dataCR,1); ncond = lg(vChar)-1;
  C    = cgetg(ncond+1, t_VEC);
  N0   = cgetg(ncond+1, t_VECSMALL);
  nmax = 0;
  for (j = 1; j <= ncond; j++)
  {
    C[j]  = mael(dataCR, mael(vChar,j,1), 2);
    N0[j] = (long)(bit_accuracy(prec) * gtodouble((GEN)C[j]) * 0.35);
    if (nmax < N0[j]) nmax = N0[j];
  }
  if ((ulong)nmax > maxprime())
    err(talker, "Not enough precomputed primes (need all p <= %ld)", nmax);
  if (DEBUGLEVEL>1) fprintferr("nmax = %ld\n", nmax);
  InitPrimesQuad(gmael(dataCR,1,4), nmax, &LIST);

  cf  = gmul2n(mpsqrt(mppi(prec)), 1);
  cfh = gmul2n(cf, -1);

  av1 = avma;
  /* loop over conductors */
  for (j = 1; j <= ncond; j++)
  {
    const GEN c1 = (GEN)C[j], c2 = divsr(2,c1), cexp = mpexp(gneg(c2));
    const GEN LChar = (GEN)vChar[j];
    const long nChar = lg(LChar)-1, NN = N0[j];
    GEN veint1, vcn = cgetg(NN+1, t_VEC);

    if (DEBUGLEVEL>1)
      fprintferr("* conductor no %ld/%ld (N = %ld)\n\tInit: ", j,ncond,NN);
    veint1 = veceint1(c2, stoi(NN), prec);
    vcn[1] = (long)cexp;
    for (n=2; n<=NN; n++) vcn[n] = lmulrr((GEN)vcn[n-1], cexp);
    av2 = avma;
    for (n=2; n<=NN; n++, avma = av2)
      affrr(divrs((GEN)vcn[n],n), (GEN)vcn[n]);

    for (k = 1; k <= nChar; k++)
    {
      const long t = LChar[k], d = degs[t];
      const GEN z = gmael3(dataCR, t, 5, 2);
      GEN p1 = gzero, p2 = gzero;
      int **matan;
      long c = 0;

      if (DEBUGLEVEL>1)
        fprintferr("\tcharacter no: %ld (%ld/%ld)\n", t,k,nChar);
      matan = computean((GEN)dataCR[t], &LIST, NN, d);
      for (n = 1; n <= NN; n++)
	if ((an = EvalCoeff(z, matan[n], d)))
        {
          p1 = gadd(p1, gmul(an, (GEN)vcn[n]));
	  p2 = gadd(p2, gmul(an, (GEN)veint1[n]));
          if (++c == 256)
          { GEN *gptr[2]; gptr[0]=&p1; gptr[1]=&p2;
            gerepilemany(av2,gptr,2); c = 0;
          }
        }
      gaffect(gmul(cfh, gmul(p1,c1)), (GEN)S[t]);
      gaffect(gmul(cf,  gconj(p2)),   (GEN)T[t]);
      FreeMat(matan,NN); avma = av2;
    }
    if (DEBUGLEVEL>1) fprintferr("\n");
    avma = av1;
  }
  if (DEBUGLEVEL) msgtimer("S & T");
  avma = av; return rep;
}

typedef struct {
  long cl;
  GEN dkpow;
} DH_t;

/* return 1 if the absolute polynomial pol (over Q) defines the
   Hilbert class field of the real quadratic field bnf */
static int
define_hilbert(void *S, GEN pol)
{
  DH_t *T = (DH_t*)S;
  return (degpol(pol) == T->cl
      && (T->cl & 1 || !egalii(discf(pol), T->dkpow)));
}

/* let polrel define Hk/k,  find L/Q such that Hk=Lk and L and k are
   disjoint */
static GEN
makescind(GEN bnf, GEN polabs, long cl, long prec)
{
  long av = avma, i, l;
  GEN pol, p1, nf2, dabs, dk, bas;
  DH_t T;

  /* check the result (a little): signature and discriminant */
  bas = allbase4(polabs,0,&dabs,NULL);
  dk  = gmael(bnf,7,3);
  if (!egalii(dabs, gpowgs(dk,cl)) || sturm(polabs) != 2*cl)
    err(bugparier, "quadhilbert");

  /* attempt to find the subfields using polred */
  p1 = cgetg(3,t_VEC); p1[1]=(long)polabs; p1[2]=(long)bas;
  T.cl = cl;
  T.dkpow = (cl & 1) ? NULL: gpowgs(dk, cl>>1);
  pol = polredfirstpol(p1, (prec<<1) - 2, &define_hilbert, &T);
  if (DEBUGLEVEL) msgtimer("polred");

  if (!pol)
  {
    nf2 = nfinit0(polabs, 1, prec);
    p1  = subfields(nf2, stoi(cl));
    l = lg(p1);
    if (DEBUGLEVEL) msgtimer("subfields");

    for (i = 1; i < l; i++)
    {
      pol = gmael(p1, i, 1);
      if (cl & 1 || !egalii(sqri(discf(pol)), (GEN)nf2[3])) break;
    }
    if (i == l)
      for (i = 1; i < l; i++)
      {
        pol = gmael(p1, i, 1);
        if (degpol(gcoeff(nffactor(bnf, pol), 1, 1)) == cl) break;
      }
    if (i == l)
      err(bugparier, "makescind (no polynomial found)");
  }
  pol = polredabs(pol, prec);
  return gerepileupto(av, pol);
}

/* compute the Hilbert class field using genus class field theory when
   the exponent of the class group is 2 */
static GEN
GenusField(GEN bnf, long prec)
{
  long hk, c, l, av = avma;
  GEN disc, x2, pol, div, d;

  hk   = itos(gmael3(bnf, 8, 1, 1));
  disc = gmael(bnf, 7, 3);
  x2   = gsqr(polx[0]);

  if (mod4(disc) == 0) disc = divis(disc, 4);
  div = divisors(disc);
  l = 0;
  pol = NULL;

  for (c = 2; l < hk; c++) /* skip c = 1 : div[1] = gun */
  {
    d = (GEN)div[c];
    if (mod4(d) == 1)
    {
      GEN t = gsub(x2, d); 
      if (!pol)
	pol = t;
      else
	pol = (GEN)compositum(pol, t)[1];

      l = degpol(pol);
    }
  }

  return gerepileupto(av, polredabs(pol, prec));
}

/* if flag = 0 returns the reduced polynomial,  flag = 1 returns the
   non-reduced polynomial,  flag = 2 returns an absolute reduced
   polynomial,  flag = 3 returns the polynomial of the Stark's unit,
   flag = -1 computes a fast and crude approximation of the result */
static GEN
AllStark(GEN data,  GEN nf,  long flag,  long newprec)
{
  long cl, i, j, cpt = 0, av, av2, N, h, v, n, bnd = 300, sq = 1, r1, r2;
  int **matan;
  GEN p0, p1, p2, S, T, polrelnum, polrel, Lp, W, A, veczeta, sig;
  GEN degs, ro, C, Cmax, dataCR, cond1, L1, *gptr[2], an, Pi;
  LISTray LIST;

  N     = degpol(nf[1]);
  r1    = nf_get_r1(nf);
  r2    = (N - r1)>>1;
  cond1 = gmael4(data, 1, 2, 1, 2);
  Pi    = mppi(newprec);
  dataCR = (GEN)data[5];

  v = 1;
  while(gcmp1((GEN)cond1[v])) v++;

  cl = lg(dataCR)-1;
  degs = GetDeg(dataCR);
  h  = itos(gmul2n(det((GEN)data[2]), -1));

LABDOUB:

  av = avma;

  if (flag >= 0)
  {
    if (N == 2) /* compute S,T differently if nf is quadratic */
      p1 = QuadGetST(dataCR, newprec);
    else
      p1 = GetST(dataCR, newprec);

    S = (GEN)p1[1];
    T = (GEN)p1[2];

    Lp = cgetg(cl + 1, t_VEC);
    for (i = 1; i <= cl; i++)
      Lp[i] = GetValue((GEN)dataCR[i], (GEN)S[i], (GEN)T[i], 0, 1, newprec)[2];

    if (DEBUGLEVEL) msgtimer("Compute W");
  }
  else
  { /* compute a crude approximation of the result */
    C = cgetg(cl + 1, t_VEC);
    for (i = 1; i <= cl; i++) C[i] = mael(dataCR, i, 2);
    Cmax = vecmax(C);

    n = GetBoundN0(Cmax, r1, r2, newprec);
    if (n > bnd) n = bnd;
    if (DEBUGLEVEL) fprintferr("nmax in QuickPol: %ld \n", n);
    InitPrimes(gmael(dataCR,1,4), n, &LIST);

    p0 = cgetg(3, t_COMPLEX);
    p0[1] = lgetr(newprec); affsr(0, (GEN)p0[1]);
    p0[2] = lgetr(newprec); affsr(0, (GEN)p0[2]);

    L1 = cgetg(cl+1, t_VEC);
    /* we use the formulae L(1) = sum (an / n) */
    for (i = 1; i <= cl; i++)
    {
      matan = ComputeCoeff((GEN)dataCR[i], &LIST, n, degs[i]);
      av2 = avma;
      p1 = p0; p2 = gmael3(dataCR, i, 5, 2);
      for (j = 1; j <= n; j++)
	if ( (an = EvalCoeff(p2, matan[j], degs[i])) )
          p1 = gadd(p1, gdivgs(an, j));
      L1[i] = lpileupto(av2, p1);
      FreeMat(matan, n);
    }

    p1 = gmul2n(gpowgs(mpsqrt(Pi), N - 2), 1);

    Lp = cgetg(cl+1, t_VEC);
    for (i = 1; i <= cl; i++)
    {
      W = ComputeArtinNumber((GEN)dataCR[i], 1, newprec);
      A = (GEN)ComputeAChi((GEN)dataCR[i], 0, newprec)[2];
      W = gmul((GEN)C[i], gmul(A, W));

      Lp[i] = ldiv(gmul(W, gconj((GEN)L1[i])), p1);
    }
  }

  p1 = ComputeLift(gmael(data, 4, 2));

  veczeta = cgetg(h + 1, t_VEC);
  for (i = 1; i <= h; i++)
  {
    GEN z = gzero;

    sig = (GEN)p1[i];
    for (j = 1; j <= cl; j++)
    {
      GEN CHI = gmael(dataCR,j,5);
      GEN val = ComputeImagebyChar(CHI, sig);
      GEN p2 = greal(gmul((GEN)Lp[j], val));
      if (itos((GEN)CHI[3]) != 2) p2 = gmul2n(p2, 1); /* character not real */
      z = gadd(z, p2);
    }
    veczeta[i] = ldivgs(z, 2 * h);
  }
  if (DEBUGLEVEL >= 2) fprintferr("zetavalues = %Z\n", veczeta);

  if (flag >=0 && flag <= 3) sq = 0;

  ro = cgetg(h+1, t_VEC); /* roots */

  for (;;)
  {
    if (DEBUGLEVEL > 1 && !sq)
      fprintferr("Checking the square-root of the Stark unit...\n");

    for (j = 1; j <= h; j++)
    {
      p1 = gexp(gmul2n((GEN)veczeta[j], sq), newprec);
      ro[j] = ladd(p1, ginv(p1));
    }
    polrelnum = roots_to_pol_intern(realun(newprec),ro, 0,0);
    if (DEBUGLEVEL)
    {
      if (DEBUGLEVEL >= 2) fprintferr("polrelnum = %Z\n", polrelnum);
      msgtimer("Compute %s", (flag < 0)? "quickpol": "polrelnum");
    }

    if (flag < 0)
      return gerepilecopy(av, polrelnum);

    /* we try to recognize this polynomial */
    polrel = RecCoeff(nf, polrelnum, v, newprec);

    if (polrel || (sq++ == 1)) break;
  }

  if (!polrel) /* if it fails... */
  {
    long pr;
    if (++cpt >= 3) err(precer, "stark (computation impossible)");

    /* we compute the precision that we need */
    pr = 1 + (gexpo(polrelnum)>>TWOPOTBITS_IN_LONG);
    if (pr < 0) pr = 0;
    newprec = ADD_PREC + max(newprec,pr);

    if (DEBUGLEVEL) err(warnprec, "AllStark", newprec);

    nf = nfnewprec(nf, newprec);
    dataCR = CharNewPrec(dataCR, nf, newprec);

    gptr[0] = &dataCR;
    gptr[1] = &nf; gerepilemany(av, gptr, 2);

    goto LABDOUB;
  }

  /* and we compute the polynomial of eps if flag = 3 */
  if (flag == 3)
  {
    n  = fetch_var();
    p1 = gsub(polx[0], gadd(polx[n], ginv(polx[n])));
    polrel = polresultant0(polrel, p1, 0, 0);
    polrel = gmul(polrel, gpowgs(polx[n], h));
    polrel = gsubst(polrel, n, polx[0]);
    polrel = gmul(polrel, leading_term(polrel));
    delete_var();
  }

  if (DEBUGLEVEL >= 2) fprintferr("polrel = %Z\n", polrel);
  if (DEBUGLEVEL) msgtimer("Recpolnum");

  /* we want a reduced relative polynomial */
  if (!flag) return gerepileupto(av, rnfpolredabs(nf, polrel, 0, newprec));

  /* we just want the polynomial computed */
  if (flag!=2) return gerepilecopy(av, polrel);

  /* we want a reduced absolute polynomial */
  return gerepileupto(av, rnfpolredabs(nf, polrel, 2, newprec));
}

/********************************************************************/
/*                        Main functions                            */
/********************************************************************/

/* compute the polynomial over Q of the Hilbert class field of
   Q(sqrt(D)) where D is a positive fundamental discriminant */
GEN
quadhilbertreal(GEN D, GEN flag, long prec)
{
  VOLATILE long av = avma, cl;
  long newprec;
  VOLATILE GEN pol, bnf, bnr, dataC, bnrh, nf, exp;
  void *catcherr = NULL;

  (void)&prec; /* prevent longjmp clobbering it */
  if (DEBUGLEVEL) timer2();

  disable_dbg(0);
  /* quick computation of the class number */

  cl = itos((GEN)quadclassunit0(D, 0, NULL, prec)[1]);
  if (cl == 1)
  {
    disable_dbg(-1);
    avma = av; return polx[0];
  }

  /* initialize the polynomial defining Q(sqrt{D}) as a polynomial in y */
  pol = quadpoly(D);
  setvarn(pol, fetch_var());

 START:
  /* compute the class group */
  bnf = bnfinit0(pol, 1, NULL, prec);
  nf  = (GEN)bnf[7];
  disable_dbg(-1);

  if (DEBUGLEVEL) msgtimer("Compute Cl(k)");

  /* if the exponent of the class group is 2, use rather Genus Field Theory */
  exp = gmael4(bnf, 8, 1, 2, 1);
  if (gegal(exp, gdeux)) { delete_var(); return GenusField(bnf, prec); }

  { /* catch precision problems (precision too small) */
    jmp_buf env;
    if (setjmp(env))
    {
      prec += EXTRA_PREC;
      err (warnprec, "quadhilbertreal", prec);
      goto START;
    }
    catcherr = err_catch(precer, env, NULL);
  }

  /* find the modulus defining N */
  bnr   = buchrayinitgen(bnf, gun);
  dataC = InitQuotient(bnr, gzero);
  bnrh  = FindModulus(dataC, 1, &newprec, prec, gcmp0(flag)? 0: -10);

  if (DEBUGLEVEL) msgtimer("FindModulus");

  if (newprec > prec)
  {
    if (DEBUGLEVEL >= 2) fprintferr("new precision: %ld\n", newprec);
    nf = nfnewprec(nf, newprec);
  }

  /* use the generic function AllStark */
  pol = AllStark(bnrh, nf, 2, newprec);
  delete_var();
  err_leave(&catcherr);
  return gerepileupto(av, makescind(bnf, pol, cl, prec));
}

static GEN
get_subgroup(GEN subgp, GEN cyc)
{
  if (gcmp0(subgp)) return cyc;
  return gcmp1(denom(gauss(subgp, cyc)))? subgp: NULL;
}

GEN
bnrstark(GEN bnr,  GEN subgrp,  long flag,  long prec)
{
  long cl, N, newprec, av = avma, bnd = 0;
  GEN bnf, dataS, p1, Mcyc, nf, data;

  if (flag >= 4)
  {
    bnd = -10;
    flag -= 4;
  }

  if (flag < 0 || flag > 3) err(flagerr,"bnrstark");

  /* check the bnr */
  checkbnrgen(bnr);

  bnf  = (GEN)bnr[1];
  nf   = (GEN)bnf[7];
  Mcyc = diagonal(gmael(bnr, 5, 2));
  N    = degpol(nf[1]);
  if (N == 1)
    err(talker, "the ground field must be distinct from Q");

  /* check the bnf */
  if (!varn(nf[1]))
    err(talker, "main variable in bnrstark must not be x");

  if (nf_get_r2(nf))
    err(talker, "not a totally real ground base field in bnrstark");

  /* check the subgrp */
  if (! (subgrp = get_subgroup(subgrp,Mcyc)) )
    err(talker, "incorrect subgrp in bnrstark");

  /* compute bnr(conductor) */
  p1       = conductor(bnr, subgrp, 2);
  bnr      = (GEN)p1[2];
  subgrp = (GEN)p1[3];

  /* check the class field */
  if (nf_get_r2(checknf(bnr)))
    err(talker, "not a totally real class field in bnrstark");

  cl = itos(det(subgrp));
  if (cl == 1) return polx[0];

  timer2();

  /* find a suitable extension N */
  dataS = InitQuotient(bnr, subgrp);
  data  = FindModulus(dataS, 1, &newprec, prec, bnd);

  if (newprec > prec)
  {
    if (DEBUGLEVEL >= 2) fprintferr("new precision: %ld\n", newprec);
    nf = nfnewprec(nf, newprec);
  }

  return gerepileupto(av, AllStark(data, nf, flag, newprec));
}

/* For each character of Cl(bnr)/subgp, compute L(1, chi) (or equivalently
   the first non-zero term c(chi) of the expansion at s = 0). The binary
   digits of flag mean 1: if 0 then compute the term c(chi) and return
   [r(chi), c(chi)] where r(chi) is the order of L(s, chi) at s = 0,
   or if 1 then compute the value at s = 1 (and in this case, only for
   non-trivial characters), 2: if 0 then compute the value of the
   primitive L-function associated to chi, if 1 then compute the value
   of the L-function L_S(s, chi) where S is the set of places dividing
   the modulus of bnr (and the infinite places), 3: return also the
   character */
GEN
bnrL1(GEN bnr, GEN subgp, long flag, long prec)
{
  GEN bnf, nf, cyc, Mcyc, p1, L1, chi, lchi, clchi, allCR, listCR, dataCR;
  GEN S, T, rep, indCR, invCR, Qt;
  long N, cl, i, j, k, nc, lq, a, av = avma, ncc;

  checkbnr(bnr);
  bnf  = (GEN)bnr[1];
  nf   = (GEN)bnf[7];
  cyc  = gmael(bnr, 5, 2);
  Mcyc = diagonal(cyc);
  ncc  = lg(cyc) - 1;
  N    = degpol(nf[1]);

  if (N == 1)
    err(talker, "the ground field must be distinct from Q");

  if (flag < 0 || flag > 8)
    err(flagerr,"bnrL1");

  /* check the bnr */
  checkbnrgen(bnr);

  /* compute bnr(conductor) */
  if (!(flag & 2))
  {
    p1   = conductor(bnr, gzero, 2);
    bnr  = (GEN)p1[2];
    cyc  = gmael(bnr, 5, 2);
    Mcyc = diagonal(cyc);
  }

  /* check the subgroup */
  if (! (subgp = get_subgroup(subgp,Mcyc)) )
    err(talker, "incorrect subgroup in bnrL1");

  cl = labs(itos(det(subgp)));
  Qt = InitQuotient0(Mcyc, subgp);
  lq = lg((GEN)Qt[2]) - 1;

  /* compute all the characters */
  allCR = EltsOfGroup(cl, (GEN)Qt[2]);

  /* make a list of all non-trivial characters modulo conjugation */
  listCR = cgetg(cl, t_VEC);
  indCR = new_chunk(cl);
  invCR = new_chunk(cl);

  nc = 0;

  for (i = 1; i < cl; i++)
  {
    chi = (GEN)allCR[i];

    /* lift the character to a character on Cl(bnr) */
    lchi = cgetg(ncc + 1, t_VEC);
    for (j = 1; j <= ncc; j++)
    {
      p1 = gzero;
      for (k = 1; k <= lq; k++)
	p1 = gadd(p1, gdiv(mulii(gmael3(Qt, 3, j, k), (GEN)chi[k]),
			   gmael(Qt, 2, k)));
      lchi[j] = lmodii(gmul(p1, (GEN)cyc[j]), (GEN)cyc[j]);
    }
    clchi = ConjChar(lchi, cyc);

    a = i;
    for (j = 1; j <= nc; j++)
      if (gegal(gmael(listCR, j, 1), clchi)) { a = -j; break; }

    if (a > 0)
    {
      nc++;
      listCR[nc] = lgetg(3, t_VEC);
      mael(listCR, nc, 1) = (long)lchi;
      mael(listCR, nc, 2) = (long)bnrconductorofchar(bnr, lchi);

      indCR[i]  = nc;
      invCR[nc] = i;
    }
    else
      indCR[i] = -invCR[-a];

    allCR[i] = lcopy(lchi);
  }

  /* the trivial character has to be a row vector too! */
  allCR[cl] = ltrans((GEN)allCR[cl]);

  setlg(listCR, nc + 1);
  if (nc == 0) err(talker, "no non-trivial character in bnrL1");

  /* compute the data for these characters */
  dataCR = InitChar(bnr, listCR, prec);

  p1 = GetST(dataCR, prec);

  S = (GEN)p1[1];
  T = (GEN)p1[2];

  if (flag & 1)
    L1 = cgetg(cl, t_VEC);
  else
    L1 = cgetg(cl + 1, t_VEC);

  for (i = 1; i < cl; i++)
  {
    a = indCR[i];
    if (a > 0)
      L1[i] = (long)GetValue((GEN)dataCR[a], (GEN)S[a], (GEN)T[a], flag & 1,
			     flag & 2, prec);
  }

  for (i = 1; i < cl; i++)
  {
    a = indCR[i];
    if (a < 0)
      L1[i] = lconj((GEN)L1[-a]);
  }

  if (!(flag & 1))
    L1[cl] = (long)GetValue1(bnr, flag & 2, prec);
  else
    cl--;

  if (flag & 4)
  {
    rep = cgetg(cl + 1, t_VEC);
    for (i = 1; i <= cl; i++)
    {
      p1 = cgetg(3, t_VEC);
      p1[1] = allCR[i];
      p1[2] = L1[i];

      rep[i] = (long)p1;
    }
  }
  else
    rep = L1;

  return gerepilecopy(av, rep);
}
