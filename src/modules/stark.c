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

/********************************************************************/
/*                    Miscellaneous functions                       */
/********************************************************************/

/* Compute the image of logelt by chi as a complex number if flag = 0,
   otherwise as a polmod, see InitChar in part 3 */
static GEN
ComputeImagebyChar(GEN chi, GEN logelt, long flag)
{
  GEN gn = gmul((GEN)chi[1], logelt), x = (GEN)chi[flag? 4: 2];
  long d = itos((GEN)chi[3]), n = smodis(gn, d);
  /* x^d = 1 and, if d even, x^(d/2) = -1 */
  if ((d & 1) == 0)
  {
    d /= 2;
    if (n >= d) return gneg(gpowgs(x, n-d));
  }
  return gpowgs(x, n);
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

/* compute the next element for FindEltofGroup */
static GEN
NextEltofGroup(GEN cyc, long l, long adec)
{
  GEN p1;
  long dj, j;

  p1 = cgetg(l + 1, t_COL);
  
  for (j = 1; j <= l; j++)
  {
    dj = itos((GEN)cyc[j]);
    p1[j] = lstoi(adec%dj);
    adec /= dj;
  }
  
  return p1;
}

/* Compute all the elements of a group given by its SNF */
static GEN
FindEltofGroup(long order, GEN cyc)
{
  long l, i;
  GEN rep;

  l = lg(cyc)-1;

  rep = cgetg(order + 1, t_VEC);

  for  (i = 1; i <= order; i++)
    rep[i] = (long)NextEltofGroup(cyc, l, i);

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

  eltq = FindEltofGroup(order, cyc);

  elt = cgetg(order + 1, t_VEC);

  for (i = 1; i <= order; i++)
    elt[i] = (long)inverseimage(surj, (GEN)eltq[i]);

  return gerepileupto(av, elt);
}

/* Let bnr1, bnr2 be such that mod(bnr2) | mod(bnr1), compute the
   matrix of the surjective map Cl(bnr1) ->> Cl(bnr2) */
static GEN
GetSurjMat(GEN bnr1, GEN bnr2)
{
  long nbg, i;
  GEN gen, M;

  gen = gmael(bnr1, 5, 3);
  nbg = lg(gen) - 1;

  M = cgetg(nbg + 1, t_MAT);
  for (i = 1; i <= nbg; i++)
    M[i] = (long)isprincipalray(bnr2, (GEN)gen[i]);

  return M;
}

/* A character is given by a vector [(c_i), z, d, pm] such that
   chi(id) = z ^ sum(c_i * a_i) where
     a_i= log(id) on the generators of bnr
     z  = exp(2i * Pi / d)
     pm = z as a polmod */
static GEN
get_Char(GEN chi, long prec)
{
  GEN p2, d, _2ipi = gmul(gi, shiftr(mppi(prec), 1));
  p2 = cgetg(5, t_VEC); d = denom(chi);
  p2[1] = lmul(d, chi);
  if (egalii(d, gdeux))
    p2[2] = lstoi(-1);
  else
    p2[2] = lexp(gdiv(_2ipi, d), prec);
  p2[3] = (long)d;
  p2[4] = lmodulcp(polx[0], cyclo(itos(d), 0));
  return p2;
}

/* Let chi a character defined over bnr and primitif over bnrc,
   compute the corresponding primitive character and the vectors of
   prime ideals dividing bnr but not bnr. Returns NULL if bnr = bnrc */
static GEN
GetPrimChar(GEN chi, GEN bnr, GEN bnrc, long prec)
{
  long nbg, i, j, l, av = avma, nd;
  GEN gen, cyc, U, chic, M, s, p1, cond, condc, p2, nf;
  GEN prdiff, Mrc;

  cond  = gmael(bnr, 2, 1);
  condc = gmael(bnrc, 2, 1);
  if (gegal(cond, condc)) return NULL;

  gen   = gmael(bnr, 5, 3);
  nbg   = lg(gen) - 1;
  cyc   = gmael(bnr, 5, 2);
  Mrc   = diagonal(gmael(bnrc, 5, 2));
  nf    = gmael(bnr, 1, 7);

  cond  = (GEN)cond[1];
  condc = (GEN)condc[1];

  M  = GetSurjMat(bnr, bnrc);
  l  = lg((GEN)M[1]);
  p1 = hnfall(concatsp(M, Mrc));
  U  = (GEN)p1[2];

  chic = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    s  = gzero; p1 = (GEN)U[i + nbg];
    for (j = 1; j <= nbg; j++)
    {
      p2 = gdiv((GEN)p1[j], (GEN)cyc[j]);
      s  = gadd(s,gmul(p2,(GEN)chi[j]));
    }
    chic[i] = (long)s;
  }

  p2 = (GEN)idealfactor(nf, cond)[1];
  l  = lg(p2);

  prdiff = cgetg(l, t_COL);
  for (nd=1, i=1; i < l; i++)
    if (!idealval(nf, condc, (GEN)p2[i])) prdiff[nd++] = p2[i];
  setlg(prdiff, nd);

  p1  = cgetg(3, t_VEC);
  p1[1] = (long)get_Char(chic,prec);
  p1[2] = lcopy(prdiff);

  return gerepileupto(av,p1);
}

/* Let dataCR be a list of characters, compute the image of logelt */
static GEN
chiideal(GEN dataCR, GEN logelt, long flag)
{
  long j, l = lg(dataCR);
  GEN rep = cgetg(l, t_VEC);

  for (j = 1; j < l; j++)
    rep[j] = (long)ComputeImagebyChar(gmael(dataCR, j, 5), logelt, flag);

  return rep;
}

static GEN
GetDeg(GEN dataCR)
{
  long i, l = lg(dataCR);
  GEN degs = cgetg(l, t_VECSMALL);

  for (i = 1; i < l; i++)
    degs[i] = degpol(gmael4(dataCR, i, 5, 4, 1));
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
  long i, l;
  GEN MQ, MrC, H, snf, snf2, rep, p1;

  l = lg(DA)-1;
  H = gcmp0(C)? DA: C;
  MrC  = gauss(H, DA);
  snf  = smith2(hnf(MrC));
  MQ   = concatsp(gmul(H, (GEN)snf[1]), DA);
  snf2 = smith2(hnf(MQ));

  rep = cgetg(5, t_VEC);

  p1  = cgetg(l + 1, t_VEC);
  for (i = 1; i <= l; i++)
    p1[i] = lcopy(gcoeff((GEN)snf2[3], i, i));

  rep[1] = (long)dethnf((GEN)snf2[3]);
  rep[2] = (long)p1;
  rep[3] = lcopy((GEN)snf2[1]);
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
   relations of A and B, let nbA, nbB be resp. the rank of A and B,
   compute the kernel of s. If DA = 0 then A is free */
static GEN
ComputeKernel0(GEN P, GEN DA, GEN DB, long nbA, long nbB)
{
  long rk, av = avma;
  GEN herm, mask1, mask2, U;

  herm  = hnfall(concatsp(P, DB));
  rk = nbA + nbB + 1;
  rk -= lg((GEN)herm[1]); /* two steps: bug in pgcc 1.1.3 inlining (IS) */

  mask1 = subis(shifti(gun, nbA), 1);
  mask2 = subis(shifti(gun, rk), 1);

  U = matextract((GEN)herm[2], mask1, mask2);

  if (!gcmp0(DA)) U = concatsp(U, DA);
  return gerepileupto(av, hnf(U));
}

/* Let m and n be two moduli such that n|m and let C be a congruence
   group modulo n, compute the corresponding congruence group modulo m
   ie then kernel of the map Clk(m) ->> Clk(n)/C */
static GEN
ComputeKernel(GEN bnrm, GEN dataC)
{
  long av = avma, i, nbm, nbq;
  GEN bnrn, Mrm, genm, Mrq, mgq, P;

  bnrn = (GEN)dataC[1];
  Mrm  = diagonal(gmael(bnrm, 5, 2));
  genm = gmael(bnrm, 5, 3);
  nbm  = lg(genm) - 1;
  Mrq  = diagonal(gmael(dataC, 2, 2));
  mgq  = gmael(dataC, 2, 3);
  nbq  = lg(mgq) - 1;

  P = cgetg(nbm + 1, t_MAT);
  for (i = 1; i <= nbm; i++)
    P[i] = lmul(mgq, isprincipalray(bnrn, (GEN)genm[i]));

  return gerepileupto(av, ComputeKernel0(P, Mrm, Mrq, nbm, nbq));
}

/* Let C a congruence group in bnr, compute its subgroups of index 2 as
   subgroups of Clk(bnr) */
static GEN
ComputeIndex2Subgroup(GEN bnr, GEN C)
{
  long nb, i, l, av = avma;
  GEN snf, Mr, U, CU, subgrp, rep, p1;

  disable_dbg(0); 

  Mr = diagonal(gmael(bnr, 5, 2));
  snf = smith2(gmul(ginv(C), Mr));

  U = ginv((GEN)snf[1]);
  l = lg((GEN)snf[3]);

  p1 = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
    p1[i] = mael3(snf, 3, i, i);

  subgrp  = subgrouplist(p1, 2);
  nb = lg(subgrp) - 1; CU = gmul(C,U);

  rep = cgetg(nb, t_VEC);
  for (i = 1; i < nb; i++) /* skip Id which comes last */
    rep[i] = (long)hnf(concatsp(gmul(CU, (GEN)subgrp[i]), Mr));

  disable_dbg(-1); 
  return gerepilecopy(av, rep);
}

/* Let pr be a prime (pr may divide mod(bnr)), compute the indexes
   e,f of the splitting of pr in the class field nf(bnr/subgroup) */
static GEN
GetIndex(GEN pr, GEN bnr, GEN subgroup)
{
  long av = avma, v, lg, i;
  GEN bnf, mod, mod0, mpr0, mpr, bnrpr, subpr, M, e, f, dtQ, p1;
  GEN rep, cycpr, cycQ;

  bnf  = (GEN)bnr[1];
  mod  = gmael(bnr, 2, 1);
  mod0 = (GEN)mod[1];

  /* Compute the part of mod coprime to pr */
  v = idealval(bnf, mod0, pr);
  mpr0 = idealdivexact(bnf, mod0, idealpow(bnf, pr, stoi(v)));

  mpr = cgetg(3, t_VEC);
  mpr[1] = (long)mpr0;
  mpr[2] = mod[2];
  if (gegal(mpr0, mod0))
  {
    bnrpr = bnr;
    subpr = subgroup;
  }
  else
  {
    bnrpr = buchrayinitgen(bnf, mpr);
    cycpr = gmael(bnrpr, 5, 2);
    M = GetSurjMat(bnr, bnrpr);
    M = gmul(M, subgroup);
    subpr = hnf(concatsp(M, diagonal(cycpr)));
  }

  /* e = #(bnr/subgroup) / #(bnrpr/subpr) */
  e = gdiv(det(subgroup), det(subpr));

  /* f = order of [pr] in bnrpr/subpr */
  dtQ  = InitQuotient(bnrpr, subpr);
  p1   = isprincipalray(bnrpr, pr);
  p1   = gmul(gmael(dtQ, 2, 3), p1);
  cycQ = gmael(dtQ, 2, 2);
  lg = lg(cycQ) - 1;
  f  = gun;
  for (i = 1; i <= lg; i++)
    f = glcm(f, gdiv((GEN)cycQ[i], ggcd((GEN)cycQ[i], (GEN)p1[i])));

  rep = cgetg(3, t_VEC);
  rep[1] = lcopy(e);
  rep[2] = lcopy(f);

  return gerepileupto(av, rep);
}


/* Given a conductor and a subgroups, return the corresponding
   complexity and precision required using quickpol */
static GEN
CplxModulus(GEN data, long *newprec, long prec)
{
  long av = avma, pr, dprec;
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

  for (;;)
  {
    p1[5] = (long)InitChar0((GEN)data[3], dprec);
    pol   = AllStark(p1, nf, -1, dprec);
    if (!gcmp0(leading_term(pol)))
    {
      cpl   = mpabs(poldisc0(pol, 0));
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
  rb = powgi(gmul(gmael(bnf, 7, 3), det(f)), gmul2n(gmael(bnr, 5, 1), 3));

  bpr = (GEN)idealfactor(nf, f)[1];
  nbp = lg(bpr) - 1;

  indpr = cgetg(nbp + 1,t_VEC);
  for (i = 1; i <= nbp; i++)
  {
    p1 = GetIndex((GEN)bpr[i], bnr, sgp);
    indpr[i] = lmulii((GEN)p1[1], (GEN)p1[2]);
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
  limnorm = 200;

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
	  if (signe(p1))
	  {
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
	      if (signe(p1))
	      {
		/* check the splitting of primes */
		for (j = 1; j <= nbp; j++)
		{
		  p1 = GetIndex((GEN)bpr[j], bnrm, D);
		  p1 = mulii((GEN)p1[1], (GEN)p1[2]);
		  if (egalii(p1, (GEN)indpr[j])) break; /* no good */
		}
                if (j > nbp)
                {
		  p2 = cgetg(6, t_VEC);

		  p2[1] = lcopy(bnrm);
                  p2[2] = lcopy(D);
                  p2[3] = (long)InitQuotient((GEN)p2[1], (GEN)p2[2]);
                  p2[4] = (long)InitQuotient((GEN)p2[1], ImC);

		  p1 = CplxModulus(p2, &pr, prec);

		  if (first == 1 || gcmp(p1, (GEN)rep[5]) < 0)
		  {
		    *newprec = pr;
		    for (j = 1; j <= 4; j++) rep[j] = p2[j];
		    rep[5] = (long)p1;
		  }

		  if (!fl || (gcmp(p1, rb) < 0))
		  {
		    rep[5] = (long)InitChar0((GEN)rep[3], *newprec);
		    return gerepilecopy(av, rep);
		  }
		  if (DEBUGLEVEL >= 2)
		    fprintferr("Trying to find another modulus...");
		  first--;
                }
	      }
	    }
	  }
          arch[N+1-s] = un;
	}
        if (first <= bnd)
	{
	  if (DEBUGLEVEL >= 2)
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
ComputeArtinNumber(GEN datachi, long flag, long prec)
{
  long av = avma, av2, G, ms, j, i, nz, zcard, q, l, N, lim;
  GEN chi, nc, dc, p1, cond0, cond1, elts, Msign, umod2, lambda, nf;
  GEN sg, p2, chib, diff, vt, z, idg, mu, idh, zid, zstruc, zgen, zchi;
  GEN classe, bnr, beta, s, tr, p3, den, muslambda, Pi, lp1, beta2;

  chi   = (GEN)datachi[8];
  /* trivial case */
  if (cmpsi(2, (GEN)chi[3]) >= 0) return gun;

  bnr   = (GEN)datachi[3];
  nf    = gmael(bnr, 1, 7);
  diff  = gmael(nf, 5, 5);
  cond0 = gmael3(bnr, 2, 1, 1);
  cond1 = gmael3(bnr, 2, 1, 2);
  umod2 = gmodulcp(gun, gdeux);
  N     = degpol(nf[1]);
  Pi    = mppi(prec);

  G   = - bit_accuracy(prec) >> 1;
  nc  = idealnorm(nf, cond0);
  dc  = idealmul(nf, diff, cond0);
  den = idealnorm(nf, dc);
  z   = gexp(gdiv(gmul2n(gmul(gi, Pi), 1), den), prec);

  q = 0;
  for (i = 1; i < lg(cond1); i++)
    if (gcmp1((GEN)cond1[i])) q++;

  /* compute a system of elements congru to 1 mod cond0 and giving all
     possible signatures for cond1 */
  p1 = zarchstar(nf, cond0, cond1, q);
  elts = (GEN)p1[2];
  Msign = gmul((GEN)p1[3], umod2);
  ms = lg(elts) - 1;

  /* find lambda in diff.cond such that gcd(lambda.(diff.cond)^-1,cond0) = 1
     and lambda >(cond1)> 0 */
  lambda = idealappr(nf, dc);
  sg = zsigne(nf, lambda, cond1);
  p2 = lift(gmul(Msign, sg));

  for (j = 1; j <= ms; j++)
    if (gcmp1((GEN)p2[j])) lambda = element_mul(nf, lambda, (GEN)elts[j]);

  idg = idealdivexact(nf, lambda, dc);

  /* find mu in idg such that idh=(mu) / idg is coprime with cond0 and
     mu >(cond1)> 0 */
  if (!gcmp1(gcoeff(idg, 1, 1)))
  {
    p1 = idealfactor(nf, idg);
    p2 = idealfactor(nf, cond0);

    l = lg((GEN)p2[1]);
    for (i = 1; i < l; i++) coeff(p2, i, 2) = zero;

    p1 = gtrans(concatsp(gtrans(p1), gtrans(p2)));
    mu = idealapprfact(nf, p1);
    sg = zsigne(nf, mu, cond1);
    p2 = lift(gmul(Msign, sg));

    for (j = 1; j <= ms; j++)
      if (gcmp1((GEN)p2[j])) mu = element_mul(nf, mu, (GEN)elts[j]);

    idh = idealdivexact(nf, mu, idg);
  }
  else
  {
    mu  = gun;
    idh = gcopy(idg);
  }

  muslambda = element_div(nf, mu, lambda);

  /* compute a system of generators of (Ok/cond)^* cond1-positive */
  zid = zidealstarinitgen(nf, cond0);

  zcard  = itos(gmael(zid, 2, 1));
  zstruc = gmael(zid, 2, 2);
  zgen   = gmael(zid, 2, 3);
  nz = lg(zgen) - 1;

  zchi = cgetg(nz + 1, t_VEC);
  for (i = 1; i <= nz; i++)
  {
    p1 = (GEN)zgen[i];
    sg = zsigne(nf, p1, cond1);
    p2 = lift(gmul(Msign, sg));

    for (j = 1; j <= ms; j++)
      if (gcmp1((GEN)p2[j])) p1 = element_mul(nf, p1, (GEN)elts[j]);

    classe = isprincipalray(bnr, p1);
    zchi[i] = (long)ComputeImagebyChar(chi, classe, 0);
    zgen[i] = (long)p1;
  }

  /* Sum chi(beta) * exp(2i * Pi * Tr(beta * mu / lambda) where beta
     runs through the classes of (Ok/cond0)^* and beta cond1-positive */

  p3 = cgetg(N + 1, t_COL);
  for (i = 1; i <= N; i++) p3[i] = zero;

  vt = cgetg(N + 1, t_VEC);
  for (i = 1; i <= N; i++)
  {
    p3[i] = un;
    vt[i] = ltrace(basistoalg(nf, p3));
    p3[i] = zero;
  }

  lp1 = NULL;
  s = gzero;

  av2 = avma; lim = stack_lim(av2, 1);

  for (i = 0; i < zcard; i++)
  {
    p1 = NextEltofGroup(zstruc, nz, i);

    /* we test if we can use the previous value 
       of beta / chib to compute the next one */
    /* FIXME: there should be a better way of doing that! */
    if (!lp1 || !gcmp1(gnorml2(gsub(p1, lp1))))
    {
      beta = gun;
      chib = gun;

      for (j = 1; j <= nz; j++)
      {
	if (!gcmp0((GEN)p1[j]))
	{
	  p2 = element_powmodideal(nf, (GEN)zgen[j], (GEN)p1[j], cond0);
	  beta = element_mulmodideal(nf, beta, p2, cond0);
	  chib = gmul(chib, powgi((GEN)zchi[j], (GEN)p1[j]));
	}
      }
    }
    else
    {
      /* we use the fact that NextEltofGroup is, in general, 
	 obtained by adding 1 to a component of p1 */
      for (j = 1; j <= nz; j++)
	if (!gegal((GEN)p1[j], (GEN)lp1[j]))
	{
	  beta = element_mulmodideal(nf, beta, (GEN)zgen[j], cond0);
	  chib = gmul(chib, (GEN)zchi[j]);
	}
    }  
    
    lp1 = p1;
    sg  = zsigne(nf, beta, cond1);
    p2  = lift(gmul(Msign, sg));

    for (j = 1; j <= ms; j++)
      if (gcmp1((GEN)p2[j]))
	beta = element_mul(nf, beta, (GEN)elts[j]);

    beta2 = element_mul(nf, beta, muslambda);
    tr = gmul(vt, beta2);
    tr = gmod(gmul(tr, den), den);

    s = gadd(s, gmul(chib, powgi(z,tr)));

    if (low_stack(lim, stack_lim(av2, 1)))
    {
      GEN *gptr[5];
      gptr[0] = &s; gptr[1] = &lp1; gptr[2] = &beta; gptr[3] = &chib;
      if (DEBUGMEM > 1) err(warnmem,"ComputeArtinNumber");
      gerepilemany(av2, gptr, 4);
    }
  }

  classe = isprincipalray(bnr, idh);
  s = gmul(s, ComputeImagebyChar(chi, classe, 0));
  s = gdiv(s, gsqrt(nc, prec));

  p1 = gsubgs(gabs(s, prec), 1);

  i = expo(p1);
  if ((i > G) && !flag)
    err(bugparier, "ComputeArtinNumber");

  return gerepileupto(av, gmul(s, gpowgs(gneg_i(gi),q)));
}

/* compute the constant W of the functional equation of
   Lambda(chi). If flag = 1 then chi is assumed to be primitive */
GEN
bnrrootnumber(GEN bnr, GEN chi, long flag, long prec)
{
  long av = avma, l, i;
  GEN cond, condc, bnrc, chic, cyc, d, p1, p2, dtcr, Pi;

  if ((flag < 0) || (flag > 1))
    err(flagerr,"bnrrootnumber");

  checkbnr(bnr);

  cond = gmael(bnr, 2, 1);
  l    = lg(gmael(bnr, 5, 2));
  Pi   = mppi(prec);

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

  chic = cgetg(l, t_VEC);
  cyc  = gmael(bnr, 5, 2);
  for (i = 1; i < l; i++)
    chic[i] = ldiv((GEN)chi[i], (GEN)cyc[i]);
  d = denom(chic);

  p2 = cgetg(4, t_VEC);
  p2[1] = lmul(d, chic);
  if (egalii(d, gdeux))
    p2[2] = lstoi(-1);
  else
    p2[2] = lexp(gdiv(gmul2n(gmul(gi, Pi), 1), d), prec);
  p2[3] = (long)d;

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
  long l, i;
  GEN p1, ray, r, A, rep, diff, chi, bnrc;

  diff = (GEN)dtcr[6];
  bnrc = (GEN)dtcr[3];
  chi  = (GEN)dtcr[8];
  l    = lg(diff) - 1;

  A = gun;
  r = gzero;

  for (i = 1; i <= l; i++)
  {
    ray = isprincipalray(bnrc, (GEN)diff[i]);
    p1  = ComputeImagebyChar(chi, ray, 0);

    if (flag)
      A = gmul(A, gsub(gun, gdiv(p1, idealnorm((GEN)bnrc[1], (GEN)diff[i]))));
    else
    {
      if (gcmp1(p1))
      {
	r = addis(r, 1);
	A = gmul(A, glog(idealnorm((GEN)bnrc[1], (GEN)diff[i]), prec));
      }
      else
	A = gmul(A, gsub(gun, p1));
    }
  }

  if (flag) return A;

  rep = cgetg(3, t_VEC);
  rep[1] = (long)r;
  rep[2] = (long)A;

  return rep;
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
  GEN modul, dk, C, dataCR, chi, cond, Mr, chic, gr2, p1, p2, q;
  long N, r1, r2, prec2, h, i, j, nbg, av = avma;

  modul = gmael(bnr, 2, 1);
  Mr    = gmael(bnr, 5, 2);
  nbg   = lg(Mr) - 1;
  dk    = (GEN)nf[3];
  N     = degpol(nf[1]);
  r1    = nf_get_r1(nf);
  r2    = (N - r1) >> 1; gr2 = stoi(r2);
  prec2 = ((prec - 2)<<1) + EXTRA_PREC;
  C     = gmul2n(gsqrt(gdiv(absi(dk), gpowgs(mppi(prec2),N)), prec2), -r2);

  disable_dbg(0);

  h = lg(listCR) - 1;
  dataCR = cgetg(h + 1, t_VEC);
  for (i = 1; i <= h ;i++)
    dataCR[i] = lgetg(10, t_VEC);

  q = gnorml2((GEN)modul[2]);
  p1 = cgetg(5, t_VEC);
  p1[1] = (long)q;
  p1[2] = lsubsi(r1, q);
  p1[3] = (long)gr2;
  p1[4] = lmax(addis((GEN)p1[2], r2+1), addsi(r2, q));

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
      data[9] = (long)p1;

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

    chic = cgetg(nbg + 1, t_VEC);
    for (j = 1; j <= nbg; j++)
      chic[j] = ldiv((GEN)chi[j], (GEN)Mr[j]);
    data[5] = (long)get_Char(chic,prec); /* char associated to bnr(m) */

    /* compute diff(chi) and the corresponding primitive character */
    data[7] = cond[1];
    p2 = GetPrimChar(chi, bnr, (GEN)data[3], prec2);
    if (p2)
    {
      data[6] = p2[2];
      data[8] = p2[1];
    }
    else
    {
      data[6] = lgetg(1, t_VEC);
      data[8] = data[5];
    }

    /* compute q and store [q, r1 - q, r2] */
    if (!olddata)
    {
      q = gnorml2((GEN)cond[2]);
      p2 = cgetg(5, t_VEC);
      p2[1] = (long)q;
      p2[2] = lsubsi(r1, q);
      p2[3] = (long)gr2;
      p2[4] = lmax(addis((GEN)p2[2], r2+1), addsi(r2, q));
      data[9] = (long)p2;
    }
    else
      data[9] = olddata[9];
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
  long hD, h, nc, i, j, lD, nbg, tnc, av = avma;

  Surj = gmael(dataD, 2, 3);
  MrD  = gmael(dataD, 2, 2);
  bnr  = (GEN)dataD[1];
  Mr   = gmael(bnr, 5, 2);
  hD   = itos(gmael(dataD, 2, 1));
  h    = hD >> 1;
  lD   = lg(MrD)-1;
  nbg  = lg(Mr) - 1;

  disable_dbg(0);

  listCR = cgetg(h + 1, t_VEC); /* non-conjugate characters */
  nc  = 1;
  allCR  = cgetg(h + 1, t_VEC); /* all characters, including conjugates */
  tnc = 1;

  p1 = FindEltofGroup(hD, MrD);

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

    /* compute the order of chi */
    p2 = cgetg(nbg + 1, t_VEC);
    for (j = 1; j <= nbg; j++)
      p2[j] = ldiv((GEN)lchi[j], (GEN)Mr[j]);
    d = denom(p2);

    /* if chi is not real, add its conjugate character to allCR */
    if (!gegal(d, gdeux))
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
  GEN dk, C, p1, Pi;
  long av = avma, N, l, j, prec2;

  dk    =  (GEN)nf[3];
  N     =  degpol((GEN)nf[1]);
  l     =  lg(dataCR) - 1;
  prec2 = ((prec - 2)<<1) + EXTRA_PREC;

  Pi    = mppi(prec2);

  C = gsqrt(gdiv(dk, gpowgs(Pi, N)), prec2);

  for (j = 1; j <= l; j++)
  {
    mael(dataCR, j, 2) = lmul(C, gsqrt(det(gmael(dataCR, j, 7)), prec2));

    mael4(dataCR, j, 3, 1, 7) = lcopy(nf);

    p1 = gmael(dataCR, j, 5);
    p1[2] = lexp(gdiv(gmul2n(gmul(gi, Pi), 1), (GEN)p1[3]), prec);

    p1 = gmael(dataCR, j, 8);
    p1[2] = lexp(gdiv(gmul2n(gmul(gi, Pi), 1), (GEN)p1[3]), prec);
  }

  return gerepilecopy(av, dataCR);
}

/********************************************************************/
/*             4th part: compute the coefficients an(chi)           */
/*                                                                  */
/* matan entries are arrays of ints containing the coefficients of  */
/* an(chi) as a polmod modulo cyclo(order(chi))                     */
/********************************************************************/

static void
_0toCoeff(int *rep, long dg)
{
  long i;
  for (i=0; i<dg; i++) rep[i] = 0;
}

/* transform a polmod into coeff */
static void
Polmod2Coeff(int *rep, GEN polmod, long dg)
{
  GEN pol = (GEN)polmod[2];
  long i,d = degpol(pol);

  pol += 2;
  for (i=0; i<=d; i++) rep[i] = itos((GEN)pol[i]);
  for (   ; i<dg; i++) rep[i] = 0;
}

/* initialize a cl x nmax x [degs[1], ..., degs[cl] matrix of ints */
/* modified to allocate ints and pointers separately since this used to
   break on 64bit platforms --GN1999Sep01 */
static int***
InitMatAn(long cl, long nmax, GEN degs, long flag)
{
  long si,dg,i,j,k, n = nmax+1;
  int *c, **pj, ***A;

  for (si=0, i=1; i <= cl; i++)
  {
    dg = degs[i];
    si += dg;
  }
  A = (int***)gpmalloc((cl+1)*sizeof(int**) + cl*n*sizeof(int*));
  c = (int*)gpmalloc(si*n*sizeof(int));
  A[0] = (int**)c;		/* keep it around for FreeMat() */

  pj = (int**)(A + (cl+1));
  for (i = 1; i <= cl; i++, pj+=n)
  {
    A[i] = pj; dg = degs[i];
    for (j = 0; j < n; j++,c+=dg)
    {
      pj[j] = c;
      c[0] = (j == 1 || flag);
      for (k = 1; k < dg; k++) c[k] = 0;
    }
  }
  return A;
}

static void
FreeMat(int ***m)
{
  free((void *)(m[0]));
  free((void *)m);
}

/* initialize coeff reduction */
/* similar change --GN1999Sep01 */
static int***
InitReduction(GEN dataCR, GEN degs)
{
  long av = avma,si,sp,dg,i,j, cl = lg(dataCR)-1;
  int *c, **pj, ***A;
  GEN d,polmod,pol, x = polx[0];

  for (si=sp=0, i=1; i <= cl; i++)
  {
    dg = degs[i];
    sp += dg;
    si += dg*dg;
  }
  A = (int***)gpmalloc((cl+1)*sizeof(int**) + sp*sizeof(int*));
  c = (int*)gpmalloc(si*sizeof(int));
  A[0] = (int**)c;		/* keep it around for FreeMat() */

  pj = (int**)(A + (cl+1));
  for (i = 1; i <= cl; i++)
  {
    A[i] = pj;
    d   = gmael3(dataCR, i, 5, 3);
    pol = cyclo(itos(d), 0);
    dg  = degs[i]; /* degree(pol) */
    for (j = 0; j < dg; j++,c+=dg)
    {
      pj[j] = c;
      polmod = gmodulcp(gpowgs(x, dg + j), pol);
      Polmod2Coeff(c, polmod, dg);
    }
    pj += dg;
  }
  avma = av; return A;
}

#if 0
static void
pan(int ***an,long cl, long nmax, GEN degs)
{
  long i,j,k;
  for (i = 1; i <= cl; i++)
  {
    long dg = degs[i];
    for (j = 0; j <= nmax; j++)
      for (k = 0; k < dg; k++) fprintferr("%d ",an[i][j][k]);
  }
}
#endif

/* multiply (with reduction) a polmod with a coeff. put result in c1 */
static void
MulPolmodCoeff(GEN polmod, int* c1, int** reduc, long dg)
{
  long av,i,j;
  int c, *c2, *c3;

  if (gcmp1(polmod)) return;
  for (i = 0; i < dg; i++)
    if (c1[i]) break;
  if (i == dg) return;
  av = avma;
  c3 = (int*)new_chunk(2*dg);
  c2 = (int*)new_chunk(dg);
  Polmod2Coeff(c2,polmod, dg);

  for (i = 0; i < 2*dg; i++)
  {
    c = 0;
    for (j = 0; j <= i; j++)
      if (j < dg && j > i - dg) c += c1[j] * c2[i-j];
    c3[i] = c;
  }
  c2 = c1;
  for (i = 0; i < dg; i++)
  {
    c = c3[i];
    for (j = 0; j < dg; j++) c += reduc[j][i] * c3[dg+j];
    c2[i] = c;
  }
  /* cast necessary to work around a gcc-2.96 bug on alpha-linux (IS) */
  for (     ; i < (short)dg; i++) c2[i] = 0;
  avma = av;
}

/* c0 <- c0 + c2 * c1 */
static void
AddMulCoeff(int *c0, int *c2, int* c1, int** reduc, long dg)
{
  long av,i,j;
  int c, *c3;

  if (!c2) /* c2 == 1 */
  {
    for (i = 0; i < dg; i++) c0[i] += c1[i];
    return;
  }
  for (i = 0; i <= dg; i++)
    if (c1[i]) break;
  if (i > dg) return;
  av = avma;
  c3 = (int*)new_chunk(2*dg);
  for (i = 0; i < 2*dg; i++)
  {
    c = 0;
    for (j = 0; j <= i; j++)
      if (j < dg && j > i - dg) c += c1[j] * c2[i-j];
    c3[i] = c;
  }
  for (i = 0; i < dg; i++)
  {
    c = c0[i] + c3[i];
    for (j = 0; j < dg; j++) c += reduc[j][i] * c3[dg+j];
    c0[i] = c;
  }

  avma = av;
}

/* returns 0 if c is zero, 1 otherwise. */
static long
IsZero(int* c, long dg)
{
  long i;

  for (i = 0; i < dg; i++)
    if (c[i]) return 0;
  return 1;
}

/* evaluate the coeff. No Garbage collector */
static GEN
EvalCoeff(GEN z, int* c, long dg)
{
  long i,j;
  GEN e, r;

#if 0
  /* standard Horner */
  e = stoi(c[dg - 1]);
  for (i = dg - 2; i >= 0; i--)
    e = gadd(stoi(c[i]), gmul(z, e));
#else
  /* specific attention to sparse polynomials */
  e = NULL;
  for (i = dg-1; i >=0; i=j-1)
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

/* copy the n * m array matan */
static void
CopyCoeff(int*** a, int*** a2, long n, long m, GEN degs)
{
  long i,j,k;

  for (i = 1; i <= n; i++)
  {
    long dg = degs[i];
    int **b = a[i], **b2 = a2[i];
    for (j = 0; j <= m; j++)
    {
      int *c = b[j], *c2 = b2[j];
      for (k = 0; k < dg; k++) c2[k] = c[k];
    }
  }
  return;
}

/* initialize the data for GetRay */
static GEN
InitGetRay(GEN bnr,  long nmax)
{
  long bd, i, j, l;
  GEN listid, listcl, id, rep, bnf, cond;

  bnf  =  (GEN)bnr[1];
  cond =  gmael3(bnr, 2, 1, 1);

  if (nmax < 1000) return NULL;

  rep = cgetg(4, t_VEC);

  disable_dbg(0);
  bd = min(1000, nmax / 50);
  listid = ideallist(bnf, bd);
  disable_dbg(-1);

  listcl = cgetg(bd + 1, t_VEC);
  for (i = 1; i <= bd; i++)
  {
    l = lg((GEN)listid[i]) - 1;
    listcl[i] = lgetg(l + 1, t_VEC);

    for (j = 1; j <= l; j++)
    {
      id = gmael(listid, i, j);
      if (gcmp1(gcoeff(idealadd(bnf, id, cond), 1, 1)))
	mael(listcl, i, j) = (long)isprincipalray(bnr, id);
    }
  }

  if (DEBUGLEVEL) msgtimer("InitGetRay");

  rep[1] = (long)listid;
  rep[2] = (long)listcl;
  rep[3] = nf_get_r2((GEN)bnf[7])? 0: un; /* != 0 iff nf is totally real */
  return rep;
}

/* compute the class of the prime ideal pr in cl(bnr) using dataray */
static GEN
GetRay(GEN bnr,  GEN dataray,  GEN pr, long prec)
{
  long av = avma, N, n, bd, c;
  GEN id, tid, t2, u, alpha, p1, cl, listid, listcl, nf, cond;

  if (!dataray)
    return isprincipalray(bnr, pr);

  listid =  (GEN)dataray[1];
  listcl =  (GEN)dataray[2];
  cond   =  gmael3(bnr, 2, 1, 1);
  bd     =  lg(listid) - 1;
  nf     =  gmael(bnr, 1, 7);
  N      =  degpol(nf[1]);

  if (dataray[3])
    t2 = gmael(nf, 5, 4);
  else
    t2 = gmael(nf, 5, 3);

  id  = prime_to_ideal(nf, pr);
  tid = qf_base_change(t2, id, 1);

  if (dataray[3])
    u = lllgramint(tid);
  else
    u = lllgramintern(tid,100,1,prec);

  if (!u) return gerepileupto(av, isprincipalray(bnr, id));

  c = 1; alpha = NULL;
  for (c=1; c<=N; c++)
  {
    p1 = gmul(id, (GEN)u[c]);
    if (gcmp1(gcoeff(idealadd(nf, p1, cond), 1, 1))) { alpha = p1; break; }
  }
  if (!alpha)
    return gerepileupto(av, isprincipalray(bnr, pr));

  id = idealdivexact(nf, alpha, id);

  n = itos(det(id));
  if (n > bd)
    cl = isprincipalray(bnr, id);
  else
  {
    cl = NULL;
    c  = 1;
    p1 = (GEN)listid[n];
    while (!cl)
    {
      if (gegal((GEN)p1[c], id))
	cl = gmael(listcl, n, c);
      c++;
    }
  }

  return gerepileupto(av, gsub(isprincipalray(bnr, alpha), cl));
}

/* correct the coefficients an(chi) according with diff(chi) in place */
static void
CorrectCoeff(GEN dtcr, int** an, int** reduc, long nmax, long dg)
{
  long lg, av1, j, p, q, limk, k, l, av = avma;
  int ***an2, **an1, *c, *c2;
  GEN chi, bnrc, diff, ray, ki, ki2, pr, degs;

  chi  =  (GEN)dtcr[8];
  bnrc =  (GEN)dtcr[3];
  diff =  (GEN)dtcr[6];
  lg   =  lg(diff) - 1;
  if (!lg) return;

  if (DEBUGLEVEL > 2) fprintferr("diff(chi) = %Z", diff);

  degs = cgetg(2, t_VECSMALL); degs[1] = dg;
  an2 = InitMatAn(1, nmax, degs, 0); an1 = an2[1];
  c = (int*)new_chunk(dg);
  av1 = avma;

  for (j = 1; j <= lg; j++)
  {
    for (k = 0; k <= nmax; k++)
      for (l = 0; l < dg; l++) an1[k][l] = an[k][l];

    pr  = (GEN)diff[j];
    ray = isprincipalray(bnrc, pr);
    ki  = ComputeImagebyChar(chi, ray, 1);
    ki2 = gcopy(ki);

    q = p = itos(powgi((GEN)pr[1], (GEN)pr[4]));
    limk = nmax / q;

    while (q <= nmax)
    {
      if (gcmp1(ki2)) c2 = NULL; else { Polmod2Coeff(c,ki2, dg); c2 = c; }
      for(k = 1; k <= limk; k++)
        AddMulCoeff(an[k*q], c2, an1[k], reduc, dg);

      q *= p; limk /= p;
      ki2 = gmul(ki2, ki);
    }
    avma = av1;
  }
  FreeMat(an2); avma = av;
}

/* compute the coefficients an in the general case */
static int***
ComputeCoeff(GEN dataCR, long nmax, long prec)
{
  long cl, i, j, av = avma, av2, np, q, q1, limk, k, id, cpt = 10, dg, Bq;
  int ***matan, ***reduc, ***matan2, *c2;
  GEN c, degs, tabprem, bnf, pr, cond, ray, ki, ki2, prime, npg, bnr, dataray;
  byteptr dp = diffptr;

  bnr  =  gmael(dataCR, 1, 4);
  bnf  =  (GEN)bnr[1];
  cond =  gmael3(bnr, 2, 1, 1);
  cl   =  lg(dataCR) - 1;

  dataray = InitGetRay(bnr, nmax);

  degs = GetDeg(dataCR);
  matan  = InitMatAn(cl, nmax, degs, 0);
  matan2 = InitMatAn(cl, nmax, degs, 0);
  reduc  = InitReduction(dataCR, degs);
  c = cgetg(cl + 1, t_VEC);
  for (i = 1; i <= cl; i++)
    c[i] = (long)new_chunk(degs[i]);

  if (DEBUGLEVEL > 1) fprintferr("p = ");

  prime = stoi(2); dp++;
  av2 = avma;
  while (*dp && (prime[2] <= nmax))
  {
    tabprem = primedec(bnf, prime);
    for (j = 1; j < lg(tabprem); j++)
    {
      pr  = (GEN)tabprem[j];
      npg = powgi((GEN)pr[1], (GEN)pr[4]);
      if (is_bigint(npg) || (np=npg[2]) > nmax
                         || idealval(bnf, cond, pr)) continue;

      CopyCoeff(matan, matan2, cl, nmax, degs);
      ray = GetRay(bnr, dataray, pr, prec);
      ki  = chiideal(dataCR, ray, 1);
      ki2 = dummycopy(ki);

      Bq = nmax/np;
      for (q1 = 1; q1 <= Bq; q1 *= np) 
      {
	q = q1*np; 
        limk = nmax / q;
        for (id = 1; id <= cl; id++)
        {
          dg = degs[id];
          if (gcmp1((GEN)ki2[id]))
            c2 = NULL;
          else
          {
            c2 = (int*)c[id];
            Polmod2Coeff(c2, (GEN)ki2[id], dg);
          }
          for (k = 1; k <= limk; k++)
            AddMulCoeff(matan[id][k*q], c2, matan2[id][k], reduc[id], dg);
          ki2[id] = lmul((GEN)ki2[id], (GEN)ki[id]);
        }
      }
    }
    avma = av2;
    prime[2] += (*dp++);
    if (!*dp) err(primer1);

    if (DEBUGLEVEL > 1 && prime[2] > cpt)
      { fprintferr("%ld ", prime[2]); cpt += 10; }
  }
  if (DEBUGLEVEL > 1) fprintferr("\n");

  for (i = 1; i <= cl; i++)
    CorrectCoeff((GEN)dataCR[i], matan[i], reduc[i], nmax, degs[i]);

  FreeMat(matan2); FreeMat(reduc);
  avma = av; return matan;
}

/********************************************************************/
/*              5th part: compute L-functions at s=1                */
/********************************************************************/

/* if flag != 0, prec means decimal digits */
static GEN
get_limx(long r1, long r2, long prec, GEN *pteps, long flag)
{
  GEN eps, a, r, c0, A0, limx, Pi = mppi(prec), N, p1;

  N = addss(r1, 2*r2);
  a = gmul(gpow(gdeux, gsubgs(gdiv(stoi(r1), N), 1), DEFAULTPREC), N); 
  r = addss(r1, r2);

  if (flag)
    *pteps = eps = gmul2n(gpowgs(dbltor(10.), -prec), -1);
  else
    *pteps = eps = gmul2n(gpowgs(dbltor(10.), (long)(-(prec-2) / pariK1)), -1);

  c0 = gpow(gmul2n(Pi, 1), gdiv(subis(r, 1), gdeux), DEFAULTPREC);
  c0 = gmul(c0, gdiv(gdeux, N));
  c0 = gmul(c0, gpow(gdeux, gmul(gdiv(stoi(r1), gdeux),
				 gsubsg(1, gdiv(addis(r, 1), N))), 
		     DEFAULTPREC));

  A0 = glog(gdiv(gmul2n(c0, 1), eps), DEFAULTPREC);

  limx = gpow(gdiv(a, A0), gdiv(N, gdeux), DEFAULTPREC);
  p1   = gsub(glog(A0, DEFAULTPREC), glog(a, DEFAULTPREC));
  p1   = gmul(gmul(p1, N), addis(r, 1));
  p1   = gdiv(p1, gmul2n(gadd(gmul2n(A0, 1), addis(r, 1)), 1));
  limx = gmul(limx, gaddgs(p1, 1));

  return limx;
}

static long
GetBoundN0(GEN C,  long r1, long r2,  long prec, long flag)
{
  long av = avma;
  GEN eps, limx = get_limx(r1, r2, prec, &eps, flag);

  limx = gfloor(gdiv(C, limx));
  if (is_bigint(limx))
    err(talker, "Too many coefficients (%Z) needed in GetST: computation impossible", limx);

  avma = av; return itos(limx);
}

static long
GetBoundi0(long r1, long r2,  long prec)
{
  long av = avma, imin, i0, itest;
  GEN ftest, borneps, eps, limx = get_limx(r1, r2, prec, &eps, 0);
  GEN Pi = mppi(DEFAULTPREC);

  borneps = gmul(gmul2n(gun, r2), gpow(Pi, gdiv(subss(r2, 3), gdeux), 
				       DEFAULTPREC));
  borneps = gdiv(gmul(borneps, gpowgs(stoi(5), r1)), eps);
  borneps = gdiv(borneps, gsqrt(limx, DEFAULTPREC));

  imin = 1;
  i0   = 1400;
  while(i0 - imin >= 4)
  {
    itest = (i0 + imin) >> 1;

    ftest = gpowgs(limx, itest);
    ftest = gmul(ftest, gpowgs(mpfactr(itest / 2, DEFAULTPREC), r1));
    ftest = gmul(ftest, gpowgs(mpfactr(itest, DEFAULTPREC), r2));

    if(gcmp(ftest, borneps) >= 0)
      i0 = itest;
    else
      imin = itest;
  }
  avma = av;

  return (i0 / 2) * 2;
}

/* compute the principal part at the integers s = 0, -1, -2, ..., -i0
   of Gamma((s+1)/2)^a Gamma(s/2)^b Gamma(s)^c / (s - z) with z = 0 and 1 */
/* NOTE: this is surely not the best way to do this, but it's fast enough! */
static GEN
ppgamma(long a, long b, long c, long i0, long prec)
{
  GEN cst, gamun, gamdm, an, bn, cn_evn, cn_odd, x, x2, aij, p1, cf, p2;
  long i, j, r, av = avma;

  r = max(b + c + 1, a + c);

  aij = cgetg(i0 + 1, t_VEC);
  for (i = 1; i <= i0; i++)
  {
    aij[i] = lgetg(3, t_VEC);
    mael(aij, i, 1) = lgetg(r + 1, t_VEC);
    mael(aij, i, 2) = lgetg(r + 1, t_VEC);
  }

  x   = polx[0];
  x2  = gmul2n(x, -1);

  /* Euler gamma constant, values of Riemann zeta functions at
     positive integers */
  cst = cgetg(r + 2, t_VEC);
  cst[1] = (long)mpeuler(prec);
  for (i = 2; i <= r + 1; i++)
    cst[i] = (long)gzeta(stoi(i), prec);

  /* the expansion of log(Gamma(s)) at s = 1 */
  gamun = cgetg(r + 2, t_SER);
  gamun[1] = evalsigne(1) | evalvalp(0) | evalvarn(0);
  gamun[2] = zero;
  for (i = 1; i <= r; i++)
  {
    gamun[i + 2] = ldivgs((GEN)cst[i], i);
    if (i%2) gamun[i + 2] = lneg((GEN)gamun[i + 2]);
  }

  /* the expansion of log(Gamma(s)) at s = 1/2 */
  gamdm = cgetg(r + 2, t_SER);
  gamdm[1] = evalsigne(1) | evalvalp(0) | evalvarn(0);
  gamdm[2] = (long)mplog(gsqrt(mppi(prec), prec));
  gamdm[3] = lneg(gadd(gmul2n(glog(gdeux, prec), 1), (GEN)cst[1]));
  for (i = 2; i <= r; i++)
    gamdm[i + 2] = lmul((GEN)gamun[i + 2], subis(shifti(gun, i), 1));

  gamun = gexp(gamun, prec);
  gamdm = gexp(gamdm, prec);

  /* We simplify to get one of the following two expressions */

  /* Case 1 (b > a): sqrt{Pi}^a 2^{a - as} Gamma(s/2)^{b-a} Gamma(s)^{a + c} */
  if (b > a)
  {
    cf = gpui(mppi(prec), gmul2n(stoi(a), -1), prec);

    /* an is the expansion of Gamma(x)^{a+c} */
    an = gpowgs(gdiv(gamun, x), a + c);

    /* bn is the expansion of 2^{a - ax} */
    bn = gpowgs(gpow(gdeux, gsubsg(1, x), prec), a);

    /* cn_evn is the expansion of Gamma(x/2)^{b-a} */
    cn_evn = gpowgs(gdiv(gsubst(gamun, 0, x2), x2), b - a);

    /* cn_odd is the expansion of Gamma((x-1)/2)^{b-a} */
    cn_odd = gpowgs(gdiv(gsubst(gamdm, 0, x2), gsub(x2, ghalf)), b - a);

    for (i = 0; i < i0/2; i++)
    {
      p1 = gmul(cf, gmul(an, gmul(bn, cn_evn)));

      p2 = gdiv(p1, gsubgs(x, 2*i));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 1, 1, j) = (long)polcoeff0(p2, -j, 0);

      p2 = gdiv(p1, gsubgs(x, 2*i + 1));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 1, 2, j) = (long)polcoeff0(p2, -j, 0);

      /* an(x-s-1) = an(x-s) / (x-s-1)^{a+c} */
      an = gdiv(an, gpowgs(gsubgs(x, 2*i + 1), a + c));

      /* bn(x-s-1) = 2^a bn(x-s) */
      bn = gmul2n(bn, a);

      /* cn_evn(x-s-2) = cn_evn(x-s) / (x/2 - (s+2)/2)^{b-a} */
      cn_evn = gdiv(cn_evn, gpowgs(gsubgs(x2, i + 1), b - a));

      p1 = gmul(cf, gmul(an, gmul(bn, cn_odd)));

      p2 = gdiv(p1, gsubgs(x, 2*i + 1));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 2, 1, j) = (long)polcoeff0(p2, -j, 0);

      p2 = gdiv(p1, gsubgs(x, 2*i + 2));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 2, 2, j) = (long)polcoeff0(p2, -j, 0);

      an = gdiv(an, gpowgs(gsubgs(x, 2*i + 2), a + c));
      bn = gmul2n(bn, a);

      /* cn_odd(x-s-2) = cn_odd(x-s) / (x/2 - (s+2)/2)^{b-a} */
      cn_odd = gdiv(cn_odd, gpowgs(gsub(x2, gaddgs(ghalf, i + 1)), b - a));
    }
  }
  else
  /* Case 2 (b <= a): sqrt{Pi}^b 2^{b - bs} Gamma((s+1)/2)^{a-b}
                                                         Gamma(s)^{b + c) */
  {
    cf = gpui(mppi(prec), gmul2n(stoi(b), -1), prec);

    /* an is the expansion of Gamma(x)^{b+c} */
    an = gpowgs(gdiv(gamun, x), b + c);

    /* bn is the expansion of 2^{b - bx} */
    bn = gpowgs(gpow(gdeux, gsubsg(1, x), prec), b);

    /* cn_evn is the expansion of Gamma((x+1)/2)^{a-b} */
    cn_evn = gpowgs(gsubst(gamdm, 0, x2), a - b);

    /* cn_odd is the expansion of Gamma(x/2)^{a-b} */
    cn_odd = gpowgs(gdiv(gsubst(gamun, 0, x2), x2), a - b);

    for (i = 0; i < i0/2; i++)
    {
      p1 = gmul(cf, gmul(an, gmul(bn, cn_evn)));

      p2 = gdiv(p1, gsubgs(x, 2*i));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 1, 1, j) = (long)polcoeff0(p2, -j, 0);

      p2 = gdiv(p1, gsubgs(x, 2*i + 1));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 1, 2, j) = (long)polcoeff0(p2, -j, 0);

      /* an(x-s-1) = an(x-s) / (x-s-1)^{b+c} */
      an = gdiv(an, gpowgs(gsubgs(x, 2*i + 1), b + c));

      /* bn(x-s-1) = 2^b bn(x-s) */
      bn = gmul2n(bn, b);

      /* cn_evn(x-s-2) = cn_evn(x-s) / (x/2 - (s+1)/2)^{a-b} */
      cn_evn = gdiv(cn_evn, gpowgs(gsub(x2, gaddgs(ghalf, i)), a - b));

      p1 = gmul(cf, gmul(an, gmul(bn, cn_odd)));

      p2 = gdiv(p1, gsubgs(x, 2*i + 1));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 2, 1, j) = (long)polcoeff0(p2, -j, 0);

      p2 = gdiv(p1, gsubgs(x, 2*i + 2));
      for (j = 1; j <= r; j++)
	mael3(aij, 2*i + 2, 2, j) = (long)polcoeff0(p2, -j, 0);

      an = gdiv(an, gpowgs(gsubgs(x, 2*i + 2), b + c));
      bn = gmul2n(bn, b);

      /* cn_odd(x-s-2) = cn_odd(x-s) / (x/2 - (s+1)/2)^{a-b} */
      cn_odd = gdiv(cn_odd, gpowgs(gsubgs(x2, i + 1), a - b));
    }
  }

  return gerepilecopy(av, aij);
}

static GEN
GetST(GEN dataCR, long prec)
{
  GEN N0, CC, bnr, bnf, nf, Pi, racpi, C, cond, aij, B, S, T, csurn, lncsurn;
  GEN degs, p1, p2, nsurc, an, rep, powlncn, powracpi;
  long i, j, k, n, av = avma, av1, av2, hk, fj, id, prec2, i0, nmax;
  long a, b, c, rc1, rc2, r, r1, r2;
  int ***matan;

  if (DEBUGLEVEL) timer2();
  bnr   = gmael(dataCR, 1, 4);
  bnf   = checkbnf(bnr);
  nf    = checknf(bnf);
  r1    = nf_get_r1(nf);
  r2    = nf_get_r2(nf);
  hk    = lg(dataCR) - 1;
  prec2 = ((prec - 2)<<1) + EXTRA_PREC;

  Pi    = mppi(prec2);
  racpi = gsqrt(Pi, prec2);

  C    = cgetg(hk + 1, t_VEC);
  cond = cgetg(hk + 1, t_VEC);
  N0 = new_chunk(hk+1);
  CC = new_chunk(hk+1);
  nmax = 0;
  for (i = 1; i <= hk; i++)
  {
    C[i]    = mael(dataCR, i, 2);

    p1 = cgetg(3, t_VEC);
    p1[1] = mael(dataCR, i, 7);
    p1[2] = mael(dataCR, i, 9);
    cond[i] = (long)p1;

    N0[i] = GetBoundN0((GEN)C[i], r1, r2, prec, 0);
    if (nmax < N0[i]) nmax  = N0[i];
  }

  if ((ulong)nmax > maxprime())
    err(talker, "Not enough precomputed primes (need all primes up to %ld)", nmax);

  i0 = GetBoundi0(r1, r2, prec);

  if(DEBUGLEVEL > 1) fprintferr("nmax = %ld and i0 = %ld\n", nmax, i0);

  matan = ComputeCoeff(dataCR, nmax, prec);
  degs = GetDeg(dataCR);
  if (DEBUGLEVEL) msgtimer("Compute an");

  p1 = cgetg(3, t_COMPLEX);
  p1[1] = lgetr(prec2);
  p1[2] = lgetr(prec2);
  gaffect(gzero, p1);

  S = cgetg(hk + 1, t_VEC);
  T = cgetg(hk + 1, t_VEC);
  for (id = 1; id <= hk; id++)
  {
    S[id] = lcopy(p1);
    T[id] = lcopy(p1);
    for (k = 1; k < id; k++)
      if (gegal((GEN)cond[id], (GEN)cond[k])) break;
    CC[id] = k;
  }

  powracpi = cgetg(hk + 1, t_VEC);
  for (j = 1; j <= hk; j++)
    powracpi[j] = (long)gpow(racpi, gmael3(dataCR, j, 9, 2), prec2);

  av1 = avma;
  if (DEBUGLEVEL > 1) fprintferr("n = ");

  for (id = 1; id <= hk; id++)
  {
    if (CC[id] != id) continue;
    p2 = gmael(dataCR, id, 9);
    a  = itos((GEN)p2[1]);
    b  = itos((GEN)p2[2]);
    c  = itos((GEN)p2[3]);
    aij = ppgamma(a, b, c, i0, prec2);
    rc1 = a + c;
    rc2 = b + c; r = max(rc2 + 1, rc1);
    av2 = avma;

    for (n = 1; n <= N0[id]; n++)
    {
      if (DEBUGLEVEL > 1 && n%100 == 0) fprintferr("%ld ", n);

      for (k = 1; k <= hk; k++)
        if (CC[k] == id && !IsZero(matan[k][n], degs[k])) break;
      if (k > hk) continue;

      csurn = gdivgs((GEN)C[id], n);
      nsurc = ginv(csurn);

      B = cgetg(r + 1, t_VEC);
      lncsurn = glog(csurn, prec2);
      powlncn = gun;
      fj = 1;

      p1 = gzero;
      p2 = gzero;
      for (j = 1; j <= r; j++)
      {
        if (j > 2) fj = fj * (j - 1);

        B[j] = ldivgs(powlncn, fj);
        p1 = gadd(p1, gmul((GEN)B[j], gmael3(aij, i0, 2, j)));
        p2 = gadd(p2, gmul((GEN)B[j], gmael3(aij, i0, 1, j)));

        powlncn = gmul(powlncn, lncsurn);
      }
      for (i = i0 - 1; i > 1; i--)
      {
        p1 = gmul(p1, nsurc);
        p2 = gmul(p2, nsurc);
        for (j = i%2? rc2: rc1; j; j--)
        {
          p1 = gadd(p1, gmul((GEN)B[j], gmael3(aij, i, 2, j)));
          p2 = gadd(p2, gmul((GEN)B[j], gmael3(aij, i, 1, j)));
        }
      }
      p1 = gmul(p1, nsurc);
      p2 = gmul(p2, nsurc);
      for (j = 1; j <= r; j++)
      {
        p1 = gadd(p1, gmul((GEN)B[j], gmael3(aij, 1, 2, j)));
        p2 = gadd(p2, gmul((GEN)B[j], gmael3(aij, 1, 1, j)));
      }

      p1 = gadd(p1, gmul(csurn, (GEN)powracpi[id]));

      for (j = 1; j <= hk; j++)
        if (CC[j] == id &&
            (an = EvalCoeff(gmael3(dataCR, j, 5, 2), matan[j][n], degs[j])))
        {
          gaffect(gadd((GEN)S[j], gmul(p1, an)),        (GEN)S[j]);
          gaffect(gadd((GEN)T[j], gmul(p2, gconj(an))), (GEN)T[j]);
        }
      avma = av2;
    }
    avma = av1;
  }
  FreeMat(matan);

  if (DEBUGLEVEL > 1) fprintferr("\n");
  if (DEBUGLEVEL) msgtimer("Compute S&T");

  rep = cgetg(3, t_VEC);
  rep[1] = (long)S;
  rep[2] = (long)T;
  return gerepilecopy(av, rep);
}

/* Given datachi, S(chi) and T(chi), return L(1, chi) if fl = 1,
   or [r(chi), c(chi)] where r(chi) is the rank of chi and c(chi)
   is given by L(s, chi) = c(chi).s^r(chi) at s = 0 if fl = 0.
   if fl2 = 1, adjust the value to get L_S(s, chi). */
static GEN
GetValue(GEN datachi, GEN S, GEN T, long fl, long fl2, long prec)
{
  GEN W, A, q, b, c, d, rchi, cf, VL, rep, racpi, nS, nT;
  long av = avma;

  racpi = gsqrt(mppi(prec), prec);
  W = ComputeArtinNumber(datachi, 0, prec);
  A = ComputeAChi(datachi, fl, prec);

  d = gmael(datachi, 8, 3);

  q = gmael(datachi, 9, 1);
  b = gmael(datachi, 9, 2);
  c = gmael(datachi, 9, 3);

  rchi = addii(b, c);

  if (!fl)
  {
    cf = gmul2n(gpow(racpi, q, 0), itos(b));

    nS = gdiv(gconj(S), cf);
    nT = gdiv(gconj(T), cf);

    /* VL = W(chi).S(conj(chi)) + T(chi)) / (sqrt(Pi)^q 2^{r1 - q}) */
    VL = gadd(gmul(W, nS), nT);
    if (cmpis(d, 3) < 0) VL = greal(VL);

    if (fl2)
    {
      VL = gmul((GEN)A[2], VL);
      rchi = gadd(rchi, (GEN)A[1]);
    }

    rep = cgetg(3, t_VEC);
    rep[1] = (long)rchi;
    rep[2] = (long)VL;
  }
  else
  {
    cf = gmul((GEN)datachi[2], gpow(racpi, b, 0));

    /* VL = S(chi) + W(chi).T(chi)) / (C(chi) sqrt(Pi)^{r1 - q}) */
    rep = gdiv(gadd(S, gmul(W, T)), cf);
    if (cmpis(d, 3) < 0) rep = greal(rep);

    if (fl2) rep = gmul(A, rep);
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
TestOne(GEN plg,  GEN beta,  GEN B,  long v,  long G,  long N)
{
  long j;
  GEN p1;

  p1 = gsub(beta, (GEN)plg[v]);
  if (expo(p1) >= G) return 0;

  for (j = 1; j <= N; j++)
    if (j != v)
    {
      p1 = gabs((GEN)plg[j], DEFAULTPREC);
      if (gcmp(p1, B) > 0) return 0;
    }
  return 1;
}

/* Using linear dependance relations */
static GEN
RecCoeff2(GEN nf,  GEN beta,  GEN B,  long v,  long prec)
{
  long N, G, i, bacmin, bacmax, av = avma, av2;
  GEN vec, velt, p1, cand, M, plg, pol, cand2;

  M    = gmael(nf, 5, 1);
  pol  = (GEN)nf[1];
  N    = degpol(pol);
  vec  = gtrans((GEN)gtrans(M)[v]);
  velt = (GEN)nf[7];

  G = min( - 20, - bit_accuracy(prec) >> 4);

  p1 = cgetg(2, t_VEC);

  p1[1] = lneg(beta);
  vec = concat(p1, vec);

  p1[1] = zero;
  velt = concat(p1, velt);

  bacmin = (long)(.225 * bit_accuracy(prec));
  bacmax = (long)(.315 * bit_accuracy(prec));

  av2 = avma;

  for (i = bacmax; i >= bacmin; i--)
  {
    p1 = lindep2(vec, i);

    if (signe((GEN)p1[1]))
    {
      p1    = ground(gdiv(p1, (GEN)p1[1]));
      cand  = gmodulcp(gmul(velt, gtrans(p1)), pol);
      cand2 = algtobasis(nf, cand);
      plg   = gmul(M, cand2);

      if (TestOne(plg, beta, B, v, G, N))
        return gerepilecopy(av, cand);
    }
    avma = av2;
  }
  return NULL;
}

GEN
chk_reccoeff_init(FP_chk_fun *chk, GEN nf, GEN gram, GEN mat, long *ptprec)
{
  GEN data = chk->data;
  data[6] = (long)mat;
  chk->data = data;
  return (GEN)data[7];
}

GEN 
chk_reccoeff(GEN data, GEN x)
{
  GEN M = (GEN)data[0], beta = (GEN)data[1], B = (GEN)data[2];
  long v = data[3], G = data[4], N = data[5], j;
  GEN U = (GEN)data[6], p1 = gmul(U, x), sol, plg;  

  if (!gcmp1((GEN)p1[1])) return NULL;
  
  sol = cgetg(N + 1, t_COL);
  for (j = 1; j <= N; j++)
    sol[j] = lmulii((GEN)p1[1], (GEN)p1[j + 1]);
  plg = gmul(M, sol);
  
  if (TestOne(plg, beta, B, v, G, N)) return sol;
  return NULL;
}

GEN
chk_reccoeff_post(GEN data, GEN res)
{
  return res;
}

/* Using Cohen's method */
static GEN
RecCoeff3(GEN nf, GEN beta, GEN B, long v, long prec)
{
  GEN A, M, nB, cand, p1, B2, C2, data, tB, beta2, eps, nf2, Bd;
  long N, G, i, j, k, l, ct = 0, av = avma, prec2;
  FP_chk_fun *chk;

  N   = degpol(nf[1]);
  G   = min(-10, -bit_accuracy(prec) >> 4);
  eps = gpowgs(stoi(10), min(-8, (G >> 1)));
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

  data = new_chunk(8);
  data[0] = (long)M; 
  data[1] = (long)beta;
  data[2] = (long)B;
  data[3] = v;
  data[4] = G;
  data[5] = N;
  data[6] = (long)NULL;
  data[7] = (long)nB;

  chk = (FP_chk_fun*)new_chunk(sizeof(FP_chk_fun));
  chk->f         = &chk_reccoeff;
  chk->f_init    = &chk_reccoeff_init;
  chk->f_post    = &chk_reccoeff_post;
  chk->data      = data;
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

/* Attempts to find a polynomial with coefficients in nf such that 
   its coefficients are close to those of pol at the place v and 
   less than B at all the other places */
GEN
RecCoeff(GEN nf,  GEN pol,  long v, long prec)
{
  long av = avma, j, md, G, cl = degpol(pol);
  GEN p1, beta;

  /* if precision(pol) is too low, abort */
  for (j = 2; j <= cl+1; j++)
  {
    p1 = (GEN)pol[j];
    G  = bit_accuracy(gprecision(p1)) - gexpo(p1);
    if (G < 34) { avma = av; return NULL; }
  }

  md = cl/2;
  pol = dummycopy(pol);

  for (j = 1; j <= cl; j++)
  {
    /* start with the coefficients in the middle,
       since they are the harder to recognize! */
    long cf = md + (j%2? j/2: -j/2);
    GEN bound = binome(stoi(cl), cf);

    bound = shifti(bound, cl - cf);

    if (DEBUGLEVEL > 1) fprintferr("In RecCoeff with cf = %ld and B = %Z\n", 
				   cf, bound);

    beta = greal((GEN)pol[cf+2]);
    p1 = RecCoeff2(nf, beta, bound, v, prec);
    if (!p1)
    {
      p1 = RecCoeff3(nf, beta, bound, v, prec);
      if (!p1) return NULL;
    }
    pol[cf+2] = (long)p1;
  }
  pol[cl+2] = un;
  return gerepilecopy(av, pol);
}

/*******************************************************************/
/*******************************************************************/
/*                                                                 */
/*                   Computation of class fields of                */
/*	          real quadratic fields using Stark units          */
/*                                                                 */
/*******************************************************************/
/*******************************************************************/

/* compute the coefficients an for the quadratic case */
static int***
computean(GEN dtcr,  long nmax, long prec)
{
  long i, j, cl, q, cp, al, v1, v2, v, fldiv, av, av1;
  int ***matan, ***reduc;
  GEN bnf, ideal, dk, degs, idno, p1, prime, chi, qg, chi1, chi2;
  GEN chi11, chi12, bnr, pr, pr1, pr2, xray, xray1, xray2, dataray;
  byteptr dp = diffptr;

  av = avma;

  cl = lg(dtcr) - 1;
  degs = GetDeg(dtcr);

  matan = InitMatAn(cl, nmax, degs, 1);
  reduc = InitReduction(dtcr, degs);

  bnr = gmael(dtcr, 1, 4); bnf = (GEN)bnr[1];
  dataray = InitGetRay(bnr, nmax);

  ideal = gmael3(bnr, 2, 1, 1);
  idno  = idealnorm(bnf, ideal);
  dk = gmael(bnf, 7, 3);

  prime = stoi(2);
  dp++;

  av1 = avma;

  chi = chi1 = chi2 = NULL; /* gcc -Wall */
  while (*dp && prime[2] <= nmax)
  {
    qg = prime;
    al = 1;

    switch (krogs(dk, prime[2]))
    {
      /* prime is inert */
      case -1:
	fldiv = divise(idno, prime);

	if (!fldiv)
	{
	  xray = GetRay(bnr, dataray, prime, prec);
	  chi  = chiideal(dtcr, xray, 1);
	  chi1 = dummycopy(chi);
	}

       	while(cmpis(qg, nmax) <= 0)
	{
	  q = qg[2];

	  for (cp = 1, i = q; i <= nmax; i += q, cp++)
	    if(cp % prime[2])
	    {
	      if (fldiv || al%2)
                for (j = 1; j <= cl; j++)
		  _0toCoeff(matan[j][i], degs[j]);
	      else
		for (j = 1; j <= cl; j++)
		  MulPolmodCoeff((GEN)chi[j], matan[j][i], reduc[j], degs[j]);
	    }

	  qg = mulsi(q, prime);
	  al++;

	  if (al%2 && !fldiv)
	    for (j = 1; j <= cl; j++)
	      chi[j] = lmul((GEN)chi[j], (GEN)chi1[j]);
 	}
	break;

    /* prime is ramified */
    case 0:
      fldiv = divise(idno, prime);

      if (!fldiv)
      {
	pr   = (GEN)primedec(bnf, prime)[1];
	xray = GetRay(bnr, dataray, pr, prec);
	chi  = chiideal(dtcr, xray, 1);
	chi2 = dummycopy(chi);
      }

      while(cmpis(qg, nmax) <= 0)
      {
	q = qg[2];

	for (cp = 1, i = q; i <= nmax; i += q, cp++)
	  if(cp % prime[2])
          {
	    if (fldiv)
	      for(j = 1; j <= cl; j++)
		_0toCoeff(matan[j][i], degs[j]);
	    else
            {
	      for(j = 1; j <= cl; j++)
		MulPolmodCoeff((GEN)chi[j], matan[j][i], reduc[j], degs[j]);
	    }
	  }

	qg = mulsi(q, prime);
	al++;

	if (cmpis(qg, nmax) <= 0 && !fldiv)
	  for (j = 1; j <= cl; j++)
	    chi[j] = lmul((GEN)chi[j], (GEN)chi2[j]);
      }
      break;

    /* prime is split */
    default: /* case 1: */
      p1  = primedec(bnf, prime);
      pr1 = (GEN)p1[1];
      pr2 = (GEN)p1[2];
      v1 = idealval(bnf, ideal, pr1);
      v2 = idealval(bnf, ideal, pr2);

      if (v1 + v2 == 0)
      {
	xray1 = GetRay(bnr, dataray, pr1, prec);
	xray2 = GetRay(bnr, dataray, pr2, prec);
	chi11 = chiideal(dtcr, xray1, 1);
	chi12 = chiideal(dtcr, xray2, 1);

	chi1 = gadd(chi11, chi12);
	chi2 = dummycopy(chi12);

	while(cmpis(qg, nmax) <= 0)
        {
	  q = qg[2];

	  for (cp = 1, i = q; i <= nmax; i += q, cp++)
	    if(cp % prime[2])
	      for(j = 1; j <= cl; j++)
		MulPolmodCoeff((GEN)chi1[j], matan[j][i], reduc[j], degs[j]);

	  qg = mulsi(q, prime);
	  al++;

	  if(cmpis(qg, nmax) <= 0)
	    for (j = 1; j <= cl; j++)
            {
	      chi2[j] = lmul((GEN)chi2[j], (GEN)chi12[j]);
	      chi1[j] = ladd((GEN)chi2[j], gmul((GEN)chi1[j], (GEN)chi11[j]));
	    }
	}
      }
      else
      {
	if (v1) { v  = v2; pr = pr2; } else { v  = v1; pr = pr1; }

	if (v == 0)
        {
	  xray = GetRay(bnr, dataray, pr, prec);
	  chi1 = chiideal(dtcr, xray, 1);
	  chi  = gcopy(chi1);
	}

	while(cmpis(qg, nmax) <= 0)
        {
	  q = qg[2];
	  for (cp = 1, i = q; i <= nmax; i += q, cp++)
	    if(cp % prime[2])
            {
	      if (v)
		for (j = 1; j <= cl; j++)
		  _0toCoeff(matan[j][i], degs[j]);
	      else
		for (j = 1; j <= cl; j++)
		  MulPolmodCoeff((GEN)chi[j], matan[j][i], reduc[j], degs[j]);
	    }

	  qg = mulii(qg, prime);
	  al++;

	  if (!v && (cmpis(qg, nmax) <= 0))
	    for (j = 1; j <= cl; j++)
	      chi[j] = lmul((GEN)chi[j], (GEN)chi1[j]);
	}
      }
      break;
    }

    prime[2] += (*dp++);

    avma = av1;
  }

  for (i = 1; i <= cl; i++)
    CorrectCoeff((GEN)dtcr[i], matan[i], reduc[i], nmax, degs[i]);

  FreeMat(reduc);
  avma = av; return matan;
}

/* compute S and T for the quadratic case */
static GEN
QuadGetST(GEN data, long prec)
{
  long av = avma, n, j, nmax, cl, av1, av2, k;
  int ***matan;
  GEN nn, C, p1, p2, c2, cexp, cn, v, veclprime2, veclprime1;
  GEN dtcr, cond, rep, an, cf, degs, veint1;

  dtcr     = (GEN)data[5];
  cl       = lg(dtcr) - 1;
  degs     = GetDeg(dtcr);

  cf   = gmul2n(mpsqrt(mppi(prec)), 1);
  C    = cgetg(cl+1, t_VEC);
  cond = cgetg(cl+1, t_VEC);
  c2   = cgetg(cl + 1, t_VEC);
  nn   = new_chunk(cl+1);
  nmax = 0;
  for (j = 1; j <= cl; j++)
  {
    C[j]    = mael(dtcr, j, 2);
    c2[j]   = ldivsg(2, (GEN)C[j]);
    cond[j] = mael(dtcr, j, 7);
    nn[j]   = (long)(bit_accuracy(prec) * gtodouble((GEN)C[j]) * 0.35);

    nmax  = max(nmax, nn[j]);
  }

  if (nmax >= VERYBIGINT)
    err(talker, "Too many coefficients (%ld) in QuadGetST: computation impossible", nmax);

  if (DEBUGLEVEL >= 2)
    fprintferr("nmax = %ld\n", nmax);

  /* compute the coefficients */
  matan = computean(dtcr, nmax, prec);
  if (DEBUGLEVEL) msgtimer("Compute an");

  /* allocate memory for the answer */
  rep = cgetg(3, t_VEC);

  /* allocate memory for veclprime1 */
  veclprime1 = cgetg(cl + 1, t_VEC);
  for (j = 1; j <= cl; j++)
  {
    v = cgetg(3, t_COMPLEX);
    v[1] = lgetr(prec);
    v[2] = lgetr(prec); gaffect(gzero, v);
    veclprime1[j] = (long)v;
  }

  av1 = avma;
  cn = cgetr(prec);
  p1 = gmul2n(cf, -1);

  /* compute veclprime1 */
  for (j = 1; j <= cl; j++)
  {
    long n0 = 0;
    p2 = gmael3(dtcr, j, 5, 2);
    cexp = gexp(gneg_i((GEN)c2[j]), prec);
    av2 = avma; affsr(1, cn); v = (GEN)veclprime1[j];
    for (n = 1; n <= nn[j]; n++)
      if ( (an = EvalCoeff(p2, matan[j][n], degs[j])) )
      {
        affrr(gmul(cn, gpowgs(cexp, n - n0)), cn);
        n0 = n;
        gaffect(gadd(v, gmul(divrs(cn,n), an)), v);
        avma = av2;
      }
    gaffect(gmul(p1, gmul(v, (GEN)C[j])), v);
    avma = av2;
  }
  avma = av1;
  rep[1] = (long)veclprime1;
  if (DEBUGLEVEL) msgtimer("Compute V1");

  /* allocate memory for veclprime2 */
  veclprime2 = cgetg(cl + 1, t_VEC);
  for (j = 1; j <= cl; j++)
  {
    v = cgetg(3, t_COMPLEX);
    v[1] = lgetr(prec);
    v[2] = lgetr(prec); gaffect(gzero, v);
    veclprime2[j] = (long)v;
  }

  /* compute f1(C/n) */
  av1 = avma;

  veint1 = cgetg(cl + 1, t_VEC);
  for (j = 1; j <= cl; j++)
  {
    p1 = NULL;
    for (k = 1; k < j; k++)
      if (gegal((GEN)cond[j], (GEN)cond[k])) { p1 = (GEN)veint1[k]; break; }
    if (p1 == NULL)
    {
      p1 = veceint1((GEN)c2[j], stoi(nn[j]), prec);
      veint1[j] = (long)p1;
    }
    av2 = avma; p2 = gmael3(dtcr, j, 5, 2);
    v = (GEN)veclprime2[j];
    for (n = 1; n <= nn[j]; n++)
      if ( (an = EvalCoeff(p2, matan[j][n], degs[j])) )
      {
        gaffect(gadd(v, gmul((GEN)p1[n], an)), v);
        avma = av2;
      }
    gaffect(gmul(cf, gconj(v)), v);
    avma = av2;
  }
  avma = av1;
  rep[2] = (long)veclprime2;
  if (DEBUGLEVEL) msgtimer("Compute V2");
  FreeMat(matan); return gerepileupto(av, rep);
}

#if 0
/* recover a quadratic integer by an exhaustive search */
static GEN
recbeta2(GEN nf,  GEN beta,  GEN bound,  long prec)
{
  long av = avma, av2, tetpil, i, range, G, e, m;
  GEN om, om1, om2, dom, p1, a, b, rom, bom2, *gptr[2];

  G = min( - 20, - bit_accuracy(prec) >> 4);

  if (DEBUGLEVEL > 3)
    fprintferr("\n Precision needed: %ld", G);

  om  = gmael(nf, 7, 2);
  rom = (GEN)nf[6];
  om1 = poleval(om, (GEN)rom[2]);
  om2 = poleval(om, (GEN)rom[1]);
  dom = subrr(om1, om2);

  /* b will run from b to b + range */
  p1 = gaddgs(gmul2n(gceil(absr(divir(bound, dom))), 1), 2);
  range = VERYBIGINT;
  if (cmpis(p1,  VERYBIGINT) < 0)
    range = itos(p1);

  av2 = avma;

  b = gdiv(gsub(bound, beta), dom);
  if (gsigne(b) < 0)
    b = subis(negi(gcvtoi(gneg_i(b), &e)), 1);
  else
    b=gcvtoi(b, &e);

  if (e > 0)  /* precision is lost in truncation */
  {
    avma = av;
    return NULL;
  }

  bom2 = mulir(b, om2);
  m = 0;

  for (i = 0; i <= range; i++)
  {
    /* for every b,  we construct a and test it */
    a = grndtoi(gsub(beta, bom2), &e);

    if (e > 0) /* precision is lost in truncation */
    {
      avma = av;
      return NULL;
    }

    p1 = gsub(mpadd(a, bom2),  beta);

    if ((DEBUGLEVEL > 3) && (expo(p1)<m))
    {
      m = expo(p1);
      fprintferr("\n Precision found: %ld", expo(p1));
    }

    if (gcmp0(p1) || (expo(p1) < G))  /* result found */
    {
      p1 = gadd(a, gmul(b, om));
      return gerepileupto(av, gmodulcp(p1, (GEN)nf[1]));
    }

    tetpil = avma;

    b    = gaddgs(b, 1);
    bom2 = gadd(bom2, om2);

    gptr[0] = &b;
    gptr[1] = &bom2;
    gerepilemanysp(av2, tetpil, gptr, 2);
  }

  /* if it fails... */
  return NULL;
}
#endif

/* return 1 if the absolute polynomial pol (over Q) defines the
   Hilbert class field of the real quadratic field bnf */
int
define_hilbert(GEN bnf, GEN pol)
{
  long cl;
  GEN dk;

  cl = itos(gmael3(bnf, 8, 1, 1));
  dk = gmael(bnf, 7, 3);
 
  if (degpol(pol) == cl)
    if ((cl%2) || !egalii(discf(pol), gpowgs(dk,cl>>1))) return 1;

  return 0;
}

/* let polrel define Hk/k,  find L/Q such that Hk=Lk and L and k are
   disjoint */
static GEN
makescind(GEN bnf, GEN polabs, long cl, long prec)
{
  long av = avma, i, l;
  GEN pol, p1, nf2, dabs, dk, bas;

  /* check the result (a little): signature and discriminant */
  bas = allbase4(polabs,0,&dabs,NULL);
  dk  = gmael(bnf,7,3);
  if (!egalii(dabs, gpowgs(dk,cl)) || sturm(polabs) != 2*cl)
    err(bugparier, "quadhilbert");

  /* attempt to find the subfields using polred */
  p1 = cgetg(3,t_VEC); p1[1]=(long)polabs; p1[2]=(long)bas;
  pol = polredfirstpol(p1, (prec<<1) - 2, &define_hilbert, bnf);
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
      if ((cl%2) || !gegal(sqri(discf(pol)), (GEN)nf2[3])) break;
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
  GEN disc, quat, x2, pol, div, d;

  hk   = itos(gmael3(bnf, 8, 1, 1));
  disc = gmael(bnf, 7, 3);
  quat = stoi(4);
  x2   = gsqr(polx[0]);

  if (gcmp0(modii(disc, quat))) disc = divii(disc, quat);

  div = divisors(disc);
  c = 1;
  l = 0;
  pol = NULL; /* gcc -Wall */

  while(l < hk)
  {
    c++;
    d = (GEN)div[c];

    if (gcmp1(modii(d, quat)))
    {
      if (!l)
	pol = gsub(x2, d);
      else
	pol=(GEN)compositum(pol, gsub(x2, d))[1];

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
  int ***matan;
  GEN p0, p1, p2, S, T, polrelnum, polrel, Lp, W, A, veczeta, sig, valchi;
  GEN degs, ro, C, Cmax, dataCR, cond1, L1, *gptr[2], an, Pi;

  N     = degpol(nf[1]);
  r1    = nf_get_r1(nf);
  r2    = (N - r1)>>1;
  cond1 = gmael4(data, 1, 2, 1, 2);
  Pi    = mppi(newprec);

  v = 1;
  while(gcmp1((GEN)cond1[v])) v++;

LABDOUB:

  av = avma;

  dataCR = (GEN)data[5];
  cl = lg(dataCR)-1;
  degs = GetDeg(dataCR);
  h  = itos(gmul2n(det((GEN)data[2]), -1));

  if (flag >= 0)
  {
    /* compute S,T differently if nf is quadratic */
    if (N == 2)
      p1 = QuadGetST(data, newprec);
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
  {
    /* compute a crude approximation of the result */
    C = cgetg(cl + 1, t_VEC);
    for (i = 1; i <= cl; i++) C[i] = mael(dataCR, i, 2);
    Cmax = vecmax(C);

    n = GetBoundN0(Cmax, r1, r2, newprec, 0);
    if (n > bnd) n = bnd;
    if (DEBUGLEVEL) fprintferr("nmax in QuickPol: %ld \n", n);

    matan = ComputeCoeff(dataCR, n, newprec);

    p0 = cgetg(3, t_COMPLEX);
    p0[1] = lgetr(newprec); affsr(0, (GEN)p0[1]);
    p0[2] = lgetr(newprec); affsr(0, (GEN)p0[2]);

    L1 = cgetg(cl+1, t_VEC);
    /* we use the formulae L(1) = sum (an / n) */
    for (i = 1; i <= cl; i++)
    {
      av2 = avma;
      p1 = p0; p2 = gmael3(dataCR, i, 5, 2);
      for (j = 1; j <= n; j++)
	if ( (an = EvalCoeff(p2, matan[i][j], degs[i])) )
          p1 = gadd(p1, gdivgs(an, j));
      L1[i] = lpileupto(av2, p1);
    }
    FreeMat(matan);

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
    valchi = chiideal(dataCR, sig, 0);

    for (j = 1; j <= cl; j++)
    {
      GEN p2 = greal(gmul((GEN)Lp[j], (GEN)valchi[j]));
      if (!gegal(gdeux, gmael3(dataCR, j, 5, 3)))
        p2 = gmul2n(p2, 1); /* character not real */
      z = gadd(z,p2);
    }
    veczeta[i] = ldivgs(z, 2 * h);
  }
  if (DEBUGLEVEL >= 2) fprintferr("zetavalues = %Z\n", veczeta);

  if ((flag >=0) && (flag <= 3)) sq = 0;

  ro = cgetg(h+1, t_VEC); /* roots */
  
  for (;;)
  {
    if (!sq && (DEBUGLEVEL > 1))
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
    data[5] = (long)CharNewPrec((GEN)data[5], nf, newprec);

    gptr[0] = &data;
    gptr[1] = &nf;
    gerepilemany(av, gptr, 2);

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

GEN
bnrstark(GEN bnr,  GEN subgroup,  long flag,  long prec)
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
  if (!varn(gmael(bnf, 7, 1)))
    err(talker, "main variable in bnrstark must not be x");

  if (cmpis(gmael3(bnf, 7, 2, 1), N))
    err(talker, "not a totally real ground base field in bnrstark");

  /* check the subgroup */
  if (gcmp0(subgroup))
    subgroup = Mcyc;
  else
  {
    p1 = gauss(subgroup, Mcyc);
    if (!gcmp1(denom(p1)))
      err(talker, "incorrect subgroup in bnrstark");
  }

  /* compute bnr(conductor) */
  p1       = conductor(bnr, subgroup, 2);
  bnr      = (GEN)p1[2];
  subgroup = (GEN)p1[3];

  /* check the class field */
  if (!gcmp0(gmael3(bnr, 2, 1, 2)))
    err(talker, "not a totally real class field in bnrstark");

  cl = itos(det(subgroup));
  if (cl == 1) return polx[0];

  timer2();

  /* find a suitable extension N */
  dataS = InitQuotient(bnr, subgroup);
  data  = FindModulus(dataS, 1, &newprec, prec, bnd);

  if (newprec > prec)
  {
    if (DEBUGLEVEL >= 2) fprintferr("new precision: %ld\n", newprec);  
    nf = nfnewprec(nf, newprec);
  }

  return gerepileupto(av, AllStark(data, nf, flag, newprec));
}

/* For each character of Cl(bnr)/sbgrp, compute L(1, chi) (or equivalently 
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
bnrL1(GEN bnr, GEN sbgrp, long flag, long prec)
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

  if ((flag < 0) || (flag > 8))
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
  if (gcmp0(sbgrp))
    sbgrp = Mcyc;
  else
  {
    if (lg(sbgrp) != ncc+1) 
      err(talker, "incorrect subgroup in bnrL1");
    p1 = gauss(sbgrp, Mcyc);
    if (!gcmp1(denom(p1)))
      err(talker, "incorrect subgroup in bnrL1");
  }

  cl = labs(itos(det(sbgrp)));
  Qt = InitQuotient0(Mcyc, sbgrp);
  lq = lg((GEN)Qt[2]) - 1;

  /* compute all the characters */
  allCR = FindEltofGroup(cl, (GEN)Qt[2]);
  

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
