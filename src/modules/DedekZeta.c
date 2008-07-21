/* $Id: base1.c 10459 2008-07-13 16:24:07Z kb $

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
/*                     DEDEKIND ZETA FUNCTION                      */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
static GEN
dirzetak0(GEN nf, long N0)
{
  GEN vect, c, c2, pol = gel(nf,1), index = gel(nf,4);
  pari_sp av = avma;
  long i, k, limk, lx;
  ulong q, p;
  byteptr d = diffptr;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};

  (void)evallg(N0+1);
  c  = cgetalloc(t_VECSMALL, N0+1);
  c2 = cgetalloc(t_VECSMALL, N0+1);
  c2[1] = c[1] = 1; for (i=2; i<=N0; i++) c[i] = 0;

  maxprime_check((ulong)N0);
  court[2] = 0;
  while (court[2] <= N0)
  {
    NEXT_PRIME_VIADIFF(court[2], d);
    if (umodiu(index, court[2])) /* court does not divide index */
      { vect = gel(FpX_degfact(pol,court),1); lx = lg(vect); }
    else
    {
      GEN p1 = idealprimedec(nf,court); lx = lg(p1); vect = cgetg(lx,t_VECSMALL);
      for (i=1; i<lx; i++) vect[i] = itou( gmael(p1,i,4) );
    }
    for (i=1; i<lx; i++)
    {
      GEN N = powiu(court, vect[i]); /* N = court^f */
      if (cmpiu(N, N0) > 0) break;

      q = p = (ulong)N[2]; limk = N0/q;
      for (k=2; k <= N0; k++) c2[k] = c[k];
      while (q <= (ulong)N0)
      {
	LOCAL_HIREMAINDER;
	for (k=1; k<=limk; k++) c2[k*q] += c[k];
	q = mulll(q, p); if (hiremainder) break;
	limk /= p;
      }
      N = c; c = c2; c2 = N;
    }
    avma = av;
  }
  pari_free(c2); return c;
}

GEN
dirzetak(GEN nf, GEN b)
{
  GEN z, c;
  long n;

  if (typ(b) != t_INT) pari_err(talker,"not an integer type in dirzetak");
  if (signe(b) <= 0) return cgetg(1,t_VEC);
  nf = checknf(nf);
  n = itos_or_0(b); if (!n) pari_err(talker,"too many terms in dirzetak");
  c = dirzetak0(nf, n);
  z = vecsmall_to_vec(c); pari_free(c); return z;
}

GEN
zeta_get_limx(long r1, long r2, long bit)
{
  pari_sp av = avma;
  GEN p1, p2, c0, c1, A0;
  long r = r1 + r2, N = r + r2;

  /* c1 = N 2^(-2r2 / N) */
  c1 = mulrs(powrfrac(real2n(1, DEFAULTPREC), -2*r2, N), N);

  p1 = gpowgs(Pi2n(1, DEFAULTPREC), r - 1);
  p2 = gmul2n(mpmul(powuu(N,r), p1), -r2);
  c0 = sqrtr( mpdiv(p2, gpowgs(c1, r+1)) );

  A0 = logr_abs( gmul2n(c0, bit) ); p2 = divrr(A0, c1);
  p1 = divrr(mulsr(N*(r+1), logr_abs(p2)), addsr(2*(r+1), gmul2n(A0,2)));
  return gerepileuptoleaf(av, divrr(addrs(p1, 1), powrshalf(p2, N)));
}
/* N_0 = floor( C_K / limx ) */
long
zeta_get_N0(GEN C,  GEN limx)
{
  long e;
  pari_sp av = avma;
  GEN z = gcvtoi(gdiv(C, limx), &e); /* avoid truncation error */
  if (e >= 0 || is_bigint(z))
    pari_err(talker, "need %Ps coefficients in initzeta: computation impossible", z);
  if (DEBUGLEVEL>1) fprintferr("\ninitzeta: N0 = %Ps\n", z);
  avma = av; return itos(z);
}

static long
get_i0(long r1, long r2, GEN B, GEN limx)
{
  long imin = 1, imax   = 1400;
  while(imax - imin >= 4)
  {
    long i = (imax + imin) >> 1;
    GEN t = gpowgs(limx, i);
    t = gmul(t, gpowgs(mpfactr(i/2, DEFAULTPREC), r1));
    t = gmul(t, gpowgs(mpfactr(i  , DEFAULTPREC), r2));
    if (gcmp(t, B) >= 0) imax = i; else imin = i;
  }
  return imax & ~1; /* make it even */
}

/* assume limx = zeta_get_limx(r1, r2, bit) */
long
zeta_get_i0(long r1, long r2, long bit, GEN limx)
{
  pari_sp av = avma;
  GEN B = gmul(sqrtr( gdiv(gpowgs(mppi(DEFAULTPREC), r2-3), limx) ),
	       gmul2n(powuu(5, r1), bit + r2));
  long i0 = get_i0(r1, r2, B, limx);
  if (DEBUGLEVEL>1) { fprintferr("i0 = %ld\n",i0); flusherr(); }
  avma = av; return i0;
}

GEN
initzeta(GEN pol, long prec)
{
  GEN nfz, nf, gr1, gr2, gru, p1, p2, cst, coef, bnf = checkbnf_i(pol);
  GEN limx, resi,zet,C,coeflog,racpi,aij,tabj,colzero, tabcstn, tabcstni;
  GEN c_even, ck_even, c_odd, ck_odd, serie_even, serie_odd, serie_exp, Pi;
  long N0, i0, r1, r2, r, R, N, i, j, k, n, bit = bit_accuracy(prec) + 6;
  pari_sp av, av2;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  stackzone *zone, *zone0, *zone1;

  /*************** residue & constants ***************/
  nfz = cgetg(10,t_VEC);
  if (bnf && nf_get_prec(bnf) >= prec)
    bnf = gcopy(bnf);
  else
    bnf = bnfinit0(pol, 2, NULL, prec);
  prec = (prec<<1) - 2;
  Pi = mppi(prec); racpi = sqrtr(Pi);

  /* class number & regulator */
  nf = gel(bnf,7); N = degpol(nf[1]);
  nf_get_sign(nf, &r1, &r2);
  gr1 = gmael(nf,2,1); gr2 = gmael(nf,2,2);
  r = r1 + r2; R = r+2;
  av = avma; p1 = gel(bnf,8); p2 = mpmul(shifti(gmael(p1,1,1),r1), gel(p1,2));
  resi = gerepileupto(av, gdiv(p2, gmael(p1,4,1)));

  av = avma;
  p1 = sqrtr_abs(itor(gel(nf,3), prec));
  p2 = gmul2n(gpowgs(racpi,N), r2);
  cst = gerepileuptoleaf(av, divrr(p1,p2));

  /* N0, i0 */
  limx = zeta_get_limx(r1, r2, bit);
  N0 = zeta_get_N0(cst, limx);
  i0 = zeta_get_i0(r1, r2, bit + 4, limx);

  /* Array of i/cst (i=1..N0) */
  av = avma; i = prec*N0;
  zone  = switch_stack(NULL,i + 2*(N0+1) + 6*prec);
  zone1 = switch_stack(NULL,2*i);
  zone0 = switch_stack(NULL,2*i);
  (void)switch_stack(zone,1);
  tabcstn  = cgetg(N0+1,t_VEC);
  tabcstni = cgetg(N0+1,t_VEC);
  p1 = ginv(cst);
  for (i=1; i<=N0; i++) gel(tabcstni,i) = gel(tabcstn,i) = mulsr(i,p1);
  (void)switch_stack(zone,0);

  /********** compute a(i,j) **********/
  zet = cgetg(R,t_VEC); gel(zet,1) = mpeuler(prec);
  for (i=2; i<R; i++) gel(zet,i) = szeta(i, prec);

  aij = cgetg(i0+1,t_VEC);
  for (i=1; i<=i0; i++) gel(aij,i) = cgetg(R,t_VEC);

  c_even = real2n(r1, prec);
  c_odd = gmul(c_even, gpowgs(racpi,r1));
  if (r&1) c_odd = gneg_i(c_odd);
  ck_even = cgetg(R,t_VEC); ck_odd = cgetg(r2+2,t_VEC);
  for (k=1; k<R; k++)
  {
    GEN t = mulri(gel(zet,k), addis(shifti(gr2, k), r1));
    setexpo(t, expo(t)-k);
    if (k&1) togglesign(t);
    gel(ck_even,k) = t;
  }
  gru = utoipos(r);
  for (k = 1; k <= r2+1; k++)
  {
    GEN t = mulri(gel(zet,k), subis(shifti(gru,k), r1));
    setexpo(t, expo(t)-k);
    if (k&1) togglesign(t);
    gel(ck_odd,k) = addsr(r, t);
  }
  if (r1) gel(ck_odd,1) = subrr(gel(ck_odd,1), mulsr(r1, mplog2(prec)));
  serie_even = cgetg(r+3,t_SER);
  serie_odd = cgetg(r2+3,t_SER);
  serie_even[1] = serie_odd[1] = evalsigne(1)|_evalvalp(1);
  i = 0;
  while (i < i0/2)
  {
    for (k=1; k<R; k++) gel(serie_even,k+1) = gdivgs(gel(ck_even,k),k);
    serie_exp = gmul(c_even, gexp(serie_even,0));
    p1 = gel(aij,2*i+1);
    for (j=1; j<R; j++) p1[j] = serie_exp[r+3-j];

    for (k=1; k<=r2+1; k++) gel(serie_odd,k+1) = gdivgs(gel(ck_odd,k),k);
    serie_exp = gmul(c_odd, gexp(serie_odd,0));
    p1 = gel(aij,2*i+2);
    for (j=1; j<=r2+1; j++) p1[j] = serie_exp[r2+3-j];
    for (   ; j<R; j++) gel(p1,j) = gen_0;
    i++;

    c_even = gdiv(c_even,gmul(powuu(i,r),powuu(2*i-1,r2)));
    c_odd  = gdiv(c_odd, gmul(powuu(i,r2),powuu(2*i+1,r)));
    c_even = gmul2n(c_even,-r2);
    c_odd  = gmul2n(c_odd,r1-r2);
    if (r1 & 1) { c_even = gneg_i(c_even); c_odd = gneg_i(c_odd); }
    p1 = gr2; p2 = gru;
    for (k=1; k<R; k++)
    {
      p1 = gdivgs(p1,2*i-1); p2 = gdivgs(p2,2*i);
      gel(ck_even,k) = gadd(gel(ck_even,k), gadd(p1,p2));
    }
    p1 = gru; p2 = gr2;
    for (k=1; k<=r2+1; k++)
    {
      p1 = gdivgs(p1,2*i+1); p2 = gdivgs(p2,2*i);
      gel(ck_odd,k) = gadd(gel(ck_odd,k), gadd(p1,p2));
    }
  }
  aij = gerepilecopy(av, aij);
  if (DEBUGLEVEL>1) msgtimer("a(i,j)");
  p1=cgetg(5,t_VEC);
  gel(p1,1) = stoi(r1);
  gel(p1,2) = stoi(r2);
  gel(p1,3) = stoi(i0);
  gel(p1,4) = bnf;
  gel(nfz,1) = p1;
  gel(nfz,2) = resi;
  gel(nfz,5) = cst;
  gel(nfz,6) = glog(cst,prec);
  gel(nfz,7) = aij;

  /************* Calcul du nombre d'ideaux de norme donnee *************/
  coef = dirzetak0(nf,N0); tabj = cgetg(N0+1,t_MAT);
  if (DEBUGLEVEL>1) msgtimer("coef");
  colzero = zerocol(r+1);
  for (i=1; i<=N0; i++)
    if (coef[i])
    {
      GEN t = cgetg(r+2,t_COL);
      p1 = logr_abs(gel(tabcstn,i)); togglesign(p1);
      gel(t,1) = utoi(coef[i]);
      gel(t,2) = mulur(coef[i], p1);
      for (j=2; j<=r; j++)
      {
	pari_sp av2 = avma;
	gel(t,j+1) = gerepileuptoleaf(av2, divru(mulrr(gel(t,j), p1), j));
      }
      gel(tabj,i) = t; /* tabj[n,j] = coef(n)*ln(c/n)^(j-1)/(j-1)! */
    }
    else
      gel(tabj,i) = colzero;
  if (DEBUGLEVEL>1) msgtimer("a(n)");

  coeflog=cgetg(N0+1,t_VEC); gel(coeflog,1) = gen_0;
  for (i=2; i<=N0; i++)
    if (coef[i])
    {
      court[2] = i; p1 = glog(court,prec);
      setsigne(p1, -1); gel(coeflog,i) = p1;
    }
    else gel(coeflog,i) = gen_0;
  if (DEBUGLEVEL>1) msgtimer("log(n)");

  gel(nfz,3) = tabj;
  gel(nfz,8) = vecsmall_copy(coef);
  gel(nfz,9) = coeflog;

  /******************** Calcul des coefficients Cik ********************/
  C = cgetg(r+1,t_MAT);
  for (k=1; k<=r; k++) gel(C,k) = cgetg(i0+1,t_COL);
  av2 = avma;
  for (i=1; i<=i0; i++)
  {
    GEN aiji = gel(aij,i);
    stackzone *z;
    for (k=1; k<=r; k++)
    {
      p1 = NULL;
      for (n=1; n<=N0; n++)
	if (coef[n])
	{
	  GEN tabjn = gel(tabj,n), p2 = mpmul(gel(aiji,1+k), gel(tabjn,1));
	  for (j=2; j<=r-k+1; j++)
	    p2 = mpadd(p2, mpmul(gel(aiji,j+k), gel(tabjn,j)));
	  if (i > 1) p2 = mpmul(p2, gel(tabcstni,n));
	  p1 = p1? mpadd(p1,p2): p2;
	}
      togglesign(p1);
      gcoeff(C,i,k) = gerepileuptoleaf(av2,p1);
      av2 = avma;
    }
    if (i > 1 && i < i0) {
      /* use a parallel stack */
      z = i&1? zone1: zone0;
      (void)switch_stack(z, 1);
      for (n=1; n<=N0; n++)
	if (coef[n]) gel(tabcstni,n) = mpmul(gel(tabcstni,n),gel(tabcstn,n));
      /* come back */
      (void)switch_stack(z, 0);
    }
  }
  gel(nfz,4) = C;
  if (DEBUGLEVEL>1) msgtimer("Cik");
  pari_free((void*)zone); pari_free((void*)zone1); pari_free((void*)zone0);
  pari_free((void*)coef); return nfz;
}

GEN
gzetakall(GEN nfz, GEN s, long flag, long prec2)
{
  GEN resi,C,cst,cstlog,coeflog,cs,coef;
  GEN lambd,gammas,gammaunmoins,gammas2,gammaunmoins2,var1,var2;
  GEN smoinun,unmoins,gexpro,gar,val,valm,valk,valkm;
  long ts = typ(s), r1,r2,ru,i0,i,j,k,N0,sl,prec,bigprec;
  pari_sp av = avma;

  if (typ(nfz)!=t_VEC || lg(nfz)!=10 || typ(nfz[1]) != t_VEC)
    pari_err(talker,"not a zeta number field in zetakall");
  if (! is_intreal_t(ts) && ts != t_COMPLEX && ts != t_FRAC)
    pari_err(typeer,"gzetakall");
  resi=gel(nfz,2); C=gel(nfz,4); cst=gel(nfz,5);
  cstlog=gel(nfz,6); coef=gel(nfz,8); coeflog=gel(nfz,9);
  r1 = itos(gmael(nfz,1,1));
  r2 = itos(gmael(nfz,1,2)); ru = r1+r2;
  i0 = itos(gmael(nfz,1,3)); N0 = lg(coef)-1;
  bigprec = precision(cst); prec = prec2+1;

  if (ts==t_COMPLEX && gcmp0(imag_i(s))) { s=real_i(s); ts = typ(s); }
  if (ts==t_REAL && !signe(gfrac(s))) { s=mptrunc(s); ts = t_INT; }
  if (ts==t_INT)
  {
    sl = itos(s);
    if (sl==1) pari_err(talker,"s = 1 is a pole (gzetakall)");
    if (sl==0)
    {
      avma = av;
      if (flag) pari_err(talker,"s = 0 is a pole (gzetakall)");
      if (ru == 1) return r1? mkfrac(gen_m1, gen_2): gneg(resi);
      return gen_0;
    }
    if (sl<0 && (r2 || !odd(sl)))
    {
      if (!flag) return gen_0;
      s = subsi(1,s); sl = 1-sl;
    }
    unmoins=subsi(1,s);
    lambd = gdiv(resi, mulis(s,sl-1));
    gammas2=ggamma(gmul2n(s,-1),prec);
    gar=gpowgs(gammas2,r1);
    cs=gexp(gmul(cstlog,s),prec);
    val=s; valm=unmoins;
    if (sl < 0) /* r2 = 0 && odd(sl) */
    {
      gammaunmoins2 = ggamma(gmul2n(unmoins,-1),prec);
      var1 = var2 = gen_1;
      for (i=2; i<=N0; i++)
	if (coef[i])
	{
	  gexpro=gexp(gmul(gel(coeflog,i),s),bigprec);
	  var1 = gadd(var1,gmulsg(coef[i],gexpro));
	  var2 = gadd(var2,gdivsg(coef[i],gmulsg(i,gexpro)));
	}
      lambd=gadd(lambd,gmul(gmul(var1,cs),gar));
      lambd=gadd(lambd,gmul(gmul(var2,gdiv(cst,cs)),
			    gpowgs(gammaunmoins2,r1)));
      var1 = gen_0;
      for (i=1; i<=i0; i+=2)
      {
	valk  = val;
	valkm = valm;
	for (k=1; k<=ru; k++)
	{
	  GEN c = gcoeff(C,i,k);
	  var1 = mpadd(var1,mpdiv(c,valk )); valk  = mulii(val,valk);
	  var1 = mpadd(var1,mpdiv(c,valkm)); valkm = mulii(valm,valkm);
	}
	val  = addis(val, 2);
	valm = addis(valm,2);
      }
    }
    else
    {
      GEN tabj=gel(nfz,3), aij=gel(nfz,7);

      gar = gmul(gar,gpowgs(ggamma(s,prec),r2));
      var1=var2=gen_0;
      for (i=1; i<=N0; i++)
	if (coef[i])
	{
	  gexpro=gexp(gmul(gel(coeflog,i),s),bigprec);
	  var1 = gadd(var1,gmulsg(coef[i],gexpro));
	  if (sl <= i0)
	  {
	    GEN t=gen_0;
	    for (j=1; j<=ru+1; j++)
	      t = gadd(t, gmul(gmael(aij,sl,j), gmael(tabj,i,j)));
	    var2=gadd(var2,gdiv(t,gmulsg(i,gexpro)));
	  }
	}
      lambd=gadd(lambd,gmul(gmul(var1,cs),gar));
      lambd=gadd(lambd,gmul(var2,gdiv(cst,cs)));
      var1 = gen_0;
      for (i=1; i<=i0; i++)
      {
	valk  = val;
	valkm = valm;
	if (i == sl)
	  for (k=1; k<=ru; k++)
	  {
	    GEN c = gcoeff(C,i,k);
	    var1 = mpadd(var1,mpdiv(c,valk)); valk = mulii(val,valk);
	  }
	else
	for (k=1; k<=ru; k++)
	{
	    GEN c = gcoeff(C,i,k);
	    var1 = mpadd(var1,mpdiv(c,valk )); valk  = mulii(val,valk);
	    var1 = mpadd(var1,mpdiv(c,valkm)); valkm = mulii(valm,valkm);
	}
	val  = addis(val,1);
	valm = addis(valm,1);
      }
    }
  }
  else
  {
    GEN Pi = mppi(bigprec);
    if (ts == t_FRAC)
      s = gmul(s, real_1(bigprec));
    else
      s = gprec_w(s, bigprec);

    smoinun = gsubgs(s,1);
    unmoins = gneg(smoinun);
    lambd = gdiv(resi,gmul(s,smoinun));
    gammas = ggamma(s,prec);
    gammas2= ggamma(gmul2n(s,-1),prec);
    gar = gmul(gpowgs(gammas,r2),gpowgs(gammas2,r1));
    cs = gexp(gmul(cstlog,s),prec);
    var1 = gmul(Pi,s);
    gammaunmoins = gdiv(Pi, gmul(gsin(var1,prec),gammas));
    gammaunmoins2= gdiv(gmul(gmul(sqrtr(Pi),gpow(gen_2,smoinun,prec)),
			     gammas2),
			gmul(gcos(gmul2n(var1,-1),prec),gammas));
    var1 = var2 = gen_1;
    for (i=2; i<=N0; i++)
      if (coef[i])
      {
	gexpro = gexp(gmul(gel(coeflog,i),s),bigprec);
	var1 = gadd(var1,gmulsg(coef[i], gexpro));
	var2 = gadd(var2,gdivsg(coef[i], gmulsg(i,gexpro)));
      }
    lambd = gadd(lambd,gmul(gmul(var1,cs),gar));
    lambd = gadd(lambd,gmul(gmul(gmul(var2,gdiv(cst,cs)),
	 		         gpowgs(gammaunmoins,r2)),
			    gpowgs(gammaunmoins2,r1)));
    val  = s;
    valm = unmoins;
    var1 = gen_0;
    for (i=1; i<=i0; i++)
    {
      valk  = val;
      valkm = valm;
      for (k=1; k<=ru; k++)
      {
	GEN c = gcoeff(C,i,k);
	var1 = gadd(var1,gdiv(c,valk )); valk  = gmul(val, valk);
	var1 = gadd(var1,gdiv(c,valkm)); valkm = gmul(valm,valkm);
      }
      if (r2)
      {
	val  = gaddgs(val, 1);
	valm = gaddgs(valm,1);
      }
      else
      {
	val  = gaddgs(val, 2);
	valm = gaddgs(valm,2); i++;
      }
    }
  }
  lambd = gadd(lambd, var1);
  if (!flag) lambd = gdiv(lambd,gmul(gar,cs)); /* zetak */
  if (gprecision(lambd) > prec2) lambd = gprec_w(lambd, prec2);
  return gerepileupto(av, lambd);
}

GEN
gzetak(GEN nfz, GEN s, long prec) { return gzetakall(nfz,s,0,prec); }

GEN
glambdak(GEN nfz, GEN s, long prec) { return gzetakall(nfz,s,1,prec); }
