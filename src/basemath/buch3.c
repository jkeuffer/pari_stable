/*******************************************************************/
/*                                                                 */
/*                       RAY CLASS FIELDS                          */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "parinf.h"

GEN check_and_build_cycgen(GEN bnf);
GEN compute_class_number(GEN mit,GEN *met,GEN *u1,GEN *u2);
GEN gmul_mat_smallvec(GEN x, GEN y);
GEN ideleaddone_aux(GEN nf,GEN x,GEN ideal);
GEN logunitmatrix(GEN nf,GEN funits,GEN racunit,GEN bid);
GEN vconcat(GEN Q1, GEN Q2);

static GEN
get_full_rank(GEN nf, GEN v, GEN _0, GEN _1, GEN vecsign, GEN gen,
              long ngen, long rankmax)
{
  GEN v1,p1,alpha, bas=(GEN)nf[7], rac=(GEN)nf[6];
  long rankinit=lg(v)-1, N=lgef(nf[1])-3, va=varn(nf[1]);
  long limr,i,k,kk,r,rr;

  for (r=1,rr=3; ; r++,rr+=2)
  {
    p1 = gpuigs(stoi(rr),N);
    limr=(cmpis(p1,BIGINT)>1)? BIGINT: p1[2]; /* min(BIGINT,rr^N) */
    limr = (limr-1)>>1;
    for (k=rr;  k<=limr; k++)
    {
      long av1=avma;
      alpha = gzero;
      for (kk=k,i=1; i<=N; i++,kk/=rr)
      {
        long lambda = (kk+r)%rr - r;
        if (lambda)
          alpha = gadd(alpha,gmulsg(lambda,(GEN)bas[i]));
      }
      for (i=1; i<=rankmax; i++)
	vecsign[i] = (gsigne(gsubst(alpha,va,(GEN)rac[i])) > 0)? (long)_0
                                                               : (long)_1;
      v1 = concatsp(v, vecsign);
      if (rank(v1) == rankinit) avma=av1;
      else
      {
	v=v1; rankinit++; ngen++;
        gen[ngen] = (long) alpha;
	if (rankinit == rankmax) return ginv(v); /* full rank */
      }
    }
  }
}

GEN
buchnarrow(GEN bnf)
{
  GEN nf,_0mod2,_1mod2,cyc,gen,v,matsign,arch,cycgen;
  GEN dataunit,p1,p2,p3,h,vecsign,clh,basecl,met,u1,u2;
  long R1,R,i,j,ngen,sizeh,t,lo,c;
  long av=avma,tetpil;

  if (typ(bnf)!=t_VEC || lg(bnf)!=11)
    err(talker,"not a big number field vector in buchnarrow");
  nf=checknf(bnf); R1=itos(gmael(nf,2,1));
  if (!R1) return gcopy(gmael(bnf,8,1));

  _1mod2=gmodulss(1,2); _0mod2=gmodulss(0,2);
  v=cgetg(R1+1,t_COL); vecsign=cgetg(R1+1,t_COL);
  for (i=1; i<=R1; i++) v[i]=(long)_1mod2;
  cyc=gmael3(bnf,8,1,2); gen=gmael3(bnf,8,1,3); ngen=lg(gen)-1;
  matsign=signunits(bnf); R=lg(matsign); dataunit=cgetg(R+1,t_MAT);
  for (j=1; j<R; j++)
  {
    p1=cgetg(R1+1,t_COL); dataunit[j]=(long)p1;
    for (i=1; i<=R1; i++)
      p1[i] = (signe(gcoeff(matsign,i,j)) > 0)? (long)_0mod2: (long)_1mod2;
  }
  dataunit[R]=(long)v; v=image(dataunit); t=lg(v)-1;
  sizeh=ngen+R1-t; p1 = cgetg(sizeh+1,t_COL);
  for (i=1; i<=ngen; i++) p1[i]=gen[i];
  gen = p1;
  if (t<R1)
    v = get_full_rank(nf,v,_0mod2,_1mod2,vecsign,gen,ngen,R1);

  h=cgetg(sizeh+1,t_MAT); arch = cgetg(R1+1,t_VEC);
  for (i=1; i<=R1; i++) arch[i]=un;
  cycgen = check_and_build_cycgen(bnf);
  for (j=1; j<=ngen; j++)
  {
    p1 = cgetg(sizeh+1,t_COL); h[j]=(long)p1;
    p2 = gmul(v,zsigne(nf,(GEN)cycgen[j],arch));
    for (i=1; i<=ngen;  i++) p1[i] = (i==j)? cyc[j]: zero;
    for (   ; i<=sizeh; i++) p1[i] = llift((GEN)p2[i+t-ngen]);
  }
  for (   ; j<=sizeh; j++)
  {
    p1 = cgetg(sizeh+1,t_COL); h[j]=(long)p1;
    for (i=1; i<=sizeh; i++) p1[i]=(i==j)?deux:zero;
  }
  clh=compute_class_number(h,&met,&u1,&u2);
  u1=reducemodmatrix(u1,h); lo=lg(met)-1; c=0;
  for (c=1; c<=lo; c++)
    if (gcmp1(gcoeff(met,c,c))) break;
  basecl=cgetg(c,t_VEC);
  for (j=1; j<c; j++)
  {
    p1=gcoeff(u1,1,j);
    p3=idealpow(nf,(GEN)gen[1],p1);
    if (signe(p1)<0) p3=numer(p3);
    for (i=2; i<=lo; i++)
    {
      p1=gcoeff(u1,i,j);
      if (signe(p1))
      {
	p3 = idealmul(nf,p3, idealpow(nf,(GEN)gen[i],p1));
        p1 = content(p3); if (!gcmp1(p1)) p3 = gdiv(p3,p1);
      }
    }
    basecl[j]=(long)p3;
  }
  tetpil=avma; v=cgetg(4,t_VEC);
  v[1]=lcopy(clh); setlg(met,c);
  v[2]=(long)mattodiagonal(met);
  v[3]=lcopy(basecl); return gerepile(av,tetpil,v);
}

GEN idealaddtoone_i(GEN nf, GEN x, GEN y);

/* given two coprime ideals x (integral) and id, compute alpha in x,
 * alpha = 1 mod (id), with x/alpha nearly reduced.
 */
static GEN
findalpha(GEN nf,GEN x,GEN id,long prec)
{
  GEN p1,idprod,y;
  GEN alp = idealaddtoone_i(nf,x,id);

  idprod = idealmullll(nf,x,id);
  y = lllgram(qf_base_change(gmael(nf,5,3),idprod,1), 2*prec-2);
  y = gmul(idprod, (GEN)y[1]); /* small vector in idprod */

  p1 = ground(element_div(nf,alp,y));
  alp = gsub(alp,element_mul(nf,p1,y));
  return gcmp0(alp)? y: alp;
}

static int
too_big(GEN nf, GEN bet)
{
  GEN x = gnorm(basistoalg(nf,bet));
  switch (typ(x))
  {
    case t_INT: return absi_cmp(x, gun);
    case t_FRAC: return absi_cmp((GEN)x[1], (GEN)x[2]);
  }
  err(bugparier, "wrong type in too_big");
  return 0; /* not reached */
}

static GEN
idealmodidele(GEN nf, GEN x, GEN ideal, GEN sarch, GEN arch, long prec)
{
  long av = avma,i,l;
  GEN p1,p2,alp,bet,b;

  nf=checknf(nf); alp=findalpha(nf,x,ideal,prec);
  p1=idealdiv(nf,alp,x);
  bet = element_div(nf,findalpha(nf,p1,ideal,prec),alp);
  if (too_big(nf,bet) > 0) { avma=av; return x; }
  p1=(GEN)sarch[2]; l=lg(p1);
  if (l > 1)
  {
    b=bet; p2=lift_intern(gmul((GEN)sarch[3],zsigne(nf,bet,arch)));
    for (i=1; i<l; i++)
    if (signe(p2[i])) bet = element_mul(nf,bet,(GEN)p1[i]);
    if (b != bet && too_big(nf,bet) > 0) { avma=av; return x; }
  }
  return idealmul(nf,bet,x);
}

static GEN
idealmulmodidele(GEN nf,GEN x,GEN y, GEN ideal,GEN sarch,GEN arch,long prec)
{
  return idealmodidele(nf,idealmul(nf,x,y),ideal,sarch,arch,prec);
}

/* assume n > 0 */
static GEN
idealpowmodidele(GEN nf,GEN x,GEN n, GEN ideal,GEN sarch,GEN arch,long prec)
{
  long i,m,av=avma;
  GEN y;
  ulong j;

  if (cmpis(n, 16) < 0)
  {
    if (gcmp1(n)) return x;
    x = idealpow(nf,x,n);
    x = idealmodidele(nf,x,ideal,sarch,arch,prec);
    return gerepileupto(av,x);
  }

  i = lgefint(n)-1; m=n[i]; j=HIGHBIT;
  while ((m&j)==0) j>>=1;
  y = x;
  for (j>>=1; j; j>>=1)
  {
    y = idealmul(nf,y,y);
    if (m&j) y = idealmul(nf,y,x);
    y = idealmodidele(nf,y,ideal,sarch,arch,prec);
  }
  for (i--; i>=2; i--)
    for (m=n[i],j=HIGHBIT; j; j>>=1)
    {
      y = idealmul(nf,y,y);
      if (m&j) y = idealmul(nf,y,x);
      y = idealmodidele(nf,y,ideal,sarch,arch,prec);
    }
  return gerepileupto(av,y);
}

static GEN
buchrayall(GEN bnf,GEN module,long flag,long prec)
{
  GEN nf,cyc,gen,genplus,fa2,sarch,hmatu,u,clg;
  GEN dataunit,p1,p2,h,clh,basecl,met,u1,u2,u1old,cycgen;
  GEN racunit,bigres,bid,resbid2,resbid3,x,y,funits,hmat,vecel;
  long RU,R3,i,j,ngen,lh,lo,c,av=avma,N;

  bnf = checkbnf(bnf); nf=checknf(bnf); bigres=(GEN)bnf[8];
  funits = check_units(bnf, "buchrayall");
  vecel = genplus = NULL; /* gcc -Wall */
  N=lgef(nf[1])-3;
  cyc=gmael(bigres,1,2);
  gen=gmael(bigres,1,3); ngen=lg(cyc)-1;

  bid = zidealstarinitall(nf,module,1);
  resbid2=gmael(bid,2,2);
  resbid3=gmael(bid,2,3);
  R3=lg(resbid2)-1; lh=ngen+R3;

  x = idealhermite(nf,module);
  if (R3 || flag & (nf_INIT|nf_GEN))
  {
    vecel = cgetg(ngen+1,t_VEC);
    for (j=1; j<=ngen; j++)
    {
      p1 = idealcoprime(nf,(GEN)gen[j],x);
      if (isnfscalar(p1)) p1 = (GEN)p1[1];
      vecel[j]=(long)p1;
    }
  }
  if (flag & nf_GEN)
  {
    genplus=cgetg(lh+1,t_VEC);
    for (j=1; j<=ngen; j++)
      genplus[j] = (long) idealmul(nf,(GEN)vecel[j],(GEN)gen[j]);
    for (  ; j<=lh; j++)
      genplus[j] = resbid3[j-ngen];
  }
  if (!R3)
  {
    if (!(flag & nf_GEN)) clg=cgetg(3,t_VEC);
    else
      { clg=cgetg(4,t_VEC); clg[3]=(long)genplus; }
    clg[1]=mael(bigres,1,1);
    clg[2]=(long)cyc;
    if (!(flag & nf_INIT)) return gerepileupto(av,gcopy(clg));
    y = cgetg(7,t_VEC);
    y[1]=lcopy(bnf);
    y[2]=lcopy(bid);
    y[3]=lcopy(vecel);
    y[4]=(long)idmat(ngen);
    y[5]=lcopy(clg); u=cgetg(3,t_VEC);
    y[6]=(long)u;
    u[1]=lgetg(1,t_MAT);
    u[2]=(long)idmat(lg(funits));
    return gerepileupto(av,y);
  }
  fa2=(GEN)bid[4]; sarch=(GEN)fa2[lg(fa2)-1];

  RU=lg(funits); dataunit=cgetg(RU+R3+1,t_MAT);
  racunit=gmael(bigres,4,2);
  dataunit[1] = (long)zideallog(nf,racunit,bid);
  for (j=2; j<=RU; j++)
    dataunit[j] = (long)zideallog(nf,(GEN)funits[j-1],bid);
  for (   ; j<=RU+R3; j++)
  {
    p1=cgetg(R3+1,t_COL); dataunit[j]=(long)p1;
    for (i=1; i<=R3; i++)
      p1[i] = (i==(j-RU))? resbid2[i]: zero;
  }
  h=cgetg(lh+1,t_MAT);
  cycgen = check_and_build_cycgen(bnf);
  for (j=1; j<=ngen; j++)
  {
    p1=cgetg(lh+1,t_COL); h[j]=(long)p1;
    p2 = element_mul(nf, (GEN)cycgen[j],
                         element_pow(nf,(GEN)vecel[j],(GEN)cyc[j]));
    p2 = zideallog(nf,p2,bid);
    for (i=1; i<=ngen;  i++) p1[i] = (i==j)? cyc[j]: zero;
    for (   ; i<=lh; i++) p1[i] = lnegi((GEN)p2[i-ngen]);
  }

  hmatu=hnfall(dataunit); hmat=(GEN)hmatu[1];
  for (   ; j<=lh; j++)
  {
    p1=cgetg(lh+1,t_COL); h[j]=(long)p1;
    for (i=1; i<=ngen; i++) p1[i]=zero;
    for (   ; i<=lh; i++) p1[i]=coeff(hmat,i-ngen,j-ngen);
  }
  clh = compute_class_number(h,&met,&u1,&u2);
  u1old=u1; lo=lg(met)-1;
  for (c=1; c<=lo; c++)
    if (gcmp1(gcoeff(met,c,c))) break;

  if (flag & nf_GEN)
  {
    GEN Id=idmat(N), arch=(GEN)module[2];
    u1 = reducemodmatrix(u1,h);
    basecl=cgetg(c,t_VEC);
    for (j=1; j<c; j++)
    {
      GEN *op, minus = Id, plus = Id;
      long av1 = avma, s;
      for (i=1; i<=lo; i++)
      {
	p1 = gcoeff(u1,i,j);
        if (!(s = signe(p1))) continue;

        if (s > 0) op = &plus; else { op = &minus; p1 = negi(p1); }
        p1 = idealpowmodidele(nf,(GEN)genplus[i],p1,x,sarch,arch,prec);
        *op = *op==Id? p1
                     : idealmulmodidele(nf,*op,p1,x,sarch,arch,prec);
      }
      if (minus == Id) p1 = plus;
      else
      {
        p2 = ideleaddone_aux(nf,minus,module);
        p1 = idealdivexact(nf,idealmul(nf,p2,plus),minus);
        p1 = idealmodidele(nf,p1,x,sarch,arch,prec);
      }
      basecl[j]=lpileupto(av1,p1);
    }
    clg=cgetg(4,t_VEC); clg[3]=lcopy(basecl);
  } else clg=cgetg(3,t_VEC);
  clg[1]=licopy(clh); setlg(met,c);
  clg[2]=(long)mattodiagonal(met);
  if (!(flag & nf_INIT)) return gerepileupto(av,clg);

  u2 = cgetg(R3+1,t_MAT);
  u1 = cgetg(RU+1,t_MAT); u = (GEN)hmatu[2];
  for (j=1; j<=RU; j++) { u1[j]=u[j]; setlg(u[j],RU+1); }
  u += RU;
  for (j=1; j<=R3; j++) { u2[j]=u[j]; setlg(u[j],RU+1); }
  p1=lllint(u1); p2=ginv(hmat);
  y=cgetg(7,t_VEC);
  y[1]=lcopy(bnf);
  y[2]=lcopy(bid);
  y[3]=lcopy(vecel);
  y[4]=linv(u1old);
  y[5]=lcopy(clg); u=cgetg(3,t_VEC);
  y[6]=(long)u;
  u[1]=lmul(u2,p2);
  u[2]=lmul(u1,p1);
  return gerepileupto(av,y);
}

GEN
buchrayinitgen(GEN bignf, GEN ideal,long prec)
{
  return buchrayall(bignf,ideal, nf_INIT | nf_GEN,prec);
}

GEN
buchrayinit(GEN bignf, GEN ideal,long prec)
{
  return buchrayall(bignf,ideal, nf_INIT,prec);
}

GEN
buchray(GEN bignf, GEN ideal,long prec)
{
  return buchrayall(bignf,ideal, nf_GEN,prec);
}

GEN
bnrclass0(GEN bignf, GEN ideal, long flag, long prec)
{
  switch(flag)
  {
    case 0: flag = nf_GEN; break;
    case 1: flag = nf_INIT; break;
    case 2: flag = nf_INIT | nf_GEN; break;
    default: err(flagerr,"bnrclass");
  }
  return buchrayall(bignf,ideal,flag,prec);
}

GEN
bnrinit0(GEN bignf, GEN ideal, long flag, long prec)
{
  switch(flag)
  {
    case 0: flag = nf_INIT; break;
    case 1: flag = nf_INIT | nf_GEN; break;
    default: err(flagerr,"bnrinit");
  }
  return buchrayall(bignf,ideal,flag,prec);
}

GEN
rayclassno(GEN bnf,GEN ideal)
{
  GEN nf,clno,dataunit,p1;
  GEN racunit,bigres,bid,resbid,resbid2,funits,hmat;
  long RU,R3,i,j,av=avma;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7]; bigres=(GEN)bnf[8];
  funits = check_units(bnf,"rayclassno");
  clno = gmael(bigres,1,1);
  bid = zidealstarinitall(nf,ideal,0);
  resbid=(GEN)bid[2]; resbid2=(GEN)resbid[2];
  R3=lg(resbid2)-1; if (!R3) { avma=av; return icopy(clno); }

  RU=lg(funits); dataunit=cgetg(RU+R3+1,t_MAT);
  racunit=gmael(bigres,4,2); dataunit[1]=(long)zideallog(nf,racunit,bid);
  for (j=2; j<=RU; j++)
    dataunit[j]=(long)zideallog(nf,(GEN)funits[j-1],bid);
  for (   ; j<=RU+R3; j++)
  {
    p1=cgetg(R3+1,t_COL); dataunit[j]=(long)p1;
    for (i=1; i<=R3; i++)
      p1[i] = (i==(j-RU))?resbid2[i]:zero;
  }
  hmat = hnfmodid(dataunit,(GEN)resbid2[1]);
  for (i=lg(hmat)-1 ; i; i--) clno = mulii(clno,gcoeff(hmat,i,i));
  avma=av; return icopy(clno);
}

GEN
isprincipalrayall(GEN bnr, GEN x, long flag)
{
  long av=avma,i,j,c,N,ngen,ngzk;
  GEN bnf,nf,bid,vecel,vecep,matu,ep,p1,p2,beta,idep,y,rayclass;
  GEN divray,genray,alpha,alphaall,racunit,res,funit,pol;

  checkbnr(bnr);
  bnf = (GEN)bnr[1];
  bid = (GEN)bnr[2];
  vecel=(GEN)bnr[3]; ngen=lg(vecel)-1;
  matu =(GEN)bnr[4];
  rayclass=(GEN)bnr[5];

  nf = (GEN)bnf[7];
  if (typ(x) == t_VEC && lg(x) == 3)
  { idep = (GEN)x[2]; x = (GEN)x[1]; } /* precomputed */
  else
    idep = isprincipalgenforce(bnf,x);
  if (lg(idep[1]) != ngen+1)
    err(talker,"incorrect generator length in isprincipalray");
  pol=(GEN)nf[1]; N=lgef(pol)-3;
  ep  =(GEN)idep[1];
  beta=(GEN)idep[2]; p2 = NULL;
  for (i=1; i<=ngen; i++)
    if (typ(vecel[i]) != t_INT) /* <==> != 1 */
    {
      p1 = element_pow(nf, (GEN)vecel[i], (GEN)ep[i]);
      p2 = p2? element_mul(nf,p2,p1): p1;
    }
  if (p2) beta = element_div(nf,beta,p2);
  p1 = zideallog(nf,beta,bid); ngzk=lg(p1)-1;
  vecep = cgetg(ngen+ngzk+1,t_COL);
  for (i=1; i<=ngen;      i++) vecep[i] = ep[i];
  for (   ; i<=ngen+ngzk; i++) vecep[i] = p1[i-ngen];
  p1 = gmul(matu,vecep);
  divray = (GEN)rayclass[2]; c=lg(divray);
  y = cgetg(c,t_COL);
  for (i=1; i<c; i++)
    y[i] = lmodii((GEN)p1[i],(GEN)divray[i]);
  if (!(flag & nf_GEN)) return gerepileupto(av, y);

  /* compute generator */
  if (lg(rayclass)<=3)
    err(talker,"please apply bnrinit(,,1) and not bnrinit(,,0)");

  genray = (GEN)rayclass[3]; p2 = NULL;
  for (i=1; i<c; i++)
  {
    p1 = idealpow(nf,(GEN)genray[i],(GEN)y[i]);
    p2 = p2? idealmul(nf,p2,p1): p1;
  }
  if (p2) x = idealdiv(nf,x,p2);
  alphaall = isprincipalgenforce(bnf,x);
  if (!gcmp0((GEN)alphaall[1])) err(bugparier,"isprincipalray (bug1)");

  res = (GEN)bnf[8];
  funit = check_units(bnf,"isprincipalrayall");
  alpha = basistoalg(nf,(GEN)alphaall[2]);
  p1 = zideallog(nf,(GEN)alphaall[2],bid);
  if (lg(p1) > 1)
  {
    GEN mat = (GEN)bnr[6];
    p1 = gmul((GEN)mat[1],p1);
    if (!gcmp1(denom(p1))) err(bugparier,"isprincipalray (bug2)");

    x = lllreducemodmatrix(p1,(GEN)mat[2]);
    racunit = gmael(res,4,2);
    p1 = powgi(gmodulcp(racunit,pol), (GEN)x[1]);
    for (j=1; j<lg(funit); j++)
      p1 = gmul(p1, powgi(gmodulcp((GEN)funit[j],pol), (GEN)x[j+1]));
    alpha = gdiv(alpha,p1);
  }
  p1 = cgetg(4,t_VEC);
  p1[1] = lcopy(y);
  p1[2] = (long)algtobasis(nf,alpha);
  p1[3] = lmin((GEN)idep[3],(GEN)alphaall[3]);
  return gerepileupto(av, p1);
}

GEN
isprincipalray(GEN bignfray, GEN x)
{
  return isprincipalrayall(bignfray,x,nf_REGULAR);
}

GEN
isprincipalraygen(GEN bignfray, GEN x)
{
  return isprincipalrayall(bignfray,x,nf_GEN);
}

GEN
minkowski_bound(GEN D, long N, long r2, long prec)
{
  long av = avma;
  GEN p1;
  p1 = gdiv(mpfactr(N,prec), gpowgs(stoi(N),N));
  p1 = gmul(p1, gpowgs(gdivsg(4,mppi(prec)), r2));
  p1 = gmul(p1, gsqrt(absi(D),prec));
  return gerepileupto(av, p1);
}

/* DK = |dK| */
static long
zimmertbound(long N,long R2,GEN DK)
{
  long av = avma;
  GEN w;

  if (N < 2) return 1;
  if (N < 21)
  {
    static double c[21][11] = {
{/*2*/  0.6931,     0.45158},
{/*3*/  1.71733859, 1.37420604},
{/*4*/  2.91799837, 2.50091538, 2.11943331},
{/*5*/  4.22701425, 3.75471588, 3.31196660},
{/*6*/  5.61209925, 5.09730381, 4.60693851, 4.14303665},
{/*7*/  7.05406203, 6.50550021, 5.97735406, 5.47145968},
{/*8*/  8.54052636, 7.96438858, 7.40555445, 6.86558259, 6.34608077},
{/*9*/ 10.0630022,  9.46382812, 8.87952524, 8.31139202, 7.76081149},
{/*10*/11.6153797, 10.9966020, 10.3907654,  9.79895170, 9.22232770, 8.66213267},
{/*11*/13.1930961, 12.5573772, 11.9330458, 11.3210061, 10.7222412, 10.1378082},
{/*12*/14.7926394, 14.1420915, 13.5016616, 12.8721114, 12.2542699, 11.6490374,
       11.0573775},
{/*13*/16.4112395, 15.7475710, 15.0929680, 14.4480777, 13.8136054, 13.1903162,
       12.5790381},
{/*14*/18.0466672, 17.3712806, 16.7040780, 16.0456127, 15.3964878, 14.7573587,
       14.1289364, 13.5119848},
{/*15*/19.6970961, 19.0111606, 18.3326615, 17.6620757, 16.9999233, 16.3467686,
       15.7032228, 15.0699480},
{/*16*/21.3610081, 20.6655103, 19.9768082, 19.2953176, 18.6214885, 17.9558093,
       17.2988108, 16.6510652, 16.0131906},

{/*17*/23.0371259, 22.3329066, 21.6349299, 20.9435607, 20.2591899, 19.5822454,
       18.9131878, 18.2525157, 17.6007672},

{/*18*/24.7243611, 24.0121449, 23.3056902, 22.6053167, 21.9113705, 21.2242247,
       20.5442836, 19.8719830, 19.2077941, 18.5522234},

{/*19*/26.4217792, 25.7021950, 24.9879497, 24.2793271, 23.5766321, 22.8801952,
       22.1903709, 21.5075437, 20.8321263, 20.1645647},
{/*20*/28.1285704, 27.4021674, 26.6807314, 25.9645140, 25.2537867, 24.5488420,
       23.8499943, 23.1575823, 22.4719720, 21.7935548, 21.1227537}
    };
    w = gmul(dbltor(exp(-c[N][R2])), gsqrt(DK,MEDDEFAULTPREC));
  }
  else
  {
    w = minkowski_bound(DK, N, R2, MEDDEFAULTPREC);
    if (cmpis(w, 500000))
      err(warner,"large Minkowski bound: certification will be VERY long");
  }
  w = gceil(w);
  if (is_bigint(w))
    err(talker,"Minkowski bound is too large");
  avma = av; return itos(w);
}

/* all primes up to Minkowski bound factor on factorbase ? */
static void
testprime(GEN bnf, long minkowski)
{
  long av = avma, pp,i,nbideal,k,pmax;
  GEN f,p1,vectpp,fb,dK, nf=checknf(bnf);
  byteptr delta = diffptr;

  if (DEBUGLEVEL>1)
    fprintferr("PHASE 1: check primes to Zimmert bound = %ld\n\n",minkowski);
  f=(GEN)nf[4]; dK=(GEN)nf[3];
  if (!gcmp1(f))
  {
    GEN different = gmael(nf,5,5);
    if (DEBUGLEVEL>1)
      fprintferr("**** Testing Different = %Z\n",different);
    p1 = isprincipalall(bnf,different,nf_FORCE);
    if (DEBUGLEVEL>1) fprintferr("     is %Z\n",p1);
  }
  fb=(GEN)bnf[5];
  p1 = gmael(fb, lg(fb)-1, 1); /* largest p in factorbase */
  pp = 0; pmax = is_bigint(p1)? VERYBIGINT: itos(p1);
  if (minkowski > maxprime()) err(primer1);
  while (pp < minkowski)
  {
    pp += *delta++;
    if (DEBUGLEVEL>1) fprintferr("*** p = %ld\n",pp);
    vectpp=primedec(bnf,stoi(pp)); nbideal=lg(vectpp)-1;
    /* loop through all P | p if ramified, all but one otherwise */
    if (!smodis(dK,pp)) nbideal++;
    for (i=1; i<nbideal; i++)
    {
      GEN P = (GEN)vectpp[i];
      if (DEBUGLEVEL>1)
        fprintferr("  Testing P = %Z\n",P);
      if (cmpis(idealnorm(bnf,P), minkowski) < 1)
      {
	if (pp <= pmax && (k = tablesearch(fb, P, cmp_prime_ideal)))
	{
	  if (DEBUGLEVEL>1) fprintferr("    #%ld in factor base\n",k);
	}
	else
	{
	  p1 = isprincipal(bnf,P);
	  if (DEBUGLEVEL>1) fprintferr("    is %Z\n",p1);
	}
      }
      else if (DEBUGLEVEL>1)
        fprintferr("    Norm(P) > Zimmert bound\n");
    }
  }
  avma=av;
  if (DEBUGLEVEL>1) { fprintferr("End of PHASE 1.\n\n"); flusherr(); }
}

/* return \gamma_n^n if known, an upper bound otherwise */
static GEN
hermiteconstant(long n)
{
  GEN h,h1;
  long av;

  switch(n)
  {
    case 1: return gun;
    case 2: h=cgetg(3,t_FRAC); h[1]=lstoi(4); h[2]=lstoi(3); return h;
    case 3: return gdeux;
    case 4: return stoi(4);
    case 5: return stoi(8);
    case 6: h=cgetg(3,t_FRAC); h[1]=lstoi(64); h[2]=lstoi(3); return h;
    case 7: return stoi(64);
    case 8: return stoi(256);
  }
  av = avma;
  h  = gpuigs(divsr(2,mppi(DEFAULTPREC)), n);
  h1 = gsqr(ggamma(gdivgs(stoi(n+4),2),DEFAULTPREC));
  return gerepileupto(av, gmul(h,h1));
}

/* 1 if primitive for sure, 0 if MAYBE imprimitive */
static long
isprimitive(GEN nf)
{
  long N,first,i,l,ep;
  GEN d,fa;

  N = lgef(nf[1])-3; fa = (GEN)factor(stoi(N))[1]; /* primes | N */
  first = itos((GEN)fa[1]); if (first==N) return 1;

  d=absi((GEN)nf[3]); fa=(GEN)factor(d)[2]; /* expo. primes | disc(nf) */
  if (mod2(d))
    { i=1; ep=1; }
  else
    { i=2; ep=itos((GEN)fa[1])>>1; }
  l=lg(fa);
  for ( ; i < l; i++)
  {
    if (ep >= first) return 0;
    ep = itos((GEN)fa[i]);
  }
  return 1;
}

static GEN
regulatorbound(GEN bnf)
{
  long N,R1,R2,R;
  GEN nf,dKa,bound,p1,c1;

  nf=(GEN)bnf[7]; N=lgef(nf[1])-3;
  bound=dbltor(0.2);
  if (!isprimitive(nf))
  {
    if (DEBUGLEVEL>=2)
      { fprintferr("Default bound for regulator: 0.2\n"); flusherr(); }
    return bound;
  }
  dKa=absi((GEN)nf[3]);
  R1=itos(gmael(nf,2,1));
  R2=itos(gmael(nf,2,2)); R=R1+R2-1;
  if (!R2 && N<12) c1=gpuigs(stoi(4),N>>1); else c1=gpuigs(stoi(N),N);
  if (cmpii(dKa,c1)<=0)
  {
    if (DEBUGLEVEL>=2)
      { fprintferr("Default bound for regulator: 0.2\n"); flusherr(); }
    return bound;
  }
  p1 = gsqr(glog(gdiv(dKa,c1),DEFAULTPREC));
  p1 = gdivgs(gmul2n(gpuigs(gdivgs(gmulgs(p1,3),N*(N*N-1)-6*R2),R),R2),N);
  p1 = gsqrt(gdiv(p1, hermiteconstant(R)), DEFAULTPREC);
  if (gcmp(p1,bound) > 0) bound = p1;
  if (DEBUGLEVEL>=2)
    { fprintferr("Mahler bound for regulator: %Z\n",p1); flusherr(); }
  return bound;
}

/* x given by its embeddings */
GEN 
norm_by_embed(long r1, GEN x)
{
  long i, ru = lg(x)-1;
  GEN p = (GEN)x[ru];
  if (r1 == ru)
  {
    for (i=ru-1; i>0; i--) p = gmul(p, (GEN)x[i]);
    return p;
  }
  p = gnorm(p);
  for (i=ru-1; i>r1; i--) p = gmul(p, gnorm((GEN)x[i]));
  for (      ; i>0 ; i--) p = gmul(p, (GEN)x[i]);
  return p;
}

static int
is_unit(GEN M, long r1, GEN x)
{
  long av = avma;
  GEN Nx = ground( norm_by_embed(r1, gmul_mat_smallvec(M,x)) );
  int ok = is_pm1(Nx);
  avma = av; return ok;
}

#define NBMAX 5000
/* should use smallvectors */
static GEN
minimforunits(GEN nf, long BOUND, long stockmax)
{
  const long prec = MEDDEFAULTPREC;
  long av = avma,n,i,j,k,s,norme,normax,*x,cmpt,r1;
  GEN u,r,S,a,M,p1;
  double p;
  double **q,*v,*y,*z;
  double eps=0.000001;

  if (DEBUGLEVEL>=2)
  {
    fprintferr("Searching minimum of T2-form on units:\n");
    if (DEBUGLEVEL>2) fprintferr("   BOUND = %ld\n",BOUND);
    flusherr();
  }
  r1 = itos(gmael(nf,2,1));
  a = gmael(nf,5,3); n = lg(a);
  minim_alloc(n, &q, &x, &y, &z, &v);
  n--; BOUND += eps;
  u = lllgram(a,prec);
  M = gmul(gmael(nf,5,1), u); /* embeddings of T2-reduced basis */
  M = gprec_w(M, prec);
  a = gmul(qf_base_change(a,u,1), realun(prec));
  r = sqred1(a);
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j));
  }
  normax=0;
  S = cgetg(stockmax+1,t_MAT);
  s=0; k=n; cmpt=0; y[n]=z[n]=0;
  x[n]=(long)(sqrt(BOUND/v[n]));

  for(;;)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
	z[l] = 0;
	for (j=k; j<=n; j++) z[l] = z[l]+q[l][j]*x[j];
	p = x[k]+z[k];
	y[l] = y[k]+p*p*v[k];
	x[l] = (long)floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
        p = x[k]+z[k];
        if (y[k] + p*p*v[k] <= BOUND) break;
	k++; x[k]--;
      }
    }
    while (k>1);
    if (!x[1] && y[1]<=eps) break;
    if (++cmpt > NBMAX) { av=avma; return NULL; }

    if (DEBUGLEVEL>8){ fprintferr("."); flusherr(); }
    p = x[1]+z[1]; norme = (long)(y[1] + p*p*v[1] + eps);
    if (norme > normax) normax = norme;
    if (is_unit(M,r1, x))
    {
      if (DEBUGLEVEL>=2) { fprintferr("*"); flusherr(); }
      cmpt = 0;
      if (++s <= stockmax)
      {
	p1 = cgetg(n+1,t_COL);
	for (i=1; i<=n; i++) p1[i]=lstoi(x[i]);
	S[s] = lmul(u,p1);
      }
    }
    x[k]--;
  }
  if (DEBUGLEVEL>=2){ fprintferr("\n"); flusherr(); }
  k = (s<stockmax)? s:stockmax; setlg(S,k+1);
  S = gerepileupto(av, gcopy(S));
  u = cgetg(4,t_VEC);
  u[1] = lstoi(s<<1);
  u[2] = lstoi(normax);
  u[3] = (long)S; return u;
}

#undef NBMAX
static int
is_zero(GEN x, long bitprec) { return (gexpo(x) < -bitprec); }

static int
is_complex(GEN x, long bitprec) { return (!is_zero(gimag(x), bitprec)); }

static GEN
compute_M0(GEN M_star,long N)
{
  long m1,m2,n1,n2,n3,k,kk,lr,lr1,lr2,i,j,l,vx,vy,vz,vM,prec;
  GEN pol,p1,p2,p3,p4,p5,p6,p7,p8,p9,u,v,w,r,r1,r2,M0,M0_pro,S,P,M;
  GEN f1,f2,f3,g1,g2,g3,pg1,pg2,pg3,pf1,pf2,pf3,X,Y,Z;
  long bitprec = 24, PREC = gprecision(M_star);

  if (N==2) return gmul2n(gsqr(gach(gmul2n(M_star,-1),PREC)), -1);
  vM = fetch_var(); M = polx[vM];
  vz = fetch_var(); Z = polx[vz];
  vy = fetch_var(); Y = polx[vy];
  vx = fetch_var(); X = polx[vx];

  PREC = PREC>>1; if (!PREC) PREC = DEFAULTPREC;
  M0 = NULL; m1 = N/3;
  for (n1=1; n1<=m1; n1++)
  {
    m2 = (N-n1)>>1;
    for (n2=n1; n2<=m2; n2++)
    {
      long av = avma; n3=N-n1-n2; prec=PREC;
      if (n1==n2 && n1==n3) /* n1 = n2 = n3 = m1 = N/3 */
      {
	p1=gdivgs(M_star,m1);
        p2=gaddsg(1,p1);
        p3=gsubgs(p1,3);
	p4=gsqrt(gmul(p2,p3),prec);
        p5=gsubgs(p1,1);
	u=gun;
        v=gmul2n(gadd(p5,p4),-1);
        w=gmul2n(gsub(p5,p4),-1);
	M0_pro=gmul2n(gmulsg(m1,gadd(gsqr(glog(v,prec)),gsqr(glog(w,prec)))),-2);
	if (DEBUGLEVEL>2)
	{
	  fprintferr("[ %ld, %ld, %ld ]: %Z\n",n1,n2,n3,gprec_w(M0_pro,3));
	  flusherr();
	}
	if (!M0 || gcmp(M0_pro,M0)<0) M0 = M0_pro;
      }
      else if (n1==n2 || n2==n3)
      { /* n3 > N/3 >= n1 */
	k = n2; kk = N-2*k;
	p2=gsub(M_star,gmulgs(X,k));
	p3=gmul(gpuigs(stoi(kk),kk),gpuigs(gsubgs(gmul(M_star,p2),kk*kk),k));
	pol=gsub(p3,gmul(gmul(gpuigs(stoi(k),k),gpuigs(X,k)),gpuigs(p2,N-k)));
	prec=gprecision(pol); if (!prec) prec = MEDDEFAULTPREC;
	r=roots(pol,prec); lr = lg(r);
	for (i=1; i<lr; i++)
	{
	  if (is_complex((GEN)r[i], bitprec) ||
	      signe(S = greal((GEN)r[i])) <= 0) continue;

          p4=gsub(M_star,gmulsg(k,S));
          P=gdiv(gmul(gmulsg(k,S),p4),gsubgs(gmul(M_star,p4),kk*kk));
          p5=gsub(gsqr(S),gmul2n(P,2));
          if (gsigne(p5) < 0) continue;

          p6=gsqrt(p5,prec);
          v=gmul2n(gsub(S,p6),-1);
          if (gsigne(v) <= 0) continue;
          
          u=gmul2n(gadd(S,p6),-1);
          w=gpui(P,gdivgs(stoi(-k),kk),prec);
          p6=gmulsg(k,gadd(gsqr(glog(u,prec)),gsqr(glog(v,prec))));
          M0_pro=gmul2n(gadd(p6,gmulsg(kk,gsqr(glog(w,prec)))),-2);
          if (DEBUGLEVEL>2)
          {
            fprintferr("[ %ld, %ld, %ld ]: %Z\n",n1,n2,n3,gprec_w(M0_pro,3));
            flusherr();
          }
          if (!M0 || gcmp(M0_pro,M0)<0) M0 = M0_pro;
	}
      }
      else
      {
	f1 = gsub(gadd(gmulsg(n1,X),gadd(gmulsg(n2,Y),gmulsg(n3,Z))), M);
	f2 =         gmulsg(n1,gmul(Y,Z));
	f2 = gadd(f2,gmulsg(n2,gmul(X,Z)));
	f2 = gadd(f2,gmulsg(n3,gmul(X,Y)));
	f2 = gsub(f2,gmul(M,gmul(X,gmul(Y,Z))));
	f3 = gsub(gmul(gpuigs(X,n1),gmul(gpuigs(Y,n2),gpuigs(Z,n3))), gun);
        /* f1 = n1 X + n2 Y + n3 Z - M */
        /* f2 = n1 YZ + n2 XZ + n3 XY */
        /* f3 = X^n1 Y^n2 Z^n3 - 1*/
	g1=subres(f1,f2); g1=gdiv(g1,content(g1));
	g2=subres(f1,f3); g2=gdiv(g2,content(g2));
	g3=subres(g1,g2); g3=gdiv(g3,content(g3));
	pf1=gsubst(f1,vM,M_star); pg1=gsubst(g1,vM,M_star);
	pf2=gsubst(f2,vM,M_star); pg2=gsubst(g2,vM,M_star);
	pf3=gsubst(f3,vM,M_star); pg3=gsubst(g3,vM,M_star);
	prec=gprecision(pg3); if (!prec) prec = MEDDEFAULTPREC;
	r=roots(pg3,prec); lr = lg(r);
	for (i=1; i<lr; i++)
	{
	  if (is_complex((GEN)r[i], bitprec) ||
	      signe(w = greal((GEN)r[i])) <= 0) continue;
          p1=gsubst(pg1,vz,w);
          p2=gsubst(pg2,vz,w);
          p3=gsubst(pf1,vz,w);
          p4=gsubst(pf2,vz,w);
          p5=gsubst(pf3,vz,w);
          prec=gprecision(p1); if (!prec) prec = MEDDEFAULTPREC;
          r1 = roots(p1,prec); lr1 = lg(r1);
          for (j=1; j<lr1; j++)
          {
            if (is_complex((GEN)r1[j], bitprec)
             || signe(v = greal((GEN)r1[j])) <= 0
             || !is_zero(gsubst(p2,vy,v), bitprec)) continue;

            p7=gsubst(p3,vy,v);
            p8=gsubst(p4,vy,v);
            p9=gsubst(p5,vy,v);
            prec=gprecision(p7); if (!prec) prec = MEDDEFAULTPREC;
            r2 = roots(p7,prec); lr2 = lg(r2);
            for (l=1; l<lr2; l++)
            {
              if (is_complex((GEN)r2[l], bitprec)
               || signe(u = greal((GEN)r2[l])) <= 0
               || !is_zero(gsubst(p8,vx,u), bitprec)
               || !is_zero(gsubst(p9,vx,u), bitprec)) continue;

              M0_pro =              gmulsg(n1,gsqr(mplog(u)));
              M0_pro = gadd(M0_pro, gmulsg(n2,gsqr(mplog(v))));
              M0_pro = gadd(M0_pro, gmulsg(n3,gsqr(mplog(w))));
              M0_pro = gmul2n(M0_pro,-2);
              if (DEBUGLEVEL>2)
              {
               fprintferr("[ %ld, %ld, %ld ]: %Z\n",n1,n2,n3,gprec_w(M0_pro,3));
               flusherr();
              }
              if (!M0 || gcmp(M0_pro,M0) < 0) M0 = M0_pro;
            }
          }
	}
      }
      if (!M0) avma = av; else M0 = gerepileupto(av, gcopy(M0));
    }
  }
  for (i=1;i<=4;i++) delete_var();
  return M0? M0: gzero;
}

static GEN
lowerboundforregulator_i(GEN bnf)
{
  long N,R1,R2,RU,i,nbrootsofone,nbmin;
  GEN rootsofone,nf,M0,M,m,col,T2,bound,minunit,newminunit;
  GEN vecminim,colalg,p1,pol,y;
  GEN units = check_units(bnf,"bnfcertify");

  rootsofone=gmael(bnf,8,4); nbrootsofone=itos((GEN)rootsofone[1]);
  nf=(GEN)bnf[7]; T2=gmael(nf,5,3); N=lgef(nf[1])-3;
  R1=itos(gmael(nf,2,1)); R2=itos(gmael(nf,2,2)); RU=R1+R2-1;
  if (RU==0) return gun;

  units=algtobasis(bnf,units); minunit=qfeval(T2,(GEN)units[1]);
  for (i=2; i<=RU; i++)
  {
    newminunit=qfeval(T2,(GEN)units[i]);
    if (gcmp(newminunit,minunit)<0) minunit=newminunit;
  }
  if (gcmpgs(minunit,1000000000)>0) return NULL;

  vecminim = minimforunits(nf,itos(gceil(minunit)),10000);
  if (!vecminim) return NULL;
  m=(GEN)vecminim[3]; nbmin=lg(m)-1;
  if (nbmin==10000) return NULL;
  bound=gaddgs(minunit,1);
  for (i=1; i<=nbmin; i++)
  {
    col=(GEN)m[i]; colalg=basistoalg(nf,col);
    if (!gcmp1(lift_intern(gpuigs(colalg,nbrootsofone))))
    {
      newminunit=qfeval(T2,col);
      if (gcmp(newminunit,bound)<0) bound=newminunit;
    }
  }
  if (gcmp(bound,minunit)>0) err(talker,"bug in lowerboundforregulator");
  if (DEBUGLEVEL>1)
  {
    fprintferr("M* = %Z\n",gprec_w(bound,3));
    if (DEBUGLEVEL>2)
    {
      p1=polx[0]; pol=gaddgs(gsub(gpuigs(p1,N),gmul(bound,p1)),N-1);
      p1 = roots(pol,DEFAULTPREC);
      if (N&1) y=greal((GEN)p1[3]); else y=greal((GEN)p1[2]);
      M0 = gmul2n(gmulsg(N*(N-1),gsqr(glog(y,DEFAULTPREC))),-2);
      fprintferr("pol = %Z\n",pol);
      fprintferr("old method: y = %Z, M0 = %Z\n",y,gprec_w(M0,3));
    }
    flusherr();
  }
  M0 = compute_M0(bound,N);
  if (DEBUGLEVEL>1) { fprintferr("M0 = %Z\n",gprec_w(M0,3)); flusherr(); }
  M = gmul2n(gdivgs(gdiv(gpuigs(M0,RU),hermiteconstant(RU)),N),R2);
  if (gcmp(M,dbltor(0.04))<0) return NULL;
  M = gsqrt(M,DEFAULTPREC);
  if (DEBUGLEVEL>1)
  {
    fprintferr("(lower bound for regulator) M = %Z\n",gprec_w(M,3));
    flusherr();
  }
  return M;
}

static GEN
lowerboundforregulator(GEN bnf)
{
  long av = avma;
  GEN x = lowerboundforregulator_i(bnf);
  if (!x) { avma = av; x = regulatorbound(bnf); }
  return x;
}

/* Calcule une matrice carree de rang lg(beta) associee a une famille
 * d'ideaux premiers P_i tels que : 1<=i<=nombre de beta; N(P_i) congru a 1
 * mod pp v_(P_i)(beta[j])=0 pour tout 1<=j<=nbalphapro et 1<=i<=lg(beta)
 */
static void
primecertify(GEN bnf,GEN beta,long pp,GEN big)
{
  long i,j,qq,nbcol,sizeofmat,nbqq,ra,N;
  GEN nf,mat,mat1,qgen,decqq,newcol,eltgen,qrhall,Q;

  nbcol=0; nf=(GEN)bnf[7]; N=lgef(nf[1])-3;
  sizeofmat=lg(beta)-1; mat=cgetg(1,t_MAT); qq=1;
  for(;;)
  {
    qq += 2*pp; qgen = stoi(qq);
    if (smodis(big,qq)==0 || !isprime(qgen)) continue;

    decqq = primedec(bnf,qgen); nbqq = lg(decqq)-1;
    for (i=1; i<=nbqq; i++)
    {
      Q = (GEN)decqq[i];
      if (!gcmp1((GEN)Q[4])) continue;

      qrhall = nfmodprinit(nf,Q); nbcol++;
      newcol = cgetg(sizeofmat+1,t_COL);
      if (DEBUGLEVEL>1)
        fprintferr("       prime ideal Q: %Z\n",Q);
      eltgen = gscalcol_i(lift(gener(qgen)), N);
      for (j=1; j<=sizeofmat; j++)
        newcol[j] = (long)nfshanks(nf,(GEN)beta[j],eltgen,Q,qrhall);
      if (DEBUGLEVEL>1)
      {
        fprintferr("       generator of (Zk/Q)^*: %Z\n",eltgen);
        fprintferr("       column #%ld of the matrix log(b_j/Q): %Z\n",
                   nbcol, newcol);
      }
      mat1 = concatsp(mat,newcol); ra = rank(mat1);
      if (DEBUGLEVEL>1)
       {fprintferr("       new rank of the matrix: %ld\n\n",ra); flusherr();}
      if (ra!=nbcol) nbcol--;
      else
      {
        if (nbcol==sizeofmat) return;
        mat = mat1;
      }
    }
  }
}

static void
check_prime(long p, GEN bnf, GEN h, GEN cyc, long R, GEN alpha,
            GEN funits, GEN rootsofone, GEN big)
{
  long av = avma, nbpro,nbalpha,i, nbgen = lg(cyc)-1;
  GEN p1,beta, nbrootsofone = (GEN)rootsofone[1];

  if (DEBUGLEVEL>1) fprintferr("***** Testing prime p = %ld\n",p);
  if (smodis(h,p)) nbpro=0;
  else
  {
    if (DEBUGLEVEL>1) fprintferr("     p divides cl(k)\n");
    for (nbpro=nbgen; nbpro; nbpro--)
      if (!smodis((GEN)cyc[nbpro],p)) break;
  }
  nbalpha = nbpro+R;
  if (smodis(nbrootsofone,p)) p1 = (GEN)alpha[nbpro];
  else
  {
    if (DEBUGLEVEL>1) fprintferr("     p divides w(k)\n");
    nbalpha++; nbpro++; p1 = (GEN)rootsofone[2];
  }
  if (DEBUGLEVEL>1) {fprintferr("     t+r+e = %ld\n",nbalpha); flusherr();}
  beta = cgetg(nbalpha+1,t_VEC);
  if (nbpro)
  {
    for (i=1; i<nbpro; i++) beta[i] = alpha[i];
    beta[nbpro] = (long)p1;
  }
  for (i=1; i<=R; i++) beta[i+nbpro] = funits[i];
  if (DEBUGLEVEL>2) {fprintferr("     Beta list = %Z\n",beta); flusherr();}
  primecertify(bnf,beta,p,big); avma = av;
}

long
certifybuchall(GEN bnf)
{
  long av = avma, nbgen,i,j,pp,N,R1,R2,R,nfa,nbf1,bound;
  GEN big,nf,reg,rootsofone,funits,gen,p1,gbound,DK,cycgen,factfd1,f1,h,cyc;
  byteptr delta = diffptr;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  N=lgef(nf[1])-3; if (N==1) return 1;
  R1=itos(gmael(nf,2,1)); R2=itos(gmael(nf,2,2)); R=R1+R2-1;
  funits = check_units(bnf,"bnfcertify");
  DK=absi((GEN)nf[3]);
  testprime(bnf,zimmertbound(N,R2,DK));
  p1=gmael(bnf,8,1); reg=gmael(bnf,8,2);
  h=(GEN)p1[1];
  cyc=(GEN)p1[2]; nbgen=lg(cyc)-1;
  gen=(GEN)p1[3]; rootsofone=gmael(bnf,8,4);
  if (DEBUGLEVEL>1)
  {
    fprintferr("Class number = %Z\n",h);
    fprintferr("Cyclic components = %Z\n",cyc);
    fprintferr("Generators = %Z\n",gen);
    fprintferr("Regulator = %Z\n",gprec_w(reg,3));
    fprintferr("Roots of one = %Z\n",rootsofone);
    fprintferr("Fundamental units = %Z\n",funits);
  }
  cycgen = check_and_build_cycgen(bnf);
  gbound = ground(gdiv(reg,lowerboundforregulator(bnf)));
  if (is_bigint(gbound))
    err(talker,"sorry, too many primes to check");

  bound = itos(gbound); if (bound > maxprime()) err(primer1);
  if (DEBUGLEVEL>1)
  {
    fprintferr("\nPHASE 2: are all primes good ?\n\n");
    fprintferr("  Testing primes <= B (= %ld)\n\n",bound); flusherr();
  }
  for (big=gun,i=1; i<=nbgen; i++)
    big = mulii(big,idealnorm(nf,(GEN)gen[i]));

  funits = dummycopy(funits);
  for (i=1; i<lg(funits); i++)
    funits[i] = (long)algtobasis(nf, (GEN)funits[i]);
  rootsofone = dummycopy(rootsofone);
  rootsofone[2] = (long)algtobasis(nf, (GEN)rootsofone[2]);

  for (pp = *delta++; pp <= bound; pp += *delta++)
    check_prime(pp,bnf,h,cyc,R,cycgen,funits,rootsofone,big);

  nfa = 0;
  if (nbgen)
  {
    factfd1=factor((GEN)cyc[1]);
    nbf1=lg(factfd1[1]); f1=(GEN)factfd1[1];
    for (i=1; i<nbf1; i++)
      if (cmpis((GEN)f1[i],bound) > 0) nfa++;
    if (DEBUGLEVEL>1 && nfa)
      { fprintferr("  Testing primes > B (# = %ld)\n\n",nfa); flusherr(); }
    for (j=1; j<=nfa; j++)
    {
      pp = itos((GEN)f1[nbf1-j]);
      check_prime(pp,bnf,gzero,cyc,R,cycgen,funits,rootsofone,big);
    }
  }
  avma=av; return 1;
}

/*******************************************************************/
/*                                                                 */
/*     CORPS DE CLASSES DE RAYON : CONDUCTEURS ET DISCRIMINANTS    */
/*                                                                 */
/*******************************************************************/

/* Si s est la surjection de Cl_m sur Cl_n et H ssgroupe de Cl_m,
 * retourne le ssgroupe s(H) de Cl_n
 */
static GEN
imageofgroup0(GEN H,GEN bnr,GEN subgroup)
{
  long j,l;
  GEN E,Delta = diagonal(gmael(bnr,5,2));

  if (gcmp0(subgroup)) return Delta;

  l=lg(H); E=cgetg(l,t_MAT);
  for (j=1; j<l; j++)
    E[j] = (long)isprincipalray(bnr,(GEN)H[j]);
  E = concatsp(gmul(E,subgroup),Delta);
  return hnf(E);
}

static GEN
imageofgroup(GEN H,GEN bnr,GEN subgroup)
{
  long av = avma;
  return gerepileupto(av,imageofgroup0(H,bnr,subgroup));
}

/* retourne le cardinal de Cl_n / s(H) */
static GEN
cardofimagofquotientgroup(GEN H,GEN bnr,GEN subgroup)
{
  return dethnf_i(imageofgroup0(H,bnr,subgroup));
}

static GEN
args_to_bnr(GEN arg0, GEN arg1, GEN arg2, GEN *subgroup, long prec)
{
  GEN bnr,bnf;

  if (typ(arg0)!=t_VEC)
    err(talker,"neither bnf nor bnr in conductor or discray");
  if (!arg1) arg1 = gzero;
  if (!arg2) arg2 = gzero;

  switch(lg(arg0))
  {
    case 7:  /* bnr */
      bnr=arg0; (void)checkbnf((GEN)bnr[1]);
      *subgroup=arg1; break;

    case 11: /* bnf */
      bnf = checkbnf(arg0);
      bnr=buchrayall(bnf,arg1,nf_INIT | nf_GEN,prec);
      *subgroup=arg2; break;

    default: err(talker,"neither bnf nor bnr in conductor or discray");
      return NULL; /* not reached */
  }
  if (!gcmp0(*subgroup))
  {
    long tx=typ(*subgroup);
    if (!is_matvec_t(tx))
      err(talker,"bad subgroup in conductor or discray");
  }
  return bnr;
}

GEN
bnrconductor(GEN arg0,GEN arg1,GEN arg2,long all,long prec)
{
  GEN sub=arg1, bnr=args_to_bnr(arg0,arg1,arg2,&sub,prec);
  return conductor(bnr,sub,all,prec);
}

long
bnrisconductor(GEN arg0,GEN arg1,GEN arg2,long prec)
{
  GEN sub=arg1, bnr=args_to_bnr(arg0,arg1,arg2,&sub,prec);
  return itos(conductor(bnr,sub,-1,prec));
}

/* special for isprincipalrayall */
static GEN
getH(GEN bnf, GEN gen)
{
  long i,l = lg(gen);
  GEN p1, H = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    p1 = cgetg(3,t_VEC); H[i] = (long)p1;
    p1[1] = (long)gen[i];
    p1[2] = (long)isprincipalgenforce(bnf, (GEN)gen[i]);
  }
  return H;
}

/*   Given a number field bnf=bnr[1], a ray class group bnr (from buchrayinit),
 *   and a subgroup (HNF form) of the ray class group, compute the conductor
 *   of the subgroup (copy of discrayrelall) if all=0. If all > 0, compute
 *   furthermore the corresponding subgroup and output
 *   [[ideal,arch],[hm,cyc,gen],subgroup] if all = 1, and output
 *   [[ideal,arch],newbnr,subgroup] if all = 2. If all<0, answer only 1 is
 *   module is the conductor, 0 otherwise.
 */
GEN
conductor(GEN bnr,GEN subgroup,long all,long prec)
{
  long r1,j,av=avma,tetpil,k,ep,trivial=0;
  GEN bnf,nf,cl,cyc,gen,bid,ideal,arch,p1,p2,clhray,clhss;
  GEN H,fa,arch2,bnr2,fa2,ex;

  checkbnrgen(bnr); bnf=(GEN)bnr[1]; bid=(GEN)bnr[2];
  cl=(GEN)bnr[5]; cyc=(GEN)cl[2]; gen=(GEN)cl[3];
  nf=(GEN)bnf[7]; r1=itos(gmael(nf,2,1));
  p1=(GEN)bid[1]; ideal=(GEN)p1[1]; arch=(GEN)p1[2];
  if (gcmp0(subgroup)) { trivial=1; clhray=(GEN)cl[1]; }
  else
  {
    p1 = gauss(subgroup,diagonal(cyc));
    if (!gcmp1(denom(p1)))
      err(talker,"incorrect subgroup in conductor");
    if (gcmp1(det(p1))) trivial=1;
    clhray = absi(det(subgroup));
  }
  H = (!trivial || all > 0)? getH(bnf, gen): NULL;
  fa=(GEN)bid[3]; fa2=(GEN)fa[1]; ex=(GEN)fa[2];
  p2=cgetg(3,t_VEC); p2[2]=(long)arch;
  for (k=1; k<lg(fa2); k++)
  {
    GEN pr=(GEN)fa2[k], prinv=idealinv(nf,pr);
    ep = (all>=0)? itos((GEN)ex[k]): 1;
    for (j=1; j<=ep; j++)
    {
      p2[1]=(long)idealmul(nf,ideal,prinv);
      if (trivial) clhss=rayclassno(bnf,p2);
      else
      {
	bnr2=buchrayall(bnf,p2,nf_INIT,prec);
	clhss=cardofimagofquotientgroup(H,bnr2,subgroup);
      }
      if (!egalii(clhss,clhray)) break;
      if (all<0) { avma=av; return gzero; }
      ideal = (GEN)p2[1];
    }
  }
  p2[1]=(long)ideal; arch2=dummycopy(arch); p2[2]=(long)arch2;
  for (k=1; k<=r1; k++)
    if (signe(arch[k]))
    {
      arch2[k]=zero;
      if (trivial) clhss=rayclassno(bnf,p2);
      else
      {
	bnr2=buchrayall(bnf,p2,nf_INIT,prec);
	clhss=cardofimagofquotientgroup(H,bnr2,subgroup);
      }
      if (!egalii(clhss,clhray)) arch2[k]=un;
      else if (all<0) { avma=av; return gzero; }
    }
  if (all<0) {avma=av; return gun;}
  if (!all) { tetpil=avma; return gerepile(av,tetpil,gcopy(p2)); }

  bnr2=buchrayall(bnf,p2,nf_INIT | nf_GEN,prec);
  tetpil=avma; p1=cgetg(4,t_VEC);
  p1[3]=(long)imageofgroup(H,bnr2,subgroup);
  if (all==1) bnr2=(GEN)bnr2[5];
  p1[2]=lcopy(bnr2);
  p1[1]=lcopy(p2); return gerepile(av,tetpil,p1);
}

/* etant donne un bnr et un polynome relatif, trouve le groupe des normes
   correspondant a l'extension relative en supposant qu'elle est abelienne
   et que le module donnant bnr est multiple du conducteur (tout ceci n'etant
   bien sur pas verifie). */
GEN
rnfnormgroup(GEN bnr, GEN polrel)
{
  long av=avma,i,j,reldeg,sizemat,prime,nfac,k;
  GEN bnf,polreldisc,nf,raycl,group,detgroup,fa,pr,famo,ep,fac,col,p1;
  byteptr d = diffptr;

  checkbnr(bnr); bnf=(GEN)bnr[1]; raycl=(GEN)bnr[5];
  if (typ(polrel)!=t_POL) err(typeer,"rnfnormgroup");
  reldeg=lgef(polrel)-3; detgroup=(GEN)raycl[1];
  group = diagonal((GEN)raycl[2]);
  k = cmpis(detgroup,reldeg);
  if (k<0) err(talker,"not an Abelian extension in rnfnormgroup?");
  if (!k) return group;

  polreldisc=discsr(polrel); nf=(GEN)bnf[7];
  sizemat=lg(group)-1; prime = *d++;
  /* tant que nffactormod est bugge pour p=2 on commence a prime = 3 */
  for(;;)
  {
    prime += *d++; if (!*d) err(primer1);
    fa=primedec(nf,stoi(prime));
    for (i=1; i<lg(fa); i++)
    {
      pr = (GEN)fa[i];
      if (element_val(nf,polreldisc,pr)==0)
      {
	famo=nffactormod(nf,polrel,pr);
	ep=(GEN)famo[2]; fac=(GEN)famo[1];
        nfac=lg(ep)-1; k=lgef((GEN)fac[1])-3;
	for (j=1; j<=nfac; j++)
	{
	  if (!gcmp1((GEN)ep[j])) err(bugparier,"rnfnormgroup");
	  if (lgef(fac[j])-3 != k)
	    err(talker,"non Galois extension in rnfnormgroup");
	}
	col=gmulsg(k,isprincipalrayall(bnr,pr,nf_REGULAR));
	p1=cgetg(sizemat+2,t_MAT);
	for (j=1; j<=sizemat; j++) p1[j]=group[j];
	p1[sizemat+1]=(long)col;
	group=hnf(p1); detgroup=dethnf(group);
        k = cmpis(detgroup,reldeg);
        if (k<0) err(talker,"not an Abelian extension in rnfnormgroup?");
	if (!k) { cgiv(detgroup); return gerepileupto(av,group); }
      }
    }
  }
}

/* Etant donne un bnf et un polynome relatif polrel definissant une extension
   abelienne (ce qui n'est pas verifie), calcule le conducteur et le groupe de
   congruence correspondant a l'extension definie par polrel sous la forme
   [[ideal,arch],[hm,cyc,gen],group] ou [ideal,arch] est le conducteur, et
   [hm,cyc,gen] est le groupe de classes de rayon correspondant. */
GEN
rnfconductor(GEN bnf, GEN polrel, long prec)
{
  long av=avma,tetpil,R1,i,v;
  GEN nf,module,arch,bnr,group,p1,pol2;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  module=cgetg(3,t_VEC); R1=itos(gmael(nf,2,1));
  v=varn(polrel);
  p1=unifpol((GEN)bnf[7],polrel,0);
  p1=denom(gtovec(p1));
  pol2=gsubst(polrel,v,gdiv(polx[v],p1));
  pol2=gmul(pol2,gpuigs(p1,degree(pol2)));
  module[1]=rnfdiscf(nf,pol2)[1]; arch=cgetg(R1+1,t_VEC);
  module[2]=(long)arch; for (i=1; i<=R1; i++) arch[i]=un;
  bnr=buchrayall(bnf,module,nf_INIT | nf_GEN,prec);
  group=rnfnormgroup(bnr,pol2); tetpil=avma;
  return gerepile(av,tetpil,conductor(bnr,group,1,prec));
}

/*   Etant donnes un corps de nombres bnf=bnr[1], un groupe de classes de rayon
 * bnr calcule par buchrayinit(), et une matrice HNF subgroup definissant un
 * sous-groupe du groupe de classes de rayon, calcule [n,r1,dk] associe a ce
 * sous groupe (cf. discrayall()). si flcond=0 le calcul est arrete si le
 * module n'est pas le conducteur et le programme retourne gzero.  Si
 * flrel=0, seul la norme de l'ideal dk est calculee au lieu de dk lui-meme
 */
static GEN
discrayrelall(GEN bnr,GEN subgroup,long flag,long prec)
{
  long r1,degk,j,av=avma,tetpil,k,ep,nbdezero;
  long trivial=0, flrel = flag & nf_REL, flcond = flag & nf_COND;
  GEN bnf,nf,cyc,gen,bid,ideal,arch,p1,p2,clhray,clhss;
  GEN H,fa,dlk,arch2,bnr2,idealrel,fa2,ex,som;

  checkbnrgen(bnr); bnf=(GEN)bnr[1];
  cyc=gmael(bnr,5,2); gen=gmael(bnr,5,3);
  nf=(GEN)bnf[7]; r1=itos(gmael(nf,2,1));

  H = NULL; /* gcc -Wall */
  if (gcmp0(subgroup)) { trivial=1; clhray=gmael(bnr,5,1); }
  else
  {
    p1=gauss(subgroup,diagonal(cyc));
    if (!gcmp1(denom(p1)))
      err(talker,"incorrect subgroup in discray");
    if (gcmp1(det(p1))) trivial=1;
    clhray = det(subgroup);
    H = getH(bnf,gen);
  }
  bid=(GEN)bnr[2]; ideal=gmael(bid,1,1); arch=gmael(bid,1,2);
  fa=(GEN)bid[3]; fa2=(GEN)fa[1]; ex=(GEN)fa[2];

  degk=lgef(nf[1])-3;
  idealrel=flrel?idmat(degk):gun;

  p2=cgetg(3,t_VEC); p2[2]=(long)arch;
  for (k=1; k<lg(fa2); k++)
  {
    GEN pr=(GEN)fa2[k], prinv=idealinv(nf,pr);

    ep=itos((GEN)ex[k]); p2[1]=(long)ideal; som=gzero;
    for (j=1; j<=ep; j++)
    {
      p2[1]=(long)idealmul(nf,(GEN)p2[1],prinv);
      if (trivial) clhss=rayclassno(bnf,p2);
      else
      {
        bnr2=buchrayall(bnf,p2,nf_INIT,prec);
        clhss=cardofimagofquotientgroup(H,bnr2,subgroup);
      }
      if (j==1 && egalii(clhss,clhray) && flcond) { avma=av; return gzero; }
      if (is_pm1(clhss)) { som = addis(som, ep-j+1); break; }
      som = addii(som, clhss);
    }
    idealrel = flrel
      ?  idealmul(nf,idealrel, idealpow(nf,pr, som))
      :  mulii(idealrel, powgi((GEN)pr[1], mulii(som,(GEN)pr[4])));
  }
  dlk = flrel
    ?  idealdiv(nf,idealpow(nf,ideal,clhray),idealrel)
    :  divii(powgi(dethnf(ideal),clhray),idealrel);

  p2[1]=(long)ideal; arch2=dummycopy(arch); p2[2]=(long)arch2; nbdezero=0;
  for (k=1; k<=r1; k++)
  {
    if (signe(arch[k]))
    {
      arch2[k]=zero;
      if (trivial) clhss=rayclassno(bnf,p2);
      else
      {
	bnr2=buchrayall(bnf,p2,nf_INIT,prec);
	clhss=cardofimagofquotientgroup(H,bnr2,subgroup);
      }
      arch2[k]=un;
      if (egalii(clhss,clhray))
      {
        if (flcond) { avma=av; return gzero; }
	nbdezero++;
      }
    }
    else nbdezero++;
  }
  tetpil=avma; p1=cgetg(4,t_VEC);
  p1[1]=lcopy(clhray);
  p1[2]=lstoi(nbdezero);
  p1[3]=lcopy(dlk); return gerepile(av,tetpil,p1);
}

static GEN
discrayabsall(GEN bnr, GEN subgroup,long flag,long prec)
{
  long av=avma,tetpil,degk,clhray,n,R1;
  GEN p1,p2,p3,p4,nf,dkabs,bnf;

  p1=discrayrelall(bnr,subgroup,flag,prec);
  if (flag & nf_REL) return p1;
  if (p1==gzero) { avma=av; return gzero; }

  bnf=(GEN)bnr[1]; nf=(GEN)bnf[7]; degk=lgef(nf[1])-3;
  dkabs=absi((GEN)nf[3]); p2=(GEN)p1[3];
  clhray=itos((GEN)p1[1]); p3=gpuigs(dkabs,clhray);
  n = degk * clhray; R1 = itos((GEN)p1[2]) * clhray;
  if (((n-R1)&3)==2) p2=negi(p2);
  tetpil=avma; p4=cgetg(4,t_VEC);
  p4[1]=lstoi(n);
  p4[2]=lstoi(R1);
  p4[3]=lmulii(p2,p3); return gerepile(av,tetpil,p4);
}

GEN
bnrdisc0(GEN arg0, GEN arg1, GEN arg2, long flag, long prec)
{
  GEN subgroup, bnr = args_to_bnr(arg0,arg1,arg2,&subgroup,prec);
  return discrayabsall(bnr,subgroup,flag,prec);
}

GEN
discrayrel(GEN bnr, GEN subgroup,long prec)
{
  return discrayrelall(bnr,subgroup,nf_REL,prec);
}

GEN
discrayrelcond(GEN bnr, GEN subgroup,long prec)
{
  return discrayrelall(bnr,subgroup,nf_REL | nf_COND,prec);
}

GEN
discrayabs(GEN bnr, GEN subgroup,long prec)
{
  return discrayabsall(bnr,subgroup,nf_REGULAR,prec);
}

GEN
discrayabscond(GEN bnr, GEN subgroup,long prec)
{
  return discrayabsall(bnr,subgroup,nf_COND,prec);
}

/* Etant donnes un corps de nombres bnf=bnr[1], un groupe de classes de rayon
 * bnr calcule par buchrayinit(), et un vecteur chi representant un caractere
 * sur les generateurs bnr[2][3], calcule le conducteur de ce caractere.
 */
GEN
bnrconductorofchar(GEN bnr,GEN chi,long prec)
{
  long nbgen,i,av=avma,tetpil;
  GEN p1,m,u,d1,cl,cyclic;

  checkbnrgen(bnr); cl=(GEN)bnr[5];
  cyclic=(GEN)cl[2]; nbgen=lg(cyclic)-1;
  if (lg(chi)-1 != nbgen)
    err(talker,"incorrect character length in conductorofchar");
  if (!nbgen) return conductor(bnr,gzero,0,prec);

  d1=(GEN)cyclic[1]; m=cgetg(nbgen+2,t_MAT);
  for (i=1; i<=nbgen; i++)
  {
    p1=cgetg(2,t_COL); m[i]=(long)p1;
    p1[1]=ldiv(gmul((GEN)chi[i],d1),(GEN)cyclic[i]);
    if (typ(p1[1])!=t_INT) err(typeer,"conductorofchar");
  }
  p1=cgetg(2,t_COL); m[i]=(long)p1;
  p1[1]=(long)d1; u=(GEN)hnfall(m)[2];
  tetpil=avma; setlg(u,nbgen+1);
  for (i=1; i<=nbgen; i++) setlg(u[i],nbgen+1);
  return gerepile(av,tetpil,conductor(bnr,u,0,prec));
}

/* Etant donne la liste des zidealstarinit et des matrices d'unites
 * correspondantes, sort la liste des nombres de classes
 */
GEN
rayclassnolist(GEN bnf,GEN listes)
{
  long av=avma,tetpil,i,j,k,kk,nc,nq,lx,ly;
  GEN h,modulist,unitlist,classlist,sous,sousu,sousclass,p2,m,bid,q,cyclic;

  if (typ(listes)!=t_VEC || lg(listes)!=3) err(typeer,"rayclassnolist");
  bnf = checkbnf(bnf); h=gmael3(bnf,8,1,1);
  modulist=(GEN)listes[1]; unitlist=(GEN)listes[2];
  lx=lg(modulist); classlist=cgetg(lx,t_VEC);
  for (i=1; i<lx; i++)
  {
    sous=(GEN)modulist[i]; sousu=(GEN)unitlist[i]; ly=lg(sous);
    sousclass=cgetg(ly,t_VEC); classlist[i]=(long)sousclass;
    for (j=1; j<ly; j++)
    {
      bid=(GEN)sous[j]; q=(GEN)sousu[j]; nq=lg(q)-1;
      cyclic=gmael(bid,2,2); nc=lg(cyclic)-1;
      if (lg(q[1]) != nc+1) err(bugparier,"rayclassnolist");
      m=cgetg(nq+nc+1,t_MAT);
      for (k=1; k<=nq; k++) m[k]=q[k];
      for (   ; k<=nq+nc; k++)
      {
	p2=cgetg(nc+1,t_COL); m[k]=(long)p2;
	for (kk=1; kk<=nc; kk++) p2[kk]=(kk==k-nq)?cyclic[kk]:zero;
      }
      sousclass[j] = lmul(h,dethnf(hnf(m)));
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(classlist));
}

static GEN
rayclassnolistes(GEN sous, GEN sousclass, GEN fac)
{
  long i;
  for (i=1; i<lg(sous); i++)
    if (gegal(gmael(sous,i,3),fac)) return (GEN)sousclass[i];
  err(bugparier,"discrayabslist");
  return NULL; /* not reached */
}

static GEN
rayclassnolistessimp(GEN sous, GEN fac)
{
  long i;
  for (i=1; i<lg(sous); i++)
    if (gegal(gmael(sous,i,1),fac)) return gmael(sous,i,2);
  err(bugparier,"discrayabslistlong");
  return NULL; /* not reached */
}

static GEN
factormul(GEN fa1,GEN fa2)
{
  GEN pr,prnew,ex,exnew,v,p,y=cgetg(3,t_MAT);
  long i,c,lx;

  pr=concatsp((GEN)fa1[1],(GEN)fa2[1]); y[1]=(long)pr;
  ex=concatsp((GEN)fa1[2],(GEN)fa2[2]); y[2]=(long)ex;
  v=sindexsort(pr); lx=lg(pr);
  prnew=cgetg(lx,t_COL); exnew=cgetg(lx,t_COL);
  for (i=1; i<lx; i++) prnew[i]=pr[v[i]];
  for (i=1; i<lx; i++) exnew[i]=ex[v[i]];
  p=gzero; c=0;
  for (i=1; i<lx; i++)
  {
    if (gegal((GEN)prnew[i],p))
      ex[c]=laddii((GEN)ex[c],(GEN)exnew[i]);
    else
    {
      c++; p=(GEN)prnew[i]; pr[c]=(long)p; ex[c]=exnew[i];
    }
  }
  setlg(pr,c+1); setlg(ex,c+1); return y;
}

static GEN
factordivexact(GEN fa1,GEN fa2)
{
  long i,j,k,c,lx1,lx2;
  GEN listpr,listex,y,listpr1,listex1,listpr2,listex2,p1;

  listpr1=(GEN)fa1[1]; listex1=(GEN)fa1[2]; lx1=lg(listpr1);
  listpr2=(GEN)fa2[1]; listex2=(GEN)fa2[2]; lx2=lg(listpr1);
  y=cgetg(3,t_MAT);
  listpr=cgetg(lx1,t_COL); y[1]=(long)listpr;
  listex=cgetg(lx1,t_COL); y[2]=(long)listex;
  for (c=0,i=1; i<lx1; i++)
  {
    j=isinvector(listpr2,(GEN)listpr1[i],lx2-1);
    if (!j) { c++; listpr[c]=listpr1[i]; listex[c]=listex1[i]; }
    else
    {
      p1=subii((GEN)listex1[i],(GEN)listex2[j]); k=signe(p1);
      if (k<0) err(talker,"factordivexact is not exact!");
      if (k>0) { c++; listpr[c]=listpr1[i]; listex[c]=(long)p1; }
    }
  }
  setlg(listpr,c+1); setlg(listex,c+1); return y;
}

static GEN
factorpow(GEN fa,long n)
{
  GEN y=cgetg(3,t_MAT);

  if (!n) { y[1]=lgetg(1,t_COL); y[2]=lgetg(1,t_COL); return y; }
  y[1]=fa[1]; y[2]=lmulsg(n,(GEN)fa[2]); return y;
}

/*   Etant donne la liste des zidealstarinit et des matrices d'unites
 * correspondantes, sort la liste des discrayabs. On ne garde pas les modules
 * qui ne sont pas des conducteurs
 */
GEN
discrayabslist(GEN bnf,GEN listes)
{
  long av=avma,tetpil,ii,jj,i,j,k,clhss,ep,clhray,lx,ly,r1,som,degk,nbdezero;
  long n,R1,normps,normi,lfa2;
  GEN classlist,modulist,disclist,nf,dkabs,sous,sousclass,sousdisc;
  GEN bid,module,ideal,arch,fa,fa2,ex,idealrel,p1,p2,pr;
  GEN dlk,arch2,p3,fac,normp,fad,fad1,fad2,no1,no2;

  classlist=rayclassnolist(bnf,listes); lx=lg(classlist);
  modulist=(GEN)listes[1];
  disclist=cgetg(lx,t_VEC); nf=(GEN)bnf[7]; r1=itos(gmael(nf,2,1));
  degk=lgef(nf[1])-3; dkabs=gabs((GEN)nf[3],0);
  nbdezero = 0; dlk = NULL; /* gcc -Wall */
  for (ii=1; ii<lx; ii++)
  {
    sous=(GEN)modulist[ii]; sousclass=(GEN)classlist[ii];
    ly=lg(sous); sousdisc=cgetg(ly,t_VEC); disclist[ii]=(long)sousdisc;
    for (jj=1; jj<ly; jj++)
    {
      bid=(GEN)sous[jj]; clhray=itos((GEN)sousclass[jj]);
      module=(GEN)bid[1]; ideal=(GEN)module[1]; arch=(GEN)module[2];
      fa=(GEN)bid[3]; fa2=(GEN)fa[1]; ex=(GEN)fa[2]; fac=gcopy(fa);
      idealrel=cgetg(3,t_MAT);
      idealrel[1]=lgetg(1,t_COL);
      idealrel[2]=lgetg(1,t_COL); lfa2=lg(fa2);
      for (k=1; k<lfa2; k++)
      {
	pr=(GEN)fa2[k]; ep=itos((GEN)ex[k]); som=0;
	normp=gpui((GEN)pr[1],(GEN)pr[4],0);
	normps=itos(normp); normi=ii;
	normp=cgetg(3,t_MAT);
	no1=cgetg(2,t_COL); no1[1]=pr[1]; normp[1]=(long)no1;
	no2=cgetg(2,t_COL); no2[1]=pr[4]; normp[2]=(long)no2;
	for (j=1; j<=ep; j++)
	{
          if (j<ep) { coeff(fac,k,2)=lstoi(ep-j); fad=fac; }
          else
          {
            fad=cgetg(3,t_MAT);
            fad1=cgetg(lfa2-1,t_COL); fad[1]=(long)fad1;
            fad2=cgetg(lfa2-1,t_COL); fad[2]=(long)fad2;
            for (i=1; i<k; i++)
              { fad1[i]=coeff(fac,i,1); fad2[i]=coeff(fac,i,2); }
            for (   ; i<lfa2-1; i++)
              { fad1[i]=coeff(fac,i+1,1); fad2[i]=coeff(fac,i+1,2); }
          }
          normi /= normps;
          clhss = itos(rayclassnolistes((GEN)modulist[normi],
                                        (GEN)classlist[normi],fad));
          if (j==1 && clhss==clhray)
	  {
	    clhray=0; coeff(fac,k,2)=ex[k]; goto LLDISCRAY;
	  }
          if (clhss==1) { som += ep-j+1; break; }
          som += clhss;
	}
	coeff(fac,k,2)=ex[k];
	idealrel=factormul(idealrel,factorpow(normp,som));
      }
      dlk=factordivexact(factorpow(factor(stoi(ii)),clhray),idealrel);
      p2=cgetg(3,t_VEC);
      p2[1]=(long)ideal; arch2=dummycopy(arch);
      p2[2]=(long)arch2; nbdezero=0;
      for (k=1; k<=r1; k++)
      {
	if (signe(arch[k]))
	{
	  arch2[k]=zero;
	  clhss=itos(rayclassno(bnf,p2));
	  arch2[k]=un;
	  if (clhss==clhray) { clhray=0; break; }
	}
	else nbdezero++;
      }
    LLDISCRAY:
      if (!clhray) sousdisc[jj]=lgetg(1,t_VEC);
      else
      {
	p3=factorpow(factor(dkabs),clhray); n=clhray*degk; R1=nbdezero*clhray;
	if (((n-R1)&3) == 2)
	{
	  normp=cgetg(3,t_MAT);
	  no1=cgetg(2,t_COL); normp[1]=(long)no1; no1[1]=lstoi(-1);
	  no2=cgetg(2,t_COL); normp[2]=(long)no2; no2[1]=un;
	  dlk=factormul(normp,dlk);
	}
	p1=cgetg(4,t_VEC); p1[1]=lstoi(n);
	p1[2]=lstoi(R1); p1[3]=(long)factormul(dlk,p3);
	sousdisc[jj]=(long)p1;
      }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(disclist));
}

#define SHLGVINT 15
#define LGVINT 32768 /* must be 1<<SHLGVINT */

/* Attention: bound est le nombre de vraies composantes voulues. */
static GEN
bigcgetvec(long bound)
{
  long nbcext,nbfinal,i;
  GEN vext;

  nbcext = ((bound-1)>>SHLGVINT)+1;
  nbfinal = bound-((nbcext-1)<<SHLGVINT);
  vext = cgetg(nbcext+1,t_VEC);
  for (i=1; i<nbcext; i++) vext[i]=lgetg(LGVINT+1,t_VEC);
  vext[nbcext]=lgetg(nbfinal+1,t_VEC); return vext;
}

static GEN
getcompobig(GEN vext,long i)
{
  long cext;

  if (i<=LGVINT) return gmael(vext,1,i);
  cext=((i-1)>>SHLGVINT)+1;
  return gmael(vext,cext,i-((cext-1)<<SHLGVINT));
}

static void
putcompobig(GEN vext,long i,GEN x)
{
  long cext;

  if (i<=LGVINT) { mael(vext,1,i)=(long)x; return; }
  cext=((i-1)>>SHLGVINT)+1; mael(vext,cext,i-((cext-1)<<SHLGVINT))=(long)x;
  return;
}

static GEN
zsimp(GEN bid, GEN matunit)
{
  GEN y=cgetg(5,t_VEC);
  y[1]=lcopy((GEN)bid[3]); y[2]=lcopy(gmael(bid,2,2));
  y[3]=lcopy((GEN)bid[5]); y[4]=lcopy(matunit); return y;
}

static GEN
zsimpjoin(GEN bidsimp, GEN bidp, GEN faussefa, GEN matunit)
{
  long i,j,lx,lx1,lx2,llx,llx1,llx2,nbgen,av=avma,tetpil,c;
  GEN y,U1,U2,cyclic1,cyclic2,U,cyc,u1u2,p1,p2,met;

  y=cgetg(5,t_VEC); y[1]=(long)vconcat((GEN)bidsimp[1],faussefa);
  U1=(GEN)bidsimp[3]; U2=(GEN)bidp[5]; cyclic1=(GEN)bidsimp[2];
  cyclic2=gmael(bidp,2,2); lx1=lg(U1); lx2=lg(U2); lx=lx1+lx2-1;
  llx1=lg(cyclic1); llx2=lg(cyclic2);
  llx=llx1+llx2-1; nbgen=llx-1; U=cgetg(lx,t_MAT);
  if (nbgen)
  {
    cyc=diagonal(concatsp(cyclic1,cyclic2));
    u1u2=smithclean(smith2(cyc)); met=(GEN)u1u2[3]; c=lg(met)-1;
    for (j=1; j<lx1; j++)
    {
      p1=cgetg(llx,t_COL); p2=(GEN)U1[j]; U[j]=(long)p1;
      for (i=1; i<llx1; i++) p1[i]=p2[i];
      for (   ; i<llx; i++) p1[i]=zero;
    }
    for (  ; j<lx; j++)
    {
      p1=cgetg(llx,t_COL); p2=(GEN)U2[j-lx1+1]; U[j]=(long)p1;
      for (i=1; i<llx1; i++) p1[i]=zero;
      for (   ; i<llx; i++) p1[i]=p2[i-llx1+1];
    }
    y[3]=lmul((GEN)u1u2[1],U);
  }
  else
  {
    met=cgetg(1,t_MAT); for (j=1; j<lx; j++) U[j]=lgetg(1,t_COL);
    y[3]=(long)U; c=0;
  }
  cyc=cgetg(c+1,t_VEC); for (i=1; i<=c; i++) cyc[i]=coeff(met,i,i);
  y[2]=(long)cyc;
  y[4]=(long)vconcat((GEN)bidsimp[4],matunit);
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
}

static GEN
rayclassnointern(GEN sous, GEN clh)
{
  long lx,nc,nq,k,kk,j;
  GEN bidsimp,qm,sousray,cyclic,m,p2,p1;

  lx=lg(sous); sousray=cgetg(lx,t_VEC);
  for (j=1; j<lx; j++)
  {
    bidsimp=(GEN)sous[j]; qm=gmul((GEN)bidsimp[3],(GEN)bidsimp[4]);
    nq=lg(qm)-1; cyclic=(GEN)bidsimp[2]; nc=lg(cyclic)-1;
    if (lg(qm[1]) != nc+1) err(bugparier,"rayclassnolist");
    m=cgetg(nq+nc+1,t_MAT);
    for (k=1; k<=nq; k++) m[k]=qm[k];
    for (   ; k<=nq+nc; k++)
    {
      p2=cgetg(nc+1,t_COL); m[k]=(long)p2;
      for (kk=1; kk<=nc; kk++) p2[kk]=(kk==k-nq)?cyclic[kk]:zero;
    }
    p1=cgetg(3,t_VEC); p1[2]=lmul(clh,dethnf(hnf(m)));
    p1[1]=bidsimp[1]; sousray[j]=(long)p1;
  }
  return sousray;
}

static GEN
rayclassnointernarch(GEN sous, GEN clh, GEN matarchunit)
{
  long lx,nc,nq,k,kk,j,lm,lh,r1,jj,i,nba,nbarch,ii;
  GEN bidsimp,qm,sousray,cyclic,m,p2,p1,p1all,p3,mm,mj,qmk,matk;

  if (!matarchunit) return rayclassnointern(sous,clh);

  lm=lg(matarchunit); if (!lm) err(talker,"no units in rayclassnointernarch");
  r1=lg(matarchunit[1])-1; if (r1>15) err(talker,"r1>15 in rayclassnointernarch");
  lx=lg(sous); sousray=cgetg(lx,t_VEC);
  for (j=1; j<lx; j++)
  {
    bidsimp=(GEN)sous[j]; qm=gmul((GEN)bidsimp[3],(GEN)bidsimp[4]);
    nq=lg(qm)-1; cyclic=(GEN)bidsimp[2]; nc=lg(cyclic)-1;
    if (lm != nq+1) err(bugparier,"rayclassnointernarch (1)");
    if (lg(qm[1]) != nc+1) err(bugparier,"rayclassnointernarch (2)");
    m=cgetg(nq+nc+r1+1,t_MAT);
    for (k=1; k<=nq; k++)
    {
      p2=cgetg(nc+r1+1,t_COL); m[k]=(long)p2; qmk=(GEN)qm[k];
      matk=(GEN)matarchunit[k];
      for (kk=1; kk<=nc; kk++) p2[kk]=qmk[kk];
      for (    ; kk<=nc+r1; kk++) p2[kk]=matk[kk-nc];
    }
    for (  ; k<=nq+nc; k++)
    {
      p2=cgetg(nc+r1+1,t_COL); m[k]=(long)p2;
      for (kk=1; kk<=nc+r1; kk++) p2[kk]=(kk==k-nq)?cyclic[kk]:zero;
    }
    for (   ; k<=nq+nc+r1; k++)
    {
      p2=cgetg(nc+r1+1,t_COL); m[k]=(long)p2;
      for (kk=1; kk<=nc+r1; kk++) p2[kk]=(kk==k-nq)?deux:zero;
    }
    m=hnf(m);
    nbarch=(1<<r1); p1all=cgetg(nbarch+1,t_VEC); lh=lg(m);
    if (lh!=nc+r1+1) err(bugparier,"rayclassnointernarch (3)");
    for (k=0; k<=nbarch-1; k++)
    {
      p2=cgetg(r1+1,t_COL); kk=k; nba=0;
      for (jj=1; jj<=r1; jj++)
      {
	if (kk%2) { nba++; p2[jj]=un; } else p2[jj]=zero;
	kk>>=1;
      }
      mm=cgetg(lh,t_MAT);
      for (jj=1; jj<lh; jj++)
      {
	p3=cgetg(nc+nba+1,t_COL); mm[jj]=(long)p3; mj=(GEN)m[jj];
	for (i=1; i<=nc; i++) p3[i]=mj[i];
	for (ii=1; ii<=r1; ii++)
          if (signe(p2[ii])) p3[i++]=mj[nc+ii];
      }
      p1all[k+1]=lmul(clh,dethnf(hnf(mm)));
    }
    p1=cgetg(3,t_VEC); p1[2]=(long)p1all; p1[1]=bidsimp[1];
    sousray[j]=(long)p1;
  }
  return sousray;
}

GEN
decodemodule(GEN nf, GEN fa)
{
  long n,k,j,fauxpr,av=avma;
  GEN fa2,ex,id,pr;

  nf=checknf(nf);
  if (typ(fa)!=t_MAT || lg(fa)!=3)
    err(talker,"incorrect factorisation in decodemodule");
  n=lgef(nf[1])-3; id=idmat(n);
  fa2=(GEN)fa[1]; ex=(GEN)fa[2];
  for (k=1; k<lg(fa2); k++)
  {
    fauxpr=itos((GEN)fa2[k]);
    j=(fauxpr%n)+1; fauxpr /= n*n;
    pr = (GEN)primedec(nf,stoi(fauxpr))[j];
    id = idealmul(nf,id,idealpow(nf,pr,(GEN)ex[k]));
  }
  return gerepileupto(av,id);
}

/*   Fait tout a partir du debut, et bound peut aller jusqu'a 2^30. Pour
 * l'instant ne s'occupe pas des sous-groupes.   le format de sortie est le
 * suivant: un vecteur vext dont les composantes vint ont exactement 2^LGVINT
 * vraies composantes sauf le dernier qui peut etre plus court. vext[i][j]
 * (ou j<=2^LGVINT) doit etre compris comme la composante d'indice
 * I=(i-1)*2^LGVINT+j d'un grand vecteur unique V.  Une telle composante
 * d'indice I est un vecteur indexe par tous les ideaux de norme egal a I. Si
 * m_0 est un tel ideal, la composante correspondante est la suivante:
 *
 *  + si arch = NULL, on parcourt toutes les parties archimediennes possibles.
 * L'ordre des arch est l'ordre lexicographique inverse, donc [0,0,..,0],
 * [1,0,..,0], [0,1,..,0],... Dans ce cas: [m_0,V] ou V est un vecteur de
 * 2^r1 composantes, donnant pour chaque arch, le triplet [N,R1,D], ou N, R1,
 * D sont comme dans discrayabs sauf que D est sous forme factorisee.
 *
 * + sinon [m_0,arch,N,R1,D], ou N, R1, D sont comme ci-dessus.
 *
 * Si ramip est different de 0 et -1, ne prend que les modules sans facteur
 * carres ailleurs qu'au dessus de ramip. Si ramip est strictement negatif,
 * archsquare.
 */
static GEN
discrayabslistarchintern(GEN bnf, GEN arch, long bound, long ramip)
{
  byteptr ptdif=diffptr;
  long degk,lim,av0,av,av1,tetpil,i,j,k,p2s,lfa,lp1,sqbou,cex, allarch;
  long ffs,fs,resp,flbou,tdi,nba, k2,karch,kka,nbarch,jjj,jj,square;
  long ii2,ii,ly,clhray,lfa2,ep,som,clhss,normps,normi,nbdezero,r1,R1,n,c;
  ulong q;
  GEN nf,p,z,pol,p1,p2,p3,fa,pr,normp,ideal,bidp,z2,matarchunit;
  GEN bigres,funits,racunit,embunit,sous,clh,sousray,raylist;
  GEN clhrayall,discall,faall,Id,idealrel,idealrelinit;
  GEN sousdisc,module,fa2,ex,fac,no1,no2,fad,fad1,fad2,fadkabs,pz;
  GEN arch2,dlk,disclist,bidsimp,p4,faussefa,pex,fauxpr,gprime;
  GEN *gptr[2];

  clhray = nbdezero = 0; /* gcc -Wall */
  module = Id = dlk = ideal = clhrayall = discall = faall = NULL;

  /* ce qui suit recopie d'assez pres ideallistzstarall */
  if (DEBUGLEVEL>2) timer2();
  if (bound <= 0) err(talker,"non-positive bound in discrayabslist");
  av0=avma; bnf = checkbnf(bnf); flbou=0;
  nf=(GEN)bnf[7]; bigres=(GEN)bnf[8]; pol=(GEN)nf[1]; degk=lgef(pol)-3;
  r1=itos(gmael(nf,2,1)); fadkabs=factor(absi((GEN)nf[3]));
  clh=gmael(bigres,1,1);
  funits = check_units(bnf,"discrayabslistarchintern");
  racunit=gmael(bigres,4,2);

  if (ramip >= 0) square = 0;
  else
  {
    square = 1; ramip = -ramip;
    if (ramip==1) ramip=0;
  }
  nba = 0; allarch = (arch==NULL);
  if (allarch)
    { arch=cgetg(r1+1,t_VEC); for (i=1; i<=r1; i++) arch[i]=un; nba=r1; }
  else if (gcmp0(arch))
    { arch=cgetg(r1+1,t_VEC); for (i=1; i<=r1; i++) arch[i]=zero; }
  else
  {
    if (lg(arch)!=r1+1)
      err(talker,"incorrect archimedean argument in discrayabslistlong");
    for (i=1; i<=r1; i++) if (signe(arch[i])) nba++;
    if (nba) module=cgetg(3,t_VEC);
  }
  p1=cgetg(3,t_VEC); p1[1]=(long)idmat(degk); p1[2]=(long)arch;
  bidp=zidealstarinitall(nf,p1,0);
  matarchunit = allarch? logunitmatrix(nf,funits,racunit,bidp): (GEN)NULL;

  p=cgeti(3); p[1]=evalsigne(1)|evallgef(3);
  sqbou=itos(racine(stoi(bound)))+1;
  av=avma; lim=stack_lim(av,1);
  z=bigcgetvec(bound); for (i=2; i<=bound; i++) putcompobig(z,i,cgetg(1,t_VEC));
  if (allarch) bidp=zidealstarinitall(nf,idmat(degk),0);
  embunit=logunitmatrix(nf,funits,racunit,bidp);
  p1=cgetg(2,t_VEC); putcompobig(z,1,p1); p1[1]=(long)zsimp(bidp,embunit);
  if (DEBUGLEVEL>=2) fprintferr("Starting zidealstarunits computations\n");
  for (p[2]=0; p[2]<=bound; )
  {
    if (!*ptdif) err(primer1);
    p[2] += *ptdif++;
    if (!flbou && p[2]>sqbou)
    {
      flbou=1;
      if (DEBUGLEVEL>=2)
        { fprintferr("\nStarting rayclassno computations\n"); flusherr(); }
      tetpil=avma; z=gerepile(av,tetpil,gcopy(z));
      av1=avma; raylist=bigcgetvec(bound);
      /* maintenant on suit rayclassnolist */
      for (i=1; i<=bound; i++)
      {
	sous=getcompobig(z,i);
        sousray=rayclassnointernarch(sous,clh,matarchunit);
	putcompobig(raylist,i,sousray);
      }
      tetpil=avma; raylist=gerepile(av1,tetpil,gcopy(raylist));
      z2=bigcgetvec(sqbou);
      for (i=1; i<=sqbou; i++)
        { p1=gcopy(getcompobig(z,i)); putcompobig(z2,i,p1); }
      z = z2;
    }
    fa=primedec(nf,p); lfa=lg(fa)-1;
    for (j=1; j<=lfa; j++)
    {
      pr=(GEN)fa[j]; normp=powgi(p,(GEN)pr[4]); cex=0;
      if (DEBUGLEVEL>=2) { fprintferr("%ld ",p[2]); flusherr(); }
      if (gcmpgs(normp,bound)<=0)
      {
	fauxpr=stoi(p[2]*degk*degk+(itos((GEN)pr[4])-1)*degk+j-1);
	q=p2s=itos(normp); ideal=pr;
	while (q <= (ulong)bound)
	{
	  bidp=zidealstarinitall(nf,ideal,0);
	  faussefa=cgetg(3,t_MAT); p1=cgetg(2,t_COL);
	  faussefa[1]=(long)p1; p1[1]=(long)fauxpr;
	  pex=cgetg(2,t_COL); faussefa[2]=(long)pex;
	  cex++; pex[1]=lstoi(cex);
	  embunit=logunitmatrix(nf,funits,racunit,bidp);
	  for (i=q; i<=bound; i+=q)
	  {
	    p1=getcompobig(z,i/q); lp1=lg(p1);
	    if (lp1>1)
	    {
	      p2=cgetg(lp1,t_VEC); c=0;
	      for (k=1; k<lp1; k++)
	      {
		p3=(GEN)p1[k];
		if (i==q ||
                    ((p4=gmael(p3,1,1)) && !isinvector(p4,fauxpr,lg(p4)-1)))
		{
		  c++;
		  p2[c]=(long)zsimpjoin(p3,bidp,faussefa,embunit);
		}
	      }
	      setlg(p2,c+1);
	      if (c)
	      {
		if (p[2]<=sqbou)
		{
		  pz=getcompobig(z,i);
		  if (lg(pz)>1) putcompobig(z,i,concatsp(pz,p2));
		  else putcompobig(z,i,p2);
		}
		else
                {
                  sousray=rayclassnointernarch(p2,clh,matarchunit);
                  pz=getcompobig(raylist,i);
                  if (lg(pz)>1) putcompobig(raylist,i,concatsp(pz,sousray));
                  else putcompobig(raylist,i,sousray);
                }
	      }
	    }
	  }
	  if (ramip && ramip % p[2]) q=bound+1;
	  else
	  {
	    pz=mulss(q,p2s);
	    q=(gcmpgs(pz,bound)>0)?bound+1:pz[2];
            if (q <= (ulong)bound) ideal=idealmul(nf,ideal,pr);
	  }
	}
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"[1]: discrayabslistarch");
      if (!flbou)
      {
	if (DEBUGLEVEL>2)
          fprintferr("avma = %ld, t(z) = %ld ",avma-bot,taille2(z));
        tetpil=avma; z=gerepile(av,tetpil,gcopy(z));
      }
      else
      {
	if (DEBUGLEVEL>2)
	  fprintferr("avma = %ld, t(r) = %ld ",avma-bot,taille2(raylist));
	gptr[0]=&z; gptr[1]=&raylist; gerepilemany(av,gptr,2);
      }
      if (DEBUGLEVEL>2) { fprintferr("avma = %ld ",avma-bot); flusherr(); }
    }
  }
  if (!flbou) /* maintenant on suit rayclassnolist */
  {
    if (DEBUGLEVEL>=2)
    { fprintferr("\nStarting rayclassno computations\n"); flusherr(); }
    tetpil=avma; z=gerepile(av,tetpil,gcopy(z));
    av1=avma; raylist=bigcgetvec(bound);
    for (i=1; i<=bound; i++)
    {
      sous=getcompobig(z,i);
      sousray=rayclassnointernarch(sous,clh,matarchunit);
      putcompobig(raylist,i,sousray);
    }
  }
  if (DEBUGLEVEL>2)
    fprintferr("avma = %ld, t(r) = %ld ",avma-bot,taille2(raylist));
  tetpil=avma; raylist=gerepile(av,tetpil,gcopy(raylist));
  if (DEBUGLEVEL>2)
    { fprintferr("avma = %ld ",avma-bot); msgtimer("zidealstarlist"); }
  /* maintenant on suit discrayabslist */
  if (DEBUGLEVEL>=2)
    { fprintferr("Starting discrayabs computations\n"); flusherr(); }

  if (allarch) nbarch = 1<<r1;
  else
  {
    nbarch = 1;
    clhrayall = cgetg(2,t_VEC);
    discall = cgetg(2,t_VEC);
    faall = cgetg(2,t_VEC);
    Id = idmat(degk);
  }
  idealrelinit=cgetg(3,t_MAT);
  idealrelinit[1]=lgetg(1,t_COL);
  idealrelinit[2]=lgetg(1,t_COL);
  av1=avma; lim=stack_lim(av1,1);
  if (square) bound = sqbou-1;
  disclist=bigcgetvec(bound);
  for (ii=1; ii<=bound; ii++) putcompobig(disclist,ii,cgetg(1,t_VEC));
  for (ii2=1; ii2<=bound; ii2++)
  {
    ii = square? ii2*ii2: ii2;
    if (DEBUGLEVEL>=2 && ii%100==0) { fprintferr("%ld ",ii); flusherr(); }
    sous=getcompobig(raylist,ii); ly=lg(sous); sousdisc=cgetg(ly,t_VEC);
    putcompobig(disclist, square? ii2: ii,sousdisc);
    for (jj=1; jj<ly; jj++)
    {
      bidsimp=(GEN)sous[jj]; fa=(GEN)bidsimp[1]; fac=gcopy(fa);
      fa2=(GEN)fa[1]; ex=(GEN)fa[2]; lfa2=lg(fa2);

      if (allarch)
      {
        clhrayall = (GEN)bidsimp[2];
        discall=cgetg(nbarch+1,t_VEC);
      }
      else
        clhray = itos((GEN)bidsimp[2]);
      for (karch=0; karch<nbarch; karch++)
      {
        if (!allarch) ideal = Id;
        else
        {
          kka=karch; nba=0;
          for (jjj=1; jjj<=r1; jjj++)
          {
            if (kka%2) nba++;
            kka>>=1;
          }
          clhray=itos((GEN)clhrayall[karch+1]);
          for (k2=1,k=1; k<=r1; k++,k2<<=1)
          {
            if (karch&k2 && clhray==itos((GEN)clhrayall[karch-k2+1]))
              { clhray=0; goto LDISCRAY; }
          }
        }
        idealrel = idealrelinit;
        for (k=1; k<lfa2; k++)
        {
          fauxpr=(GEN)fa2[k]; ep=itos((GEN)ex[k]); ffs=itos(fauxpr);
          /* Hack for NeXTgcc 2.5.8 -- splitting "resp=fs%degk+1" */
          fs=ffs/degk; resp=fs%degk; resp++; gprime=stoi((long)(fs/degk));
          if (!allarch && nba)
          {
            p1=(GEN)primedec(nf,gprime)[ffs%degk+1];
            ideal = idealmul(nf,ideal,idealpow(nf,p1,(GEN)ex[k]));
          }
          som=0; clhss=0;
          normp=gpuigs(gprime,resp); normps=itos(normp); normi=ii;
          normp=cgetg(3,t_MAT);
          no1=cgetg(2,t_COL); no1[1]=(long)gprime; normp[1]=(long)no1;
          no2=cgetg(2,t_COL); no2[1]=lstoi(resp); normp[2]=(long)no2;
          for (j=1; j<=ep; j++)
          {
            if (clhss==1) som++;
            else
            {
              if (j<ep) { coeff(fac,k,2)=lstoi(ep-j); fad=fac; }
              else
              {
                fad=cgetg(3,t_MAT);
                fad1=cgetg(lfa2-1,t_COL); fad[1]=(long)fad1;
                fad2=cgetg(lfa2-1,t_COL); fad[2]=(long)fad2;
                for (i=1; i<k; i++)
                  { fad1[i]=coeff(fac,i,1); fad2[i]=coeff(fac,i,2); }
                for (   ; i<lfa2-1; i++)
                  { fad1[i]=coeff(fac,i+1,1); fad2[i]=coeff(fac,i+1,2); }
              }
              normi /= normps;
	      /* Hack for NeXTgcc 2.5.8 -- using dlk as temporary variable */
	      dlk=rayclassnolistessimp(getcompobig(raylist,normi),fad);
              if (allarch) dlk = (GEN)dlk[karch+1];
	      clhss = itos(dlk);
              if (j==1 && clhss==clhray)
	      {
		clhray=0; coeff(fac,k,2)=ex[k]; goto LDISCRAY;
	      }
              som += clhss;
            }
          }
          coeff(fac,k,2)=ex[k];
          idealrel=factormul(idealrel,factorpow(normp,som));
        }
        dlk=factordivexact(factorpow(factor(stoi(ii)),clhray),idealrel);
        if (!allarch && nba)
        {
          module[1]=(long)ideal; arch2=gcopy(arch); module[2]=(long)arch2;
          nbdezero=0;
          for (k=1; k<=r1; k++)
          {
            if (signe(arch[k]))
            {
              arch2[k]=zero;
              clhss=itos(rayclassno(bnf,module));
              arch2[k]=un;
              if (clhss==clhray) { clhray=0; goto LDISCRAY; }
            }
            else nbdezero++;
          }
        }
        else nbdezero = r1-nba;
LDISCRAY:
        p1=cgetg(4,t_VEC); discall[karch+1]=(long)p1;
	if (!clhray) p1[1]=p1[2]=p1[3]=zero;
	else
	{
	  p3=factorpow(fadkabs,clhray); n=clhray*degk; R1=nbdezero*clhray;
	  if (((n-R1)&3)==2)
	  {
	    normp=cgetg(3,t_MAT);
            no1=cgetg(2,t_COL); normp[1]=(long)no1; no1[1]=lstoi(-1);
	    no2=cgetg(2,t_COL); normp[2]=(long)no2; no2[1]=un;
	    dlk=factormul(normp,dlk);
	  }
	  p1[1]=lstoi(n); p1[2]=lstoi(R1); p1[3]=(long)factormul(dlk,p3);
	}
      }
      if (allarch)
        { p1 = cgetg(3,t_VEC); p1[1]=(long)fa; p1[2]=(long)discall; }
      else
        { faall[1]=(long)fa; p1 = concatsp(faall, p1); }
      sousdisc[jj]=(long)p1;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"[2]: discrayabslistarch");
        if (DEBUGLEVEL>2)
          fprintferr("avma = %ld, t(d) = %ld ",avma-bot,taille2(disclist));
        tetpil=avma; disclist=gerepile(av1,tetpil,gcopy(disclist));
        if (DEBUGLEVEL>2) { fprintferr("avma = %ld ",avma-bot); flusherr(); }
      }
    }
  }
  if (DEBUGLEVEL>2) msgtimer("discrayabs");
  tdi=taille2(disclist);
  if (DEBUGLEVEL>2)
  { fprintferr("avma = %ld, t(d) = %ld ",avma-bot,tdi); flusherr(); }
  if (tdi<avma-bot)
  {
    tetpil=avma; disclist=gerepile(av0,tetpil,gcopy(disclist));
    if (DEBUGLEVEL>2) { fprintferr("avma = %ld ",avma-bot); flusherr(); }
  }
  return disclist;
}

GEN
discrayabslistarch(GEN bnf, GEN arch, long bound)
{ return discrayabslistarchintern(bnf,arch,bound, 0); }

GEN
discrayabslistlong(GEN bnf, long bound)
{ return discrayabslistarchintern(bnf,gzero,bound, 0); }

GEN
discrayabslistarchsquare(GEN bnf, GEN arch, long bound)
{ return discrayabslistarchintern(bnf,arch,bound, -1); }

static GEN
computehuv(GEN bnr,GEN id, GEN arch,long prec)
{
  long i,nbgen, av = avma;
  GEN bnf,bnrnew,listgen,P,U,DC;
  GEN newmod=cgetg(3,t_VEC);
  newmod[1]=(long)id;
  newmod[2]=(long)arch;

  bnf=(GEN)bnr[1];
  bnrnew=buchrayall(bnf,newmod,nf_INIT,prec);
  listgen=gmael(bnr,5,3); nbgen=lg(listgen);
  P=cgetg(nbgen,t_MAT);
  for (i=1; i<nbgen; i++)
    P[i] = (long)isprincipalray(bnrnew,(GEN)listgen[i]);
  DC=diagonal(gmael(bnrnew,5,2));
  U=(GEN)hnfall(concatsp(P,DC))[2];
  setlg(U,nbgen); for (i=1; i<nbgen; i++) setlg(U[i], nbgen);
  return gerepileupto(av, hnf(concatsp(U,diagonal(gmael(bnr,5,2)))));
}

/* 0 if hinv*list[i] has a denominator for all i, 1 otherwise */
static int
hnflistdivise(GEN list,GEN h)
{
  long av = avma, i, I = lg(list);
  GEN hinv = ginv(h);

  for (i=1; i<I; i++)
    if (gcmp1(denom(gmul(hinv,(GEN)list[i])))) break;
  avma = av; return i < I;
}

static GEN
subgroupcond(GEN bnr, long indexbound, long prec)
{
  long av=avma,tetpil,i,j,lgi,lp;
  GEN li,p1,lidet,perm,nf,bid,ideal,arch,primelist,listkernels;

  checkbnrgen(bnr); bid=(GEN)bnr[2];
  ideal=gmael(bid,1,1);
  arch =gmael(bid,1,2); nf=gmael(bnr,1,7);
  primelist=gmael(bid,3,1); lp=lg(primelist)-1;
  listkernels=cgetg(lp+lg(arch),t_VEC);
  for (i=1; i<=lp; )
  {
    p1=idealdiv(nf,ideal,(GEN)primelist[i]);
    listkernels[i++]=(long)computehuv(bnr,p1,arch,prec);
  }
  for (j=1; j<lg(arch); j++)
    if (signe((GEN)arch[j]))
    {
      p1=dummycopy(arch); p1[j]=zero;
      listkernels[i++]=(long)computehuv(bnr,ideal,p1,prec);
    }
  setlg(listkernels,i);

  li=subgrouplist(gmael(bnr,5,2),indexbound);
  lgi=lg(li);
  for (i=1,j=1; j<lgi; j++)
    if (!hnflistdivise(listkernels, (GEN)li[j])) li[i++] = li[j];
  /* sort by increasing index */
  lgi = i; setlg(li,i); lidet=cgetg(lgi,t_VEC);
  for (i=1; i<lgi; i++) lidet[i]=(long)dethnf_i((GEN)li[i]);
  perm = sindexsort(lidet); p1=li; li=cgetg(lgi,t_VEC);
  for (i=1; i<lgi; i++) li[i] = p1[perm[lgi-i]];
  tetpil=avma; return gerepile(av,tetpil,gcopy(li));
}

GEN
subgrouplist0(GEN bnr, long indexbound, long all, long prec)
{
  if (typ(bnr)!=t_VEC) err(typeer,"subgrouplist");
  if (lg(bnr)!=1 && typ(bnr[1])!=t_INT)
  {
    if (!all) return subgroupcond(bnr,indexbound,prec);
    checkbnr(bnr); bnr = gmael(bnr,5,2);
  }
  return subgrouplist(bnr,indexbound);
}

GEN
bnrdisclist0(GEN bnf, GEN borne, GEN arch, long all)
{
  if (typ(borne)==t_INT)
  {
    if (!arch) arch = gzero;
    if (all==1) { arch = NULL; all = 0; }
    return discrayabslistarchintern(bnf,arch,itos(borne),all);
  }
  return discrayabslist(bnf,borne);
}
