/*******************************************************************/
/*                                                                 */
/*                       BASIC NF OPERATIONS                       */
/*                           (continued)                           */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "parinf.h"

#define principalideal_aux(nf,x) (principalideal0((nf),(x),0))

GEN element_muli(GEN nf, GEN x, GEN y);

static GEN nfbezout(GEN nf, GEN a, GEN b, GEN ida, GEN idb, GEN *u, GEN *v, GEN *w, GEN *di);

/*******************************************************************/
/*                                                                 */
/*                     IDEAL OPERATIONS                            */
/*                                                                 */
/*******************************************************************/

/* A valid ideal is either principal (valid nf_element), or prime, or a matrix
 * on the integer basis (preferably HNF).
 * A prime ideal is of the form [p,a,e,f,b], where the ideal is p.Z_K+a.Z_K,
 * p is a rational prime, a belongs to Z_K, e=e(P/p), f=f(P/p), and b
 * Lenstra constant (p.P^(-1)= p Z_K + b Z_K).
 *
 * An idele is a couple[I,V] where I is a valid ideal and V a row vector
 * with r1+r2 components (real or complex). For instance, if M=(a), V
 * contains the complex logarithms of the first r1+r2 conjugates of a
 * (depends on the chosen generator a). All subroutines work with either
 * ideles or ideals (an omitted V is assumed to be 0).
 *
 * All the output ideals will be in HNF form.
 */

/* types and conversions */

static long
idealtyp(GEN *ideal, GEN *arch)
{
  GEN x = *ideal;
  long t,lx,tx = typ(x);

  if (tx==t_VEC && lg(x)==3)
  { *arch = (GEN)x[2]; x = (GEN)x[1]; tx = typ(x); }
  else
    *arch = NULL;
  switch(tx)
  {
    case t_MAT: lx = lg(x);
      if (lx>2) t = id_MAT;
      else
      {
        t = id_PRINCIPAL;
        x = (lx==2)? (GEN)x[1]: gzero;
      }
      break;

    case t_VEC: if (lg(x)!=6) err(idealer2);
      t = id_PRIME; break;

    case t_POL: case t_POLMOD: case t_COL:
      t = id_PRINCIPAL; break;
    default:
      if (tx!=t_INT && !is_frac_t(tx)) err(idealer2);
      t = id_PRINCIPAL;
  }
  *ideal = x; return t;
}

/* Assume ideal in HNF form */
long
ideal_is_zk(GEN ideal,long N)
{
  long i,j, lx = lg(ideal);

  if (typ(ideal) != t_MAT || lx==1) return 0;
  N++; if (lx != N || lg(ideal[1]) != N) return 0;
  for (i=1; i<N; i++)
  {
    if (!gcmp1(gcoeff(ideal,i,i))) return 0;
    for (j=i+1; j<N; j++)
      if (!gcmp0(gcoeff(ideal,i,j))) return 0;
  }
  return 1;
}

static GEN
prime_to_ideal_aux(GEN nf, GEN vp)
{
  GEN m,el;
  long i, N = lgef(nf[1])-3;

  m = cgetg(N+1,t_MAT); el = (GEN)vp[2];
  for (i=1; i<=N; i++) m[i] = (long) element_mulid(nf,el,i);
  return hnfmodid(m,(GEN)vp[1]);
}

GEN
prime_to_ideal(GEN nf, GEN vp)
{
  long av=avma;
  if (typ(vp) == t_INT) return gscalmat(vp, lgef(nf[1])-3);
  return gerepileupto(av, prime_to_ideal_aux(nf,vp));
}

/* x = ideal in matrix form. Put it in hnf. */
static GEN
idealmat_to_hnf(GEN nf, GEN x)
{
  long rx,i,j,N;
  GEN m,dx;

  N=lgef(nf[1])-3; rx=lg(x)-1;
  if (!rx) return gscalmat(gzero,N);

  dx=denom(x); if (gcmp1(dx)) dx = NULL; else x=gmul(dx,x);
  if (rx >= N) m = x;
  else
  {
    m=cgetg(rx*N + 1,t_MAT);
    for (i=1; i<=rx; i++)
      for (j=1; j<=N; j++)
        m[(i-1)*N + j] = (long) element_mulid(nf,(GEN)x[i],j);
  }
  x = hnfmod(m,detint(m));
  return dx? gdiv(x,dx): x;
}

int
ishnfall(GEN x)
{
  long i,j, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    if (gsigne(gcoeff(x,i,i)) <= 0) return 0;
    for (j=1; j<i; j++)
      if (!gcmp0(gcoeff(x,i,j))) return 0;
  }
  return (gsigne(gcoeff(x,1,1)) > 0);
}

GEN
idealhermite_aux(GEN nf, GEN x)
{
  long N,tx,lx;
  GEN z;

  tx = idealtyp(&x,&z);
  if (tx == id_PRIME) return prime_to_ideal_aux(nf,x);
  if (tx == id_PRINCIPAL)
  {
    x = principalideal(nf,x);
    return idealmat_to_hnf(nf,x);
  }
  N=lgef(nf[1])-3; lx = lg(x);
  if (lg(x[1]) != N+1) err(idealer2);

  if (lx == N+1 && ishnfall(x)) return x;
  if (lx <= N) return idealmat_to_hnf(nf,x);
  z=denom(x); if (gcmp1(z)) z=NULL; else x = gmul(z,x);
  x = hnfmod(x,detint(x));
  return z? gdiv(x,z): x;
}

GEN
idealhermite(GEN nf, GEN x)
{
  long av=avma;
  GEN p1;
  nf = checknf(nf); p1 = idealhermite_aux(nf,x);
  if (p1==x || p1==(GEN)x[1]) return gcopy(p1);
  return gerepileupto(av,p1);
}

static GEN
principalideal0(GEN nf, GEN x, long copy)
{
  GEN z = cgetg(2,t_MAT);
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      if (copy) x = gcopy(x);
      x = gscalcol_i(x, lgef(nf[1])-3); break;

    case t_POLMOD:
      if (!gegal((GEN)nf[1],(GEN)x[1]))
	err(talker,"incompatible number fields in principalideal");
      x=(GEN)x[2]; /* fall through */
    case t_POL:
      x = copy? algtobasis(nf,x): algtobasis_intern(nf,x);
      break;

    case t_MAT:
      if (lg(x)!=2) err(typeer,"principalideal");
      x = (GEN)x[1];
    case t_COL:
      if (lg(x)==lgef(nf[1])-2)
      {
        if (copy) x = gcopy(x);
        break;
      }
    default: err(typeer,"principalideal");
  }
  z[1]=(long)x; return z;
}

GEN
principalideal(GEN nf, GEN x)
{
  nf = checknf(nf); return principalideal0(nf,x,1);
}

static GEN
mylog(GEN x, long prec)
{
  if (gcmp0(x))
    err(talker,"precision too low in get_arch");
  return glog(x,prec);
}

/* for internal use */
GEN
get_arch(GEN nf,GEN x,long prec)
{
  long i,R1,RU;
  GEN v,p1,p2;

  R1=itos(gmael(nf,2,1)); RU = R1+itos(gmael(nf,2,2));
  if (typ(x)!=t_COL) x = algtobasis_intern(nf,x);
  if (isnfscalar(x)) /* rational number */
  {
    v = cgetg(RU+1,t_VEC);
    p1 = glog((GEN)x[1],prec);
    p2 = (RU > R1)? gmul2n(p1,1): NULL;
    for (i=1; i<=R1; i++) v[i]=(long)p1;
    for (   ; i<=RU; i++) v[i]=(long)p2;
  }
  else
  {
    x = gmul(gmael(nf,5,1),x); v = cgetg(RU+1,t_VEC);
    for (i=1; i<=R1; i++) v[i] = (long)mylog((GEN)x[i],prec);
    for (   ; i<=RU; i++) v[i] = lmul2n(mylog((GEN)x[i],prec),1);
  }
  return v;
}

GEN
get_arch_real(GEN nf,GEN x,GEN *emb,long prec)
{
  long i,R1,RU;
  GEN v,p1,p2;

  R1=itos(gmael(nf,2,1)); RU = R1+itos(gmael(nf,2,2));
  if (typ(x)!=t_COL) x = algtobasis_intern(nf,x);
  if (isnfscalar(x)) /* rational number */
  {
    GEN u = (GEN)x[1];
    v = cgetg(RU+1,t_COL);
    i = signe(u);
    if (!i) err(talker,"0 in get_arch_real");
    p1= (i > 0)? glog(u,prec): gzero;
    p2 = (RU > R1)? gmul2n(p1,1): NULL;
    for (i=1; i<=R1; i++) v[i]=(long)p1;
    for (   ; i<=RU; i++) v[i]=(long)p2;
  }
  else
  {
    x = gmul(gmael(nf,5,1),x); v = cgetg(RU+1,t_COL);
    for (i=1; i<=R1; i++) v[i] = llog(gabs((GEN)x[i],prec),prec);
    for (   ; i<=RU; i++) v[i] = llog(gnorm((GEN)x[i]),prec);
  }
  *emb = x; return v;
}

GEN
principalidele(GEN nf, GEN x, long prec)
{
  GEN p1,y = cgetg(3,t_VEC);
  long av;

  nf = checknf(nf);
  p1 = principalideal0(nf,x,1);
  y[1] = (long)p1;
  av =avma; p1 = get_arch(nf,(GEN)p1[1],prec);
  y[2] = lpileupto(av,p1); return y;
}

/* GP functions */

GEN
ideal_two_elt0(GEN nf, GEN x, GEN a)
{
  if (!a) return ideal_two_elt(nf,x);
  return ideal_two_elt2(nf,x,a);
}

GEN
idealpow0(GEN nf, GEN x, GEN n, long flag, long prec)
{
  if (flag) return idealpowred(nf,x,n,prec);
  return idealpow(nf,x,n);
}

GEN
idealmul0(GEN nf, GEN x, GEN y, long flag, long prec)
{
  if (flag) return idealmulred(nf,x,y,prec);
  return idealmul(nf,x,y);
}

GEN
idealinv0(GEN nf, GEN ix, long flag)
{
  switch(flag)
  {
    case 0: return idealinv(nf,ix);
    case 1: return oldidealinv(nf,ix);
    default: err(flagerr,"idealinv");
  }
  return NULL; /* not reached */
}

GEN
idealdiv0(GEN nf, GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 0: return idealdiv(nf,x,y);
    case 1: return idealdivexact(nf,x,y);
    default: err(flagerr,"idealdiv");
  }
  return NULL; /* not reached */
}

GEN
idealaddtoone0(GEN nf, GEN arg1, GEN arg2)
{
  if (!arg2) return idealaddmultoone(nf,arg1);
  return idealaddtoone(nf,arg1,arg2);
}

static GEN
two_to_hnf(GEN nf, GEN a, GEN b)
{
  a = principalideal_aux(nf,a);
  b = principalideal_aux(nf,b);
  a = concatsp(a,b);
  if (lgef(nf[1])==5) /* quadratic field: a has to be turned into idealmat */
    a = idealmul(nf,idmat(2),a);
  return idealmat_to_hnf(nf, a);
}

GEN
idealhnf0(GEN nf, GEN a, GEN b)
{
  long av;
  if (!b) return idealhermite(nf,a);

  /* HNF of aZ_K+bZ_K */
  av = avma; nf=checknf(nf);
  return gerepileupto(av, two_to_hnf(nf,a,b));
}

GEN
idealhermite2(GEN nf, GEN a, GEN b)
{
  return idealhnf0(nf,a,b);
}

/* x = (xZ, a) ? Use sufficient condition gcd(Na/Nx, xZ) = 1 */
static GEN
check_elt(GEN a, GEN pol, GEN Nx, GEN xZ)
{
  GEN yZ,y,norm, ck,c;
  
  if (!signe(a)) return NULL;
  c = content(a);
  if (gcmp1(c)) {y=a; ck=NULL;} else {y=gdiv(a,c); ck=gpowgs(c, lgef(pol)-3);}

  norm = resultantducos(pol,y); if (ck) norm = gmul(norm,ck);
  if (gcmp1(mppgcd(divii(norm,Nx), xZ))) return a;

  /* try a + xZ = c (y + yZ) */
  yZ = xZ;
  if (ck)
  { 
    yZ = gdiv(xZ,c);
    if (typ(yZ) == t_FRAC) /* should be exceedingly rare */
    {
      y = gmul(y,(GEN)yZ[2]);
      ck = gdiv(ck, gpowgs((GEN)yZ[2], lgef(pol)-3));
      yZ = (GEN)yZ[1];
    }
  }
  y = gadd(y,yZ);

  norm = resultantducos(pol,y); if (ck) norm = gmul(norm,ck);
  if (gcmp1(mppgcd(divii(norm,Nx), xZ))) return a;
  return NULL;
}

static void
setprec(GEN x, long prec)
{
  long i,j, n=lg(x);
  for (i=1;i<n;i++)
  {
    GEN p2,p1 = (GEN)x[i];
    for (j=1;j<n;j++) 
    {
      p2 = (GEN)p1[j];
      if (typ(p2) == t_REAL) setlg(p2, prec);
    }
  }
}

/* find a basis of x whose elements have small norm
 * M a bound for the size of coeffs of x */
GEN
ideal_better_basis(GEN nf, GEN x, GEN M)
{
  GEN a,b;
  long nfprec = (long)nfnewprec(nf,0);
  long prec = DEFAULTPREC + (expi(M) >> TWOPOTBITS_IN_LONG);
 
  if (typ(nf[5]) != t_VEC) return x;
  if ((prec<<1) < nfprec) prec = (prec+nfprec) >> 1;
  a = qf_base_change(gmael(nf,5,3),x,1);
  setprec(a,prec);
  b = lllgramintern(a,4,1,prec);
  if (!b) 
  {
    if (DEBUGLEVEL)
      err(warner, "precision too low in ideal_better_basis (1)");
    if (nfprec > prec)
    {
      setprec(a,nfprec);
      b = lllgramintern(a,4,1,nfprec);
    }
  }
  if (!b)
  {
    if (DEBUGLEVEL)
      err(warner, "precision too low in ideal_better_basis (2)");
    b = lllint(x); /* better than nothing */
  }
  return gmul(x, b);
}

static GEN
mat_ideal_two_elt(GEN nf, GEN x)
{
  GEN y,a,beta,Nx,cx,xZ, pol = (GEN)nf[1];
  long av,tetpil,i,z, N = lgef(pol)-3;

  y=cgetg(3,t_VEC); av=avma;
  if (lg(x[1])!=N+1) err(typeer,"ideal_two_elt");
  if (N == 2) 
  {
    y[1] = lcopy(gcoeff(x,1,1));
    y[2] = lcopy((GEN)x[2]); return y;
  }

  cx=content(x); if (!gcmp1(cx)) x = gdiv(x,cx);
  if (lg(x) != N+1) x = idealhermite_aux(nf,x);
  xZ = gcoeff(x,1,1); 
  if (gcmp1(xZ))
  { 
    y[1] = lpileupto(av,gcopy(cx));
    y[2] = (long)gscalcol(cx,N); return y;
  }
  Nx = dethnf_i(x);
  beta = gmul((GEN)nf[7], x);
  a = NULL; /* gcc -Wall */
  for (i=2; i<=N; i++)
  {
    a = check_elt((GEN)beta[i], pol, Nx, xZ);
    if (a) break;
  }
  if (i>N)
  {
    x = ideal_better_basis(nf,x,xZ);
    beta = gmul((GEN)nf[7], x);
    for (i=1; i<=N; i++)
    {
      a = check_elt((GEN)beta[i], pol, Nx, xZ);
      if (a) break;
    }
  }
  if (i>N)
  {
    long c=0, av1=avma;

    if (DEBUGLEVEL>3) fprintferr("ideal_two_elt, hard case: ");
    for(;;)
    {
      if (DEBUGLEVEL>3) fprintferr("%d ", ++c);
      a = gzero;
      for (i=1; i<=N; i++)
      {
        z = mymyrand() >> (BITS_IN_RANDOM-5); /* in [0,15] */
        z -= 7; /* in [-7, 8] */
        a = gadd(a, gmulsg(z,(GEN)beta[i]));
      }
      a = check_elt(a, pol, Nx, xZ);
      if (a) break;
      avma=av1;
    }
    if (DEBUGLEVEL>3) fprintferr("\n");
  }
  a = centermod(algtobasis_intern(nf,a), xZ);
  tetpil=avma; y[1]=lmul(xZ,cx); y[2]=lmul(a,cx);
  gerepilemanyvec(av,tetpil,y+1,2); return y;
}

/* Etant donne un ideal ix, ressort un vecteur [a,alpha] a deux composantes
 * tel que a soit rationnel et ix=aZ_K+alpha Z_K, alpha etant un vecteur
 * colonne sur la base d'entiers. On peut avoir a=0 ou alpha=0, mais on ne
 * cherche pas a determiner si ix est principal.
 */
GEN
ideal_two_elt(GEN nf, GEN x)
{
  GEN z;
  long N, tx = idealtyp(&x,&z);

  nf=checknf(nf);
  if (tx==id_MAT) return mat_ideal_two_elt(nf,x);

  N=lgef(nf[1])-3; z=cgetg(3,t_VEC);
  if (tx == id_PRINCIPAL)
  {
    switch(typ(x))
    {
      case t_INT: case t_FRAC: case t_FRACN:
        z[1]=lcopy(x);
	z[2]=(long)zerocol(N); return z;

      case t_POLMOD:
        if (!gegal((GEN)nf[1],(GEN)x[1]))
	  err(talker,"incompatible number fields in ideal_two_elt");
	x=(GEN)x[2]; /* fall through */
      case t_POL:
        z[1]=zero; z[2]=(long)algtobasis(nf,x); return z;
      case t_COL:
        if (lg(x)==N+1) { z[1]=zero; z[2]=lcopy(x); return z; }
    }
  }
  else if (tx == id_PRIME)
  {
    z[1]=lcopy((GEN)x[1]);
    z[2]=lcopy((GEN)x[2]); return z;
  }
  err(typeer,"ideal_two_elt");
  return NULL; /* not reached */
}

/* factorization */

/* x integral ideal in HNF, return v_p(Nx), *vz = v_p(x \cap Z)
 * Use x[i,i] | x[1,1], i > 0 */
long
val_norm(GEN x, GEN p, long *vz)
{
  long i,l = lg(x), v;
  *vz = v = pvaluation(gcoeff(x,1,1), p, NULL);
  if (!v) return 0;
  for (i=2; i<l; i++)
    v += pvaluation(gcoeff(x,i,i), p, NULL);
  return v;
}

/* return factorization of Nx */
GEN
factor_norm(GEN x)
{
  GEN f = factor(gcoeff(x,1,1)), p = (GEN)f[1], e = (GEN)f[2];
  long i,k, l = lg(p);
  for (i=1; i<l; i++)
    e[i] = (long)val_norm(x,(GEN)p[i], &k);
  settyp(e, t_VECSMALL); return f;
}

GEN
idealfactor(GEN nf, GEN x)
{
  long av,tx, tetpil,i,j,k,lf,lc,N,l,v,vc,e;
  GEN f,f1,f2,c1,c2,y1,y2,y,p1,p2,cx,P;

  tx = idealtyp(&x,&y);
  if (tx == id_PRIME)
  {
    y=cgetg(3,t_MAT);
    y[1]=lgetg(2,t_COL); mael(y,1,1)=lcopy(x);
    y[2]=lgetg(2,t_COL); mael(y,2,1)=un; return y;
  }
  nf=checknf(nf); av=avma;
  if (tx == id_PRINCIPAL) x = principalideal_aux(nf,x);

  N=lgef(nf[1])-3; if (lg(x) != N+1) x = idealmat_to_hnf(nf,x);
  if (lg(x)==1) err(talker,"zero ideal in idealfactor");
  cx = content(x);
  if (gcmp1(cx))
  {
    c1 = c2 = NULL; /* gcc -Wall */
    lc=1;
  }
  else
  {
    f = factor(cx); x = gdiv(x,cx);
    c1 = (GEN)f[1];
    c2 = (GEN)f[2]; lc = lg(c1);
  }
  f = factor_norm(x);
  f1 = (GEN)f[1];
  f2 = (GEN)f[2]; lf = lg(f1);
  y1 = cgetg((lf+lc-2)*N+1,t_COL);
  y2 = cgetg((lf+lc-2)*N+1,t_VECSMALL);
  k = 1;
  for (i=1; i<lf; i++)
  {
    p1 = primedec(nf,(GEN)f1[i]);
    l = f2[i]; /* = v_p(Nx) */
    vc = ggval(cx,(GEN)f1[i]);
    for (j=1; j<lg(p1); j++)
    {
      P = (GEN)p1[j]; e = itos((GEN)P[3]);
      v = idealval(nf,x,P);
      l -= v*itos((GEN)P[4]);
      v += vc*e; if (!v) continue;
      y1[k] = (long)P;
      y2[k] = v; k++;
      if (l == 0) break; /* now only the content contributes */
    }
    if (vc == 0) continue;
    for (j++; j<lg(p1); j++)
    {
      P = (GEN)p1[j]; e = itos((GEN)P[3]);
      y1[k] = (long)P;
      y2[k] = vc*e; k++;
    }
  }
  for (i=1; i<lc; i++)
  {
    /* p | Nx already treated */
    if (divise(gcoeff(x,1,1),(GEN)c1[i])) continue;
    p1 = primedec(nf,(GEN)c1[i]);
    vc = itos((GEN)c2[i]);
    for (j=1; j<lg(p1); j++)
    {
      P = (GEN)p1[j]; e = itos((GEN)P[3]);
      y1[k] = (long)P;
      y2[k] = vc*e; k++;
    }
  }
  tetpil=avma; y=cgetg(3,t_MAT);
  p1=cgetg(k,t_COL); y[1]=(long)p1;
  p2=cgetg(k,t_COL); y[2]=(long)p2;
  for (i=1; i<k; i++) { p1[i]=lcopy((GEN)y1[i]); p2[i]=lstoi(y2[i]); }
  y = gerepile(av,tetpil,y);
  return sort_factor_gen(y, cmp_prime_ideal);
}

/* P prime ideal in primedec format. Return valuation(ix) at P */
long
idealval(GEN nf, GEN ix, GEN P)
{
  long N,v,vd,w,av=avma,av1,lim,e,f,i,j,k, tx = typ(ix);
  GEN mul,mat,a,x,y,r,bp,p,pk,cx;

  nf=checknf(nf); checkprimeid(P);
  if (is_extscalar_t(tx) || tx==t_COL) return element_val(nf,ix,P);
  p=(GEN)P[1]; N=lgef(nf[1])-3;
  tx = idealtyp(&ix,&a);
  cx = content(ix); if (!gcmp1(cx)) ix = gdiv(ix,cx);
  if (tx != id_MAT)
    ix = idealhermite_aux(nf,ix);
  else
  {
    checkid(ix,N);
    if (lg(ix) != N+1) ix=idealmat_to_hnf(nf,ix);
  }
  e = itos((GEN)P[3]);
  f = itos((GEN)P[4]);
  /* 0 <= v_P(ix) <= floor[v_p(Nix) / f] */
  i = val_norm(ix,p, &k) / f;
  /* 0 <= ceil[v_P(ix) / e] <= v_p(ix \cap Z) --> v_P <= e * v_p */
  j = k * e;
  v = min(i,j); /* v_P(ix) <= v */
  vd = ggval(cx,p) * e;
  if (!v) { avma = av; return vd; }

  mul = cgetg(N+1,t_MAT); bp=(GEN)P[5]; 
  mat = cgetg(N+1,t_MAT);
  for (j=1; j<=N; j++) 
  {
    mul[j] = (long)element_mulid(nf,bp,j);
    x = (GEN)ix[j];
    y = cgetg(N+1, t_COL); mat[j] = (long)y;
    for (i=1; i<=N; i++)
    { /* compute (x.b)_i, ix in HNF ==> x[j+1..N] = 0 */
      a = mulii((GEN)x[1], gcoeff(mul,i,1));
      for (k=2; k<=j; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
      /* is it divisible by p ? */
      y[i] = ldvmdii(a,p,&r);
      if (signe(r)) { avma = av; return vd; }
    }
  }
  pk = gpowgs(p, v-1);
  av1 = avma; lim=stack_lim(av1,3);
  y = cgetg(N+1,t_COL);
  /* can compute mod p^(v-w) */
  for (w=1; w<v; w++)
  {
    for (j=1; j<=N; j++)
    {
      x = (GEN)mat[j];
      for (i=1; i<=N; i++)
      { /* compute (x.b)_i */
        a = mulii((GEN)x[1], gcoeff(mul,i,1));
        for (k=2; k<=N; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
        /* is it divisible by p ? */
        y[i] = ldvmdii(a,p,&r);
        if (signe(r)) { avma = av; return w + vd; }
        if (lgefint(y[i]) > lgefint(pk)) y[i] = lresii((GEN)y[i], pk);
      }
      r=x; mat[j]=(long)y; y=r;
      if (low_stack(lim,stack_lim(av1,3)))
      {
        GEN *gptr[3]; gptr[0]=&y; gptr[1]=&mat; gptr[2]=&pk;
	if(DEBUGMEM>1) err(warnmem,"idealval");
        gerepilemany(av1,gptr,3);
      }
    }
    pk = gdivexact(pk,p);
  }
  avma = av; return w + vd;
}

/* gcd and generalized Bezout */

GEN
idealadd(GEN nf, GEN x, GEN y)
{
  long av=avma,N,tx,ty;
  GEN z,p1,dx,dy,dz;
  int modid;

  tx = idealtyp(&x,&z);
  ty = idealtyp(&y,&z);
  nf=checknf(nf); N=lgef(nf[1])-3;
  z = cgetg(N+1, t_MAT);
  if (tx != id_MAT || lg(x)!=N+1) x = idealhermite_aux(nf,x);
  if (ty != id_MAT || lg(y)!=N+1) y = idealhermite_aux(nf,y);
  if (lg(x) == 1) return gerepileupto(av,y);
  if (lg(y) == 1) return gerepileupto(av,x); /* check for 0 ideal */
  dx=denom(x);
  dy=denom(y); dz=mulii(dx,dy);
  if (gcmp1(dz)) dz = NULL; else { x=gmul(x,dz); y=gmul(y,dz); }
  if (isnfscalar((GEN)x[1]) && isnfscalar((GEN)y[1]))
  {
    p1 = mppgcd(gcoeff(x,1,1),gcoeff(y,1,1));
    modid = 1;
  }
  else
  {
    p1 = mppgcd(detint(x),detint(y));
    modid = 0;
  }
  if (gcmp1(p1))
  {
    long i,j;
    if (!dz) { avma=av; return idmat(N); }
    avma = (long)dz; dz = gerepileupto((long)z, ginv(dz));
    for (i=1; i<=N; i++)
    {
      z[i]=lgetg(N+1,t_COL);
      for (j=1; j<=N; j++)
        coeff(z,j,i) = (i==j)? (long)dz: zero;
    }
    return z;
  }
  z = concatsp(x,y);
  z = modid? hnfmodid(z,p1): hnfmod(z, p1);
  if (dz) z=gdiv(z,dz);
  return gerepileupto(av,z);
}

static GEN
get_p1(GEN nf, GEN x, GEN y,long fl)
{
  GEN u,v,v1,v2,v3,v4;
  long i,j,N;

  switch(fl)
  {
    case 1:
      v1 = gcoeff(x,1,1);
      v2 = gcoeff(y,1,1);
      if (typ(v1)!=t_INT || typ(v2)!=t_INT)
        err(talker,"ideals don't sum to Z_K in idealaddtoone");
      if (gcmp1(bezout(v1,v2,&u,&v)))
        return gmul(u,(GEN)x[1]);
    default:
      v=hnfperm(concatsp(x,y));
      v1=(GEN)v[1]; v2=(GEN)v[2]; v3=(GEN)v[3];
      j=0; N = lgef(nf[1])-3;
      for (i=1; i<=N; i++)
      {
        if (!gcmp1(gcoeff(v1,i,i)))
          err(talker,"ideals don't sum to Z_K in idealaddtoone");
        if (gcmp1((GEN)v3[i])) j=i;
      }
      v4=(GEN)v2[N+j]; setlg(v4,N+1);
      return gmul(x,v4);
  }
}

GEN
idealaddtoone_i(GEN nf, GEN x, GEN y)
{
  long t, fl = 1;
  GEN p1,xh,yh;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entering idealaddtoone:\n");
    fprintferr(" x = %Z\n",x);
    fprintferr(" y = %Z\n",y);
  }
  t = idealtyp(&x,&p1);
  if (t != id_MAT || lg(x) > 1 || lg(x) != lg(x[1]))
    xh = idealhermite_aux(nf,x);
  else
    { xh=x; fl = isnfscalar((GEN)x[1]); }
  t = idealtyp(&y,&p1);
  if (t != id_MAT || lg(y) == 1 || lg(y) != lg(y[1]))
    yh = idealhermite_aux(nf,y);
  else
    { yh=y; if (fl) fl = isnfscalar((GEN)y[1]); }
  if (lg(xh) == 1)
  {
    if (lg(yh) == 1 || !gcmp1(gabs(gcoeff(yh,1,1),0)))
      err(talker,"ideals don't sum to Z_K in idealaddtoone");
    return algtobasis(nf, gzero);
  }
  if (lg(yh) == 1)
  {
    p1 = gcoeff(xh,1,1);
    if (!gcmp1(gabs(p1,0)))
      err(talker,"ideals don't sum to Z_K in idealaddtoone");
    return algtobasis(nf, gneg(p1));
  }

  p1 = get_p1(nf,xh,yh,fl);
  p1 = element_reduce(nf,p1, idealmullll(nf,x,y));
  if (DEBUGLEVEL>4 && !gcmp0(p1))
    fprintferr(" leaving idealaddtoone: %Z\n",p1);
  return p1;
}

/* ideal should be an idele (not mandatory). For internal use. */
GEN
ideleaddone_aux(GEN nf,GEN x,GEN ideal)
{
  long i,nba,R1;
  GEN p1,p2,p3,arch;

  (void)idealtyp(&ideal,&arch);
  if (!arch) return idealaddtoone_i(nf,x,ideal);

  R1=itos(gmael(nf,2,1));
  if (typ(arch)!=t_VEC && lg(arch)!=R1+1)
    err(talker,"incorrect idele in idealaddtoone");
  for (nba=0,i=1; i<lg(arch); i++)
    if (signe(arch[i])) nba++;
  if (!nba) return idealaddtoone_i(nf,x,ideal);

  p3 = idealaddtoone_i(nf,x,ideal);
  if (gcmp0(p3)) p3=(GEN)idealhermite_aux(nf,x)[1];
  p1=idealmullll(nf,x,ideal);

  p2=zarchstar(nf,p1,arch,nba);
  p1=lift_intern(gmul((GEN)p2[3],zsigne(nf,p3,arch)));
  p2=(GEN)p2[2]; nba=0;
  for (i=1; i<lg(p1); i++)
    if (signe(p1[i])) { nba=1; p3=element_mul(nf,p3,(GEN)p2[i]); }
  if (gcmp0(p3)) return gcopy((GEN)x[1]); /* can happen if ideal = Z_K */
  return nba? p3: gcopy(p3);
}

static GEN
unnf_minus_x(GEN x)
{
  long i, N = lg(x);
  GEN y = cgetg(N,t_COL);

  y[1] = lsub(gun,(GEN)x[1]);
  for (i=2;i<N; i++) y[i] = lneg((GEN)x[i]);
  return y;
}

static GEN
addone(GEN f(GEN,GEN,GEN), GEN nf, GEN x, GEN y)
{
  GEN z = cgetg(3,t_VEC);
  long av=avma;

  nf=checknf(nf); x = gerepileupto(av, f(nf,x,y));
  z[1]=(long)x; z[2]=(long)unnf_minus_x(x); return z;
}

GEN
idealaddtoone(GEN nf, GEN x, GEN y)
{
  return addone(idealaddtoone_i,nf,x,y);
}

GEN
ideleaddone(GEN nf,GEN x,GEN idele)
{
  return addone(ideleaddone_aux,nf,x,idele);
}

GEN
nfmodprinit(GEN nf, GEN pr)
{
  long av;
  GEN p,e,p1,prhall;

  nf = checknf(nf); checkprimeid(pr);
  prhall = cgetg(3,t_VEC);
  prhall[1] = (long) prime_to_ideal(nf,pr);

  av = avma; p = (GEN)pr[1]; e = (GEN)pr[3];
  p1 = cgetg(2,t_MAT);
  p1[1] = ldiv(element_pow(nf,(GEN)pr[5],e), gpuigs(p,itos(e)-1));
  p1 = hnfmodid(idealhermite_aux(nf,p1), p);
  p1 = idealaddtoone_i(nf,pr,p1);

  /* p1 = 1 mod pr, p1 = 0 mod q^{e_q} for all other primes q | p */
  prhall[2] = lpileupto(av, unnf_minus_x(p1)); return prhall;
}

/* given an element x in Z_K and an integral ideal y with x, y coprime,
   outputs an element inverse of x modulo y */
GEN
element_invmodideal(GEN nf, GEN x, GEN y)
{
  long av=avma,N,i, fl = 1;
  GEN v,p1,xh,yh;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (ideal_is_zk(y,N)) return zerocol(N);
  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans element_invmodideal() :\n");
    fprintferr(" x = "); outerr(x);
    fprintferr(" y = "); outerr(y);
  }
  i = lg(y);
  if (typ(y)!=t_MAT || i==1 || i != lg(y[1])) yh=idealhermite_aux(nf,y);
  else
    { yh=y; fl = isnfscalar((GEN)y[1]); }
  switch (typ(x))
  {
    case t_POL: case t_POLMOD: case t_COL:
      xh = idealhermite_aux(nf,x); break;
    default: err(typeer,"element_invmodideal");
      return NULL; /* not reached */
  }
  p1 = get_p1(nf,xh,yh,fl);
  p1 = element_div(nf,p1,x);
  v = gerepileupto(av, nfreducemodideal(nf,p1,y));
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de element_invmodideal : v = "); outerr(v); }
  return v;
}

GEN
idealaddmultoone(GEN nf, GEN list)
{
  long av=avma,tetpil,N,i,i1,j,k;
  GEN z,v,v1,v2,v3,p1;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans idealaddmultoone() :\n");
    fprintferr(" list = "); outerr(list);
  }
  if (typ(list)!=t_VEC && typ(list)!=t_COL)
    err(talker,"not a list in idealaddmultoone");
  k=lg(list); z=cgetg(1,t_MAT); list = dummycopy(list);
  if (k==1) err(talker,"ideals don't sum to Z_K in idealaddmultoone");
  for (i=1; i<k; i++)
  {
    p1=(GEN)list[i];
    if (typ(p1)!=t_MAT || lg(p1)!=lg(p1[1]))
      list[i] = (long)idealhermite_aux(nf,p1);
    z = concatsp(z,(GEN)list[i]);
  }
  v=hnfperm(z); v1=(GEN)v[1]; v2=(GEN)v[2]; v3=(GEN)v[3]; j=0;
  for (i=1; i<=N; i++)
  {
    if (!gcmp1(gcoeff(v1,i,i)))
      err(talker,"ideals don't sum to Z_K in idealaddmultoone");
    if (gcmp1((GEN)v3[i])) j=i;
  }

  v=(GEN)v2[(k-2)*N+j]; z=cgetg(k,t_VEC);
  for (i=1; i<k; i++)
  {
    p1=cgetg(N+1,t_COL); z[i]=(long)p1;
    for (i1=1; i1<=N; i1++) p1[i1]=v[(i-1)*N+i1];
  }
  tetpil=avma; v=cgetg(k,typ(list));
  for (i=1; i<k; i++) v[i]=lmul((GEN)list[i],(GEN)z[i]);
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de idealaddmultoone v = "); outerr(v); }
  return gerepile(av,tetpil,v);
}

/* multiplication */

/* x integral ideal (without archimedean component) in HNF form
 * [a,alpha,n] corresponds to the ideal aZ_K+alpha Z_K (a is a
 * rational integer). Multiply them
 */
static GEN
idealmulspec(GEN nf, GEN x, GEN a, GEN alpha)
{
  long i, N=lg(x)-1;
  GEN m;

  if (isnfscalar(alpha))
    return gmul(mppgcd(a,(GEN)alpha[1]),x);
  m = cgetg((N<<1)+1,t_MAT);
  for (i=1; i<=N; i++) m[i]=(long)element_muli(nf,alpha,(GEN)x[i]);
  for (i=1; i<=N; i++) m[i+N]=lmul(a,(GEN)x[i]);
  return hnfmodid(m, mulii(a, gcoeff(x,1,1)));
}

/* x ideal (matrix form,maximal rank), vp prime ideal (primedec). Output the
 * product. Can be used for arbitrary vp of the form [p,a,e,f,b], IF vp
 * =pZ_K+aZ_K, p is an integer, and norm(vp) = p^f; e and b are not used. For
 * internal use.
 */
GEN
idealmulprime(GEN nf, GEN x, GEN vp)
{
  GEN denx = denom(x);

  if (gcmp1(denx)) denx = NULL; else x=gmul(denx,x);
  x = idealmulspec(nf,x, (GEN)vp[1], (GEN)vp[2]);
  return denx? gdiv(x,denx): x;
}

/* Assume ix and iy are integral in HNF form (or ideles of the same form).
 * HACK: ideal in iy can be of the form [a,b], a in Z, b in Z_K
 * For internal use. */
GEN
idealmulh(GEN nf, GEN ix, GEN iy)
{
  long f = 0;
  GEN res,x,y;

  if (typ(ix)==t_VEC) {f=1;  x=(GEN)ix[1];} else x=ix;
  if (typ(iy)==t_VEC && typ(iy[1]) != t_INT) {f+=2; y=(GEN)iy[1];} else y=iy;
  res = f? cgetg(3,t_VEC): NULL;

  if (typ(y) != t_VEC) y = ideal_two_elt(nf,y);
  y = idealmulspec(nf,x,(GEN)y[1],(GEN)y[2]);
  if (!f) return y;

  res[1]=(long)y;
  if (f==3) y = gadd((GEN)ix[2],(GEN)iy[2]);
  else
  {
    y = (f==2)? (GEN)iy[2]: (GEN)ix[2];
    y = gcopy(y);
  }
  res[2]=(long)y; return res;
}

/* x and y are ideals in matrix form */
static GEN
idealmat_mul(GEN nf, GEN x, GEN y)
{
  long i,j, rx=lg(x)-1, ry=lg(y)-1;
  GEN dx,dy,m;

  dx=denom(x); if (!gcmp1(dx)) x=gmul(dx,x);
  dy=denom(y); if (!gcmp1(dy)) y=gmul(dy,y);
  dx = mulii(dx,dy);
  if (rx<=2 || ry<=2)
  {
    m=cgetg(rx*ry+1,t_MAT);
    for (i=1; i<=rx; i++)
      for (j=1; j<=ry; j++)
        m[(i-1)*ry+j]=(long)element_muli(nf,(GEN)x[i],(GEN)y[j]);
    if (isnfscalar((GEN)x[1]) && isnfscalar((GEN)y[1]))
    {
      GEN p1 = mulii(gcoeff(x,1,1),gcoeff(y,1,1));
      y = hnfmodid(m, p1);
    }
    else 
      y=hnfmod(m, detint(m));
  }
  else
  {
    x=idealmat_to_hnf(nf,x);
    y=idealmat_to_hnf(nf,y); y=idealmulh(nf,x,y);
  }
  return gcmp1(dx)? y: gdiv(y,dx);
}

/* y is principal */
static GEN
add_arch(GEN nf, GEN ax, GEN y)
{
  long tetpil, av=avma, prec=precision(ax);

  y = get_arch(nf,y,prec); tetpil=avma;
  return gerepile(av,tetpil,gadd(ax,y));
}

/* output the ideal product ix.iy (don't reduce) */
GEN
idealmul(GEN nf, GEN x, GEN y)
{
  long tx,ty,av,f;
  GEN res,ax,ay,p1;

  tx = idealtyp(&x,&ax);
  ty = idealtyp(&y,&ay);
  if (tx>ty) {
    res=ax; ax=ay; ay=res;
    res=x; x=y; y=res;
    f=tx; tx=ty; ty=f;
  }
  f = (ax||ay); res = f? cgetg(3,t_VEC): NULL; /* product is an idele */
  nf=checknf(nf); av=avma;
  switch(tx)
  {
    case id_PRINCIPAL:
      switch(ty)
      {
        case id_PRINCIPAL:
          p1 = idealhermite_aux(nf, element_mul(nf,x,y));
          break;
        case id_PRIME:
          p1 = gmul((GEN)y[1],x);
          p1 = two_to_hnf(nf,p1, element_mul(nf,(GEN)y[2],x));
          break;
        default: /* id_MAT */
          p1 = idealmat_mul(nf,y, principalideal_aux(nf,x));
      }break;

    case id_PRIME:
      p1 = (ty==id_PRIME)? prime_to_ideal_aux(nf,y)
                         : idealmat_to_hnf(nf,y);
      p1 = idealmulprime(nf,p1,x); break;

    default: /* id_MAT */
      p1 = idealmat_mul(nf,x,y);
  }
  p1 = gerepileupto(av,p1);
  if (!f) return p1;

  if (ax && ay)
  {
    if (typ(ax) == t_POLMOD) ax = gmul(ax,ay);
    else
      ax = (ax == ay)? gmul2n(ax,1): gadd(ax,ay);
  }
  else
  {
    if (ax)
      ax = (ty==id_PRINCIPAL)? add_arch(nf,ax,y): gcopy(ax);
    else
      ax = (tx==id_PRINCIPAL)? add_arch(nf,ay,x): gcopy(ay);
  }
  res[1]=(long)p1; res[2]=(long)ax; return res;
}

/* norm of an ideal */
GEN
idealnorm(GEN nf, GEN x)
{
  long av = avma,tetpil;
  GEN y;

  nf = checknf(nf);
  switch(idealtyp(&x,&y))
  {
    case id_PRIME:
      return powgi((GEN)x[1],(GEN)x[4]);
    case id_PRINCIPAL:
      x = gnorm(basistoalg(nf,x)); break;
    default:
      if (lg(x) != lgef(nf[1])-2) x = idealhermite_aux(nf,x);
      x = dethnf(x);
  }
  tetpil=avma; return gerepile(av,tetpil,gabs(x,0));
}

/* inverse */
extern GEN gauss_triangle_i(GEN A, GEN B);

/* rewritten from original code by P.M & M.H.
 *
 * I^(-1) = { x \in K, Tr(x D^(-1) I) \in Z }, D different of K/Q
 *
 * nf[5][6] = d_K * D^(-1) is integral = d_K T^(-1), T = (Tr(wi wj))
 * nf[5][7] = same in suitable form for ideal multiplication */
static GEN
hnfideal_inv(GEN nf, GEN I)
{
  GEN dI = denom(I), NI,a,dual;

  if (gcmp1(dI)) dI = NULL; else I = gmul(I,dI);
  NI = dethnf_i(I);
  if (gcmp0(NI) || lg(I)==1) err(talker, "cannot invert zero ideal");
  I = idealmulh(nf,I, gmael(nf,5,7));
 /* I in HNF, hence easily inverted. Multiply by NI to get integer coeffs
  * d_K cancels while solving the linear equations. */
  dual = gtrans( gauss_triangle_i(I, gmul(NI, gmael(nf,5,6))) );
  a = content(dual);
  if (!is_pm1(a)) { dual = gdivexact(dual,a); NI = divii(NI,a); }

  dual = hnfmodid(dual, NI);
  if (dI) NI = gdiv(NI,dI);
  return gdiv(dual,NI);
}

GEN
oldidealinv(GEN nf, GEN x)
{
  GEN res,dual,di,ax;
  long av,tetpil, tx = idealtyp(&x,&ax);

  if (tx!=id_MAT) return idealinv(nf,x);
  res = ax? cgetg(3,t_VEC): NULL;
  nf=checknf(nf); av=avma;
  if (lg(x)!=lgef(nf[1])) x = idealmat_to_hnf(nf,x);

  dual = ginv(gmul(gtrans(x), gmael(nf,5,4)));
  di=denom(dual); dual=gmul(di,dual);
  dual = idealmat_mul(nf,gmael(nf,5,5), dual);
  tetpil=avma; dual = gerepile(av,tetpil,gdiv(dual,di));
  if (!ax) return dual;
  res[1]=(long)dual; res[2]=lneg(ax); return res;
}

/* return p * P^(-1)  [integral] */
GEN
pidealprimeinv(GEN nf, GEN x)
{
  GEN y=cgetg(6,t_VEC); y[1]=x[1]; y[2]=x[5];
  y[3]=y[5]=zero; y[4]=lsubsi(lgef(nf[1])-3, (GEN)x[4]);
  return prime_to_ideal_aux(nf,y);
}

/* Calcule le dual de mat_id pour la forme trace */
GEN
idealinv(GEN nf, GEN x)
{
  GEN res,ax;
  long av=avma, tx = idealtyp(&x,&ax);

  res = ax? cgetg(3,t_VEC): NULL;
  nf=checknf(nf); av=avma;
  switch (tx)
  {
    case id_MAT:
      if (lg(x) != lg(x[1])) x = idealmat_to_hnf(nf,x);
      x = hnfideal_inv(nf,x); break;
    case id_PRINCIPAL: tx = typ(x);
      if (is_const_t(tx)) x = ginv(x);
      else
      {
        switch(tx)
        {
          case t_COL: x = gmul((GEN)nf[7],x); break;
          case t_POLMOD: x = (GEN)x[2]; break;
        }
        x = ginvmod(x,(GEN)nf[1]);
      }
      x = idealhermite_aux(nf,x); break;
    case id_PRIME:
      x = gdiv(pidealprimeinv(nf,x), (GEN)x[1]);
  }
  x = gerepileupto(av,x); if (!ax) return x;
  res[1]=(long)x; res[2]=lneg(ax); return res;
}

static GEN
idealpowprime(GEN nf, GEN vp, GEN n)
{
  GEN n1, x;
  long s = signe(n);

  nf = checknf(nf);
  if (s == 0) return idmat(lgef(nf[1])-3);
  if (s < 0) n = negi(n);
  x = dummycopy(vp);
  n1 = gceil(gdiv(n,(GEN)x[3]));
  x[1]=(long)powgi((GEN)x[1],n1);
  if (s < 0)
    x[2]=ldiv(element_pow(nf,(GEN)x[5],n), powgi((GEN)vp[1],subii(n,n1)));
  else
    x[2]=(long)element_pow(nf,(GEN)x[2],n);
  x = prime_to_ideal_aux(nf,x);
  if (s<0) x = gdiv(x, powgi((GEN)vp[1],n1));
  return x;
}

/* raise the ideal x to the power n (in Z) */
GEN
idealpow(GEN nf, GEN x, GEN n)
{
  long tx,N,av,s,i;
  GEN res,ax,m,cx,n1,a,alpha;

  if (typ(n) != t_INT) err(talker,"non-integral exponent in idealpow");
  tx = idealtyp(&x,&ax);
  res = ax? cgetg(3,t_VEC): NULL;
  nf = checknf(nf);
  av=avma; N=lgef(nf[1])-3; s=signe(n);
  if (!s) x = idmat(N);
  else
    switch(tx)
    {
      case id_PRINCIPAL: tx = typ(x);
        if (!is_const_t(tx))
          switch(tx)
          {
            case t_COL: x = gmul((GEN)nf[7],x);
            case t_POL: x = gmodulcp(x,(GEN)nf[1]);
          }
        x = gpui(x,n,0);
        x = idealhermite_aux(nf,x); break;
      case id_PRIME:
        x = idealpowprime(nf,x,n); break;
      default:
        n1 = (s<0)? negi(n): n;

        cx = content(x); if (gcmp1(cx)) cx = NULL; else x = gdiv(x,cx);
        a=ideal_two_elt(nf,x); alpha=(GEN)a[2]; a=(GEN)a[1];
        m = cgetg(N+1,t_MAT); a = gpui(a,n1,0);
        alpha = element_pow(nf,alpha,n1);
        for (i=1; i<=N; i++) m[i]=(long)element_mulid(nf,alpha,i);
        x = hnfmodid(m, a);
        if (s<0) x = hnfideal_inv(nf,x);
        if (cx) x = gmul(x, powgi(cx,n));
    }
  x = gerepileupto(av, x);
  if (!ax) return x;
  ax = (typ(ax) == t_POLMOD)? powgi(ax,n): gmul(n,ax);
  res[1]=(long)x;
  res[2]=(long)ax;
  return res;
}

/* Return ideal^e in number field nf. e is a C integer. */
GEN
idealpows(GEN nf, GEN ideal, long e)
{
  long court[] = {evaltyp(t_INT) | m_evallg(3),0,0};
  affsi(e,court); return idealpow(nf,ideal,court);
}

GEN
init_idele(GEN nf)
{
  GEN x = cgetg(3,t_VEC);
  long RU;
  nf = checknf(nf);
  RU = itos(gmael(nf,2,1)) + itos(gmael(nf,2,2));
  x[2] = (long)zerovec(RU); return x;
}

/* compute x^n (x ideal, n integer), reducing along the way if n is big */
GEN
idealpowred(GEN nf, GEN x, GEN n, long prec)
{
  long i,j,m,av=avma, s = signe(n);
  GEN y, p1;

  if (absi_cmp(n,stoi(16)) < 0)
  {
    y = idealpow(nf,x,n);
    return gerepileupto(av, ideallllred(nf,y,NULL,prec));
  }
  p1 = n+2; m = *p1;
  y = x; j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = idealmul(nf,y,y);
      if (m < 0) y = idealmul(nf,y,x);
      y = ideallllred(nf,y,NULL,prec);
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  if (s < 0) y = idealinv(nf,y);
  return gerepileupto(av,y);
}

GEN
idealmulred(GEN nf, GEN x, GEN y, long prec)
{
  long av=avma;
  x = idealmul(nf,x,y);
  return gerepileupto(av, ideallllred(nf,x,NULL,prec));
}

long
isideal(GEN nf,GEN x)
{
  long N,av,i,j,k,tx=typ(x),lx;
  GEN p1,minv;

  nf=checknf(nf); lx=lg(x);
  if (tx==t_VEC && lx==3) { x=(GEN)x[1]; tx=typ(x); lx=lg(x); }
  if (is_scalar_t(tx))
    return (tx==t_INT || tx==t_FRAC || tx==t_FRACN || tx==t_POL ||
                     (tx==t_POLMOD && gegal((GEN)nf[1],(GEN)x[1])));
  if (typ(x)==t_VEC) return (lx==6);
  if (typ(x)!=t_MAT) return 0;
  if (lx == 1) return 1;
  N=lgef(nf[1])-2; if (lg(x[1]) != N) return 0;

  av=avma;
  if (lx != N) x = idealmat_to_hnf(nf,x);
  x = gdiv(x,content(x)); minv=ginv(x);

  for (i=1; i<N; i++)
    for (j=1; j<N; j++)
    {
      p1=gmul(minv, element_mulid(nf,(GEN)x[i],j));
      for (k=1; k<N; k++)
	if (typ(p1[k])!=t_INT) { avma=av; return 0; }
    }
  avma=av; return 1;
}

GEN
idealdiv(GEN nf, GEN x, GEN y)
{
  long av=avma,tetpil;
  GEN z=idealinv(nf,y);

  tetpil=avma; return gerepile(av,tetpil,idealmul(nf,x,z));
}

GEN
idealdivexact(GEN nf, GEN x, GEN y)
/*  This routine computes the quotient x/y of two ideals in the number field
 *  nf. It assumes that the quotient is an integral ideal.
 *
 *  The idea is to find an ideal z dividing y
 *  such that gcd(N(x)/N(z), N(z)) = 1. Then
 *
 *    x + (N(x)/N(z))    x
 *    --------------- = -----
 *    y + (N(y)/N(z))    y
 *
 *  When x and y are integral ideals, this identity can be checked by looking
 *  at the exponent of a prime ideal p on both sides of the equation.
 *
 *  Specifically, if a prime ideal p divides N(z), then it divides neither
 *  N(x)/N(z) nor N(y)/N(z) (since N(x)/N(z) is the product of the integers
 *  N(x/y) and N(y/z)).  Both the numerator and the denominator on the left
 *  will be coprime to p.  So will x/y, since x/y is assumed integral and its
 *  norm N(x/y) is coprime to p
 *
 *  If instead p does not divide N(z), then the power of p dividing N(x)/N(z)
 *  is the same as the power of p dividing N(x), which is at least as large
 *  as the power of p dividing x.  Likewise for N(y)/N(z).  So the power of p
 *  dividing the left side equals the power of dividing the right side.
 *
 *		Peter Montgomery
 *		July, 1994.
 */
{
  long av = avma, tetpil,N;
  GEN x1,y1,detx1,dety1,detq,gcancel,gtemp, cy = content(y);

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (gcmp0(cy)) err(talker, "cannot invert zero ideal");

  x1 = gdiv(x,cy); detx1 = idealnorm(nf,x1);
  if (gcmp0(detx1)) { avma = av; return gcopy(x); } /* numerator is zero */

  y1 = gdiv(y,cy); dety1 = idealnorm(nf,y1);
  detq = gdiv(detx1,dety1);
  if (!gcmp1(denom(x1)) || typ(detq) != t_INT)
    err(talker, "quotient not integral in idealdivexact");
  gcancel = dety1;
 /* Find a norm gcancel such that
  * (1) gcancel divides dety1;
  * (2) gcd(detx1/gcancel, gcancel) = 1.
  */
  do
  {
    gtemp = ggcd(gcancel, gdiv(detx1,gcancel));
    gcancel = gdiv(gcancel,gtemp);
  }
  while (!gcmp1(gtemp));
 /*                    x1 + (detx1/gcancel)
  * Replace x1/y1 by:  --------------------
  *                    y1 + (dety1/gcancel)
  */

  x1 = idealadd(nf, x1, gscalmat(gdiv(detx1, gcancel), N));
  /* y1 reduced to unit ideal ? */
  if (gegal(gcancel,dety1)) return gerepileupto(av, x1);

  y1 = idealadd(nf,y1, gscalmat(gdiv(dety1,gcancel), N));
  y1 = hnfideal_inv(nf,y1); tetpil = avma;
  return gerepile(av, tetpil, idealmat_mul(nf,x1,y1));
}

GEN
idealintersect(GEN nf, GEN x, GEN y)
{
  long av=avma,lz,i,N;
  GEN z,dx,dy;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (idealtyp(&x,&z)!=t_MAT || lg(x)!=N+1) x=idealhermite_aux(nf,x);
  if (idealtyp(&y,&z)!=t_MAT || lg(y)!=N+1) y=idealhermite_aux(nf,y);
  if (lg(x) == 1 || lg(y) == 1) { avma = av; return cgetg(1, t_MAT); }
  dx=denom(x); if (!gcmp1(dx))   y = gmul(y,dx);
  dy=denom(y); if (!gcmp1(dy)) { x = gmul(x,dy); dx = mulii(dx,dy); }
  z = kerint(concatsp(x,y)); lz=lg(z);
  for (i=1; i<lz; i++) setlg(z[i], N+1);
  z = gmul(x,z);
  z = hnfmodid(z, glcm(gcoeff(x,1,1), gcoeff(y,1,1)));
  if (!gcmp1(dx)) z = gdiv(z,dx);
  return gerepileupto(av,z);
}

static GEN
computet2twist(GEN nf, GEN vdir)
{
  long j, ru = lg(nf[6]);
  GEN p1,MC, mat = (GEN)nf[5];

  if (!vdir) return (GEN)mat[3];
  MC=(GEN)mat[2]; p1=cgetg(ru,t_MAT);
  for (j=1; j<ru; j++)
  {
    GEN v = (GEN)vdir[j];
    if (gcmp0(v))
      p1[j]=MC[j];
    else if (typ(v) == t_INT)
      p1[j]=lmul2n((GEN)MC[j],itos(v)<<1);
    else
      p1[j]=lmul((GEN)MC[j],gpui(stoi(4),v,0));
  }
  return mulmat_real(p1,(GEN)mat[1]);
}

static GEN
chk_vdir(GEN nf, GEN vdir)
{
  if (!vdir || gcmp0(vdir)) return NULL;
  if (typ(vdir)!=t_VEC || lg(vdir) != lg(nf[6])) err(idealer5);
  return vdir;
}

GEN
ideallllredall(GEN nf, GEN I, GEN vdir, long prec, long precint)
{
  long tx,N,av,i,j;
  GEN I0,res,aI,p1,y,x,Nx,b,c1,c,pol;

  if (prec <= 0)
    precint = prec = (long)nfnewprec(nf,-1);
  nf = checknf(nf);
  vdir = chk_vdir(nf,vdir);
  pol = (GEN)nf[1]; N = lgef(pol)-3;
  tx = idealtyp(&I,&aI); I0=I;
  res = aI? cgetg(3,t_VEC): NULL;
  if (tx == id_PRINCIPAL)
  {
    if (gcmp0(I))
    {
      y = cgetg(1, t_MAT);
      if (!aI) return y;
      res[2] = lcopy(aI);
    }
    else
    {
      y = idmat(N);
      if (!aI) return y;
      av = avma;
      res[2] = lpileupto(av, gsub(aI, get_arch(nf,I,prec)));
    }
    res[1] = (long)y; return res;
  }
  av = avma;
  if (tx != id_MAT || lg(I) != N+1) I = idealhermite_aux(nf,I);

  if (DEBUGLEVEL>=6) msgtimer("entering idealllred");
  c1 = content(I); if (gcmp1(c1)) c1 = NULL; else I = gdiv(I,c1);

  for (i=1; ; i++)
  {
    p1 = computet2twist(nf,vdir);
    if (DEBUGLEVEL>=6) msgtimer("twisted T2");
    y = qf_base_change(p1,I,1);
    j = 1 + (gexpo(y)>>TWOPOTBITS_IN_LONG);
    if (j<0) j=0;
    p1 = lllgramintern(y,100,1,j+precint);
    if (p1) break;

    if (i == MAXITERPOL) err(accurer,"ideallllredall");
    precint=(precint<<1)-2; prec=max(prec,precint);
    if (DEBUGLEVEL) err(warnprec,"ideallllredall",precint);
    nf=nfnewprec(nf,(j>>1)+precint);
  }
  y = gmul(I,(GEN)p1[1]); /* small elt in I */
  if (DEBUGLEVEL>=6) msgtimer("lllgram");
  if (isnfscalar(y))
  { /* already reduced */
    if (!aI) 
    {
      if (I == I0) { avma = av; return gcopy(I); }
      return gerepileupto(av, gcopy(I));
    }
    if (I == I0)
    {
      avma = av;
      I = gcopy(I);
      aI = gcopy(aI);
    }
    else
    {
      if (typ(aI) == t_POLMOD)
      {
        c1 = gclone(c1);
        I = gerepileupto(av, I);
        aI = gmul(c1,aI); gunclone(c1);
      }
      else
      {
        I = gerepileupto(av, I);
        aI = gcopy(aI);
      }
    }
    res[1]=(long)I; res[2]=(long)aI; return res;
  }

  x = gmul((GEN)nf[7], y);
  Nx = subres(pol,x);
  b = gmul(Nx, ginvmod(x,pol));
  b = algtobasis_intern(nf,b);
  if (DEBUGLEVEL>=6) msgtimer("x/b");

  p1 = cgetg(N+1,t_MAT); /* = I Nx / x integral */
  for (i=1; i<=N; i++)
    p1[i] = (long)element_muli(nf,b,(GEN)I[i]);
  c = content(p1); if (!gcmp1(c)) p1 = gdiv(p1,c);
  if (DEBUGLEVEL>=6) msgtimer("new ideal");
  if (aI)
  {
    if (typ(aI) == t_POLMOD)
      y = gmul(x, gdiv(c1? mulii(c,c1): c,Nx));
    else
      y = gneg_i(get_arch(nf,y,prec));
    y = gclone(y);
  }

  if (isnfscalar((GEN)I[1]))
  /* c = content (I Nx / x) = Nx / den(I/x) --> d = den(I/x) = Nx / c
   * p1 = (d I / x); I[1,1] = I \cap Z --> d I[1,1] belongs to p1 and Z
   */
    p1 = hnfmodid(p1, mulii(gcoeff(I,1,1), divii(Nx, c)));
  else
    p1 = hnfmod(p1, detint(p1));
  p1 = gerepileupto(av, p1);
  if (DEBUGLEVEL>=6) msgtimer("final hnf");
  if (!aI) return p1;
  res[1]=(long)p1;
  aI = (typ(aI)==t_POLMOD)? gmul(aI,y): gadd(aI,y);
  res[2]=(long)aI;
  gunclone(y); return res;
}

GEN
ideallllred(GEN nf, GEN ix, GEN vdir, long prec)
{
  return ideallllredall(nf,ix,vdir,prec,prec);
}

GEN
minideal(GEN nf, GEN x, GEN vdir, long prec)
{
  long av = avma, N, tx;
  GEN p1,y;

  nf = checknf(nf);
  vdir = chk_vdir(nf,vdir);
  N = lgef(nf[1])-3;
  tx = idealtyp(&x,&y);
  if (tx == id_PRINCIPAL) return gcopy(x);
  if (tx != id_MAT || lg(x) != N+1) x = idealhermite_aux(nf,x);

  p1 = computet2twist(nf,vdir);
  y = qf_base_change(p1,x,0);
  y = gmul(x, (GEN)lllgram(y,prec)[1]);
  return gerepileupto(av, principalidele(nf,y,prec));
}
static GEN
appr_reduce(GEN s, GEN y, long N)
{
  GEN p1,u,z = cgetg(N+2,t_MAT);
  long i;

  s=gmod(s,gcoeff(y,1,1)); y=gmul(y,lllint(y));
  for (i=1; i<=N; i++) z[i]=y[i]; z[N+1]=(long)s;
  u=(GEN)ker(z)[1]; p1 = denom(u);
  if (!gcmp1(p1)) u=gmul(u,p1);
  p1=(GEN)u[N+1]; setlg(u,N+1);
  for (i=1; i<=N; i++) u[i]=lround(gdiv((GEN)u[i],p1));
  return gadd(s, gmul(y,u));
}

/* Given a fractional ideal x (if fl=0) or a prime ideal factorization
 * with possibly zero or negative exponents (if fl=1), gives a b such that
 * v_p(b)=v_p(x) for all prime ideals p dividing x (or in the factorization)
 * and v_p(b)>=0 for all other p, using the (standard) proof given in GTM 138.
 * Certainly not the most efficient, but sure.
 */
GEN
idealappr0(GEN nf, GEN x, long fl)
{
  long av=avma,tetpil,i,j,k,l,N,r,r2;
  GEN fact,fact2,list,ep,ep1,ep2,y,z,v,p1,p2,p3,p4,s,pr,alpha,beta,den;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans idealappr0() :\n");
    fprintferr(" x = "); outerr(x);
  }
  if (fl)
  {
    nf=checknf(nf); N=lgef(nf[1])-3;
    if (typ(x)!=t_MAT || lg(x)!=3)
      err(talker,"not a prime ideal factorization in idealappr0");
    fact=x; list=(GEN)fact[1]; ep=(GEN)fact[2]; r=lg(list);
    if (r==1) return gscalcol_i(gun,N);
    for (i=1; i<r; i++)
      if (signe(ep[i]) < 0) break;
    if (i < r)
    {
      ep1=cgetg(r,t_COL);
      for (i=1; i<r; i++)
        ep1[i] = (signe(ep[i])>=0)? zero: lnegi((GEN)ep[i]);
      fact[2]=(long)ep1; beta=idealappr0(nf,fact,1);
      fact2=idealfactor(nf,beta);
      p1=(GEN)fact2[1]; r2=lg(p1);
      ep2=(GEN)fact2[2]; l=r+r2-1;
      z=cgetg(l,t_VEC); for (i=1; i<r; i++) z[i]=list[i];
      ep1=cgetg(l,t_VEC);
      for (i=1; i<r; i++)
        ep1[i] = (signe(ep[i])<=0)? zero: licopy((GEN)ep[i]);
      j=r-1;
      for (i=1; i<r2; i++)
      {
        p3=(GEN)p1[i]; k=1;
        while (k<r &&
          (    !gegal((GEN)p3[1],gmael(list,k,1))
            || !element_val(nf,(GEN)p3[2],(GEN)list[k]) )) k++;
        if (k==r) { j++; z[j]=(long)p3; ep1[j]=ep2[i]; }
      }
      fact=cgetg(3,t_MAT);
      fact[1]=(long)z; setlg(z,j+1);
      fact[2]=(long)ep1; setlg(ep1,j+1);
      alpha=idealappr0(nf,fact,1); tetpil=avma;
      if (DEBUGLEVEL>2)
      {
        fprintferr(" alpha = "); outerr(alpha);
        fprintferr(" beta = "); outerr(beta);
      }
      return gerepile(av,tetpil,element_div(nf,alpha,beta));
    }	
    y=idmat(N);
    for (i=1; i<r; i++)
    {
      pr=(GEN)list[i];
      if (signe(ep[i]))
      {
        p4=addsi(1,(GEN)ep[i]); p1=powgi((GEN)pr[1],p4);
	if (cmpis((GEN)pr[4],N))
	{
	  p2=cgetg(3,t_MAT);
          p2[1]=(long)gscalcol_i(p1, N);
	  p2[2]=(long)element_pow(nf,(GEN)pr[2],p4);
          y=idealmat_mul(nf,y,p2);
	}
	else y=gmul(p1,y);
      }
      else y=idealmulprime(nf,y,pr);
    }
  }
  else
  {
    den=denom(x); if (gcmp1(den)) den=NULL; else x=gmul(den,x);
    x=idealhermite_aux(nf,x); N=lgef(nf[1])-3;
    fact=idealfactor(nf,x);
    list=(GEN)fact[1]; ep=(GEN)fact[2]; r=lg(list);
    if (r==1) { avma=av; return gscalcol_i(gun,N); }
    if (den)
    {
      fact2=idealfactor(nf,den);
      p1=(GEN)fact2[1]; r2=lg(p1);
      l=r+r2-1;
      z=cgetg(l,t_COL);   for (i=1; i<r; i++) z[i]=list[i];
      ep1=cgetg(l,t_COL); for (i=1; i<r; i++) ep1[i]=ep[i];
      j=r-1;
      for (i=1; i<r2; i++)
      {
	p3=(GEN)p1[i]; k=1;
	while (k<r && !gegal((GEN)list[k],p3)) k++;
	if (k==r){ j++; z[j]=(long)p3; ep1[j]=zero; }
      }
      fact=cgetg(3,t_MAT);
      fact[1]=(long)z; setlg(z,j+1);
      fact[2]=(long)ep1; setlg(ep1,j+1);
      alpha=idealappr0(nf,fact,1);
      if (DEBUGLEVEL>2) { fprintferr(" alpha = "); outerr(alpha); }
      tetpil=avma; return gerepile(av,tetpil,gdiv(alpha,den));
    }
    y=x; for (i=1; i<r; i++) y=idealmulprime(nf,y,(GEN)list[i]);
  }

  z=cgetg(r,t_VEC);
  for (i=1; i<r; i++)
  {
    pr=(GEN)list[i]; p4=addsi(1, (GEN)ep[i]); p1=powgi((GEN)pr[1],p4);
    if (cmpis((GEN)pr[4],N))
    {
      p2=cgetg(3,t_MAT);
      p2[1]=(long)gscalcol_i(p1,N);
      p2[2]=(long)element_pow(nf,(GEN)pr[5],p4);
      z[i]=ldiv(idealmat_mul(nf,y,p2),p1);
    }
    else z[i]=ldiv(y,p1);
  }
  v=idealaddmultoone(nf,z);
  s=cgetg(N+1,t_COL); for (i=1; i<=N; i++) s[i]=zero;
  for (i=1; i<r; i++)
  {
    pr=(GEN)list[i];
    if (signe(ep[i]))
      s=gadd(s,element_mul(nf,(GEN)v[i],element_pow(nf,(GEN)pr[2],(GEN)ep[i])));
    else s=gadd(s,(GEN)v[i]);
  }
  p3 = appr_reduce(s,y,N);
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de idealappr0 p3 = "); outerr(p3); }
  return gerepileupto(av,p3);
}

/* Given a prime ideal factorization x with possibly zero or negative exponents,
 * and a vector y of elements of nf, gives a b such that
 * v_p(b-y_p)>=v_p(x) for all prime ideals p in the ideal factorization
 * and v_p(b)>=0 for all other p, using the (standard) proof given in GTM 138.
 * Certainly not the most efficient, but sure.
 */
GEN
idealchinese(GEN nf, GEN x, GEN y)
{
  long ty=typ(y),av=avma,i,j,k,l,N,r,r2;
  GEN fact,fact2,list,ep,ep1,ep2,z,t,v,p1,p2,p3,p4,s,pr,den;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans idealchinese() :\n");
    fprintferr(" x = "); outerr(x);
    fprintferr(" y = "); outerr(y);
  }
  nf=checknf(nf); N=lgef(nf[1])-3;
  if (typ(x)!=t_MAT ||(lg(x)!=3))
    err(talker,"not a prime ideal factorization in idealchinese");
  fact=x; list=(GEN)fact[1]; ep=(GEN)fact[2]; r=lg(list);
  if (!is_vec_t(ty) || lg(y)!=r)
    err(talker,"not a suitable vector of elements in idealchinese");
  if (r==1) return gscalcol_i(gun,N);

  den=denom(y);
  if (!gcmp1(den))
  {
    fact2=idealfactor(nf,den);
    p1=(GEN)fact2[1]; r2=lg(p1);
    ep2=(GEN)fact2[2]; l=r+r2-1;
    z=cgetg(l,t_VEC); for (i=1; i<r; i++) z[i]=list[i];
    ep1=cgetg(l,t_VEC); for (i=1; i<r; i++) ep1[i]=ep[i];
    j=r-1;
    for (i=1; i<r2; i++)
    {
      p3=(GEN)p1[i]; k=1;
      while (k<r && !gegal((GEN)list[k],p3)) k++;
      if (k==r) { j++; z[j]=(long)p3; ep1[j]=ep2[i]; }
      else ep1[k]=ladd((GEN)ep1[k],(GEN)ep2[i]);
    }
    r=j+1; setlg(z,r); setlg(ep1,r); list=z; ep=ep1;
  }
  for (i=1; i<r; i++)
    if (signe(ep[i])<0) ep[i] = zero;
  t=idmat(N);
  for (i=1; i<r; i++)
  {
    pr=(GEN)list[i]; p4=(GEN)ep[i];
    if (signe(p4))
    {
      if (cmpis((GEN)pr[4],N))
      {
	p2=cgetg(3,t_MAT);
        p2[1]=(long)gscalcol_i(gpui((GEN)pr[1],p4,0), N);
	p2[2]=(long)element_pow(nf,(GEN)pr[2],p4);
        t=idealmat_mul(nf,t,p2);
      }
      else t=gmul(gpui((GEN)pr[1],p4,0),t);
    }
  }
  z=cgetg(r,t_VEC);
  for (i=1; i<r; i++)
  {
    pr=(GEN)list[i]; p4=(GEN)ep[i];
    if (cmpis((GEN)pr[4],N))
    {
      p2=cgetg(3,t_MAT); p1=gpui((GEN)pr[1],p4,0);
      p2[1]=(long)gscalcol_i(p1,N);
      p2[2]=(long)element_pow(nf,(GEN)pr[5],p4);
      z[i]=ldiv(idealmat_mul(nf,t,p2),p1);
    }
    else z[i]=ldiv(t,gpui((GEN)pr[1],p4,0));
  }
  v=idealaddmultoone(nf,z);
  s=cgetg(N+1,t_COL); for (i=1; i<=N; i++) s[i]=zero;
  for (i=1; i<r; i++)
    s = gadd(s,element_mul(nf,(GEN)v[i],(GEN)y[i]));

  p3 = appr_reduce(s,t,N);
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de idealchinese() : p3 = "); outerr(p3); }
  return gerepileupto(av,p3);
}

GEN
idealappr(GEN nf, GEN x) { return idealappr0(nf,x,0); }

GEN
idealapprfact(GEN nf, GEN x) { return idealappr0(nf,x,1); }

/* Given an integral ideal x and a in x, gives a b such that
 * x=aZ_K+bZ_K using a different algorithm than ideal_two_elt
 */
GEN
ideal_two_elt2(GEN nf, GEN x, GEN a)
{
  long ta=typ(a), av=avma,tetpil,i,r;
  GEN con,ep,b,list,fact;

  nf = checknf(nf);
  if (!is_extscalar_t(ta) && typ(a)!=t_COL)
    err(typeer,"ideal_two_elt2");
  x = idealhermite_aux(nf,x);
  if (gcmp0(x))
  {
    if (!gcmp0(a)) err(talker,"element not in ideal in ideal_two_elt2");
    avma=av; return gcopy(a);
  }
  con = content(x);
  if (gcmp1(con)) con = NULL; else { x = gdiv(x,con); a = gdiv(a,con); }
  a = principalideal(nf,a);
  if (!gcmp1(denom(gauss(x,a))))
    err(talker,"element does not belong to ideal in ideal_two_elt2");

  fact=idealfactor(nf,a); list=(GEN)fact[1];
  r=lg(list); ep = (GEN)fact[2];
  for (i=1; i<r; i++) ep[i]=lstoi(idealval(nf,x,(GEN)list[i]));
  b = centermod(idealappr0(nf,fact,1), gcoeff(x,1,1));
  tetpil=avma; b = con? gmul(b,con): gcopy(b);
  return gerepile(av,tetpil,b);
}

/* Given 2 integral ideals x and y in a number field nf gives a beta
 * belonging to nf such that beta.x is an integral ideal coprime to y
 */
GEN
idealcoprime(GEN nf, GEN x, GEN y)
{
  long av=avma,tetpil,i,r;
  GEN fact,list,p2,ep;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans idealcoprime() :\n");
    fprintferr(" x = "); outerr(x);
    fprintferr(" y = "); outerr(y);
  }
  fact=idealfactor(nf,y); list=(GEN)fact[1];
  r=lg(list); ep = (GEN)fact[2];
  for (i=1; i<r; i++) ep[i]=lstoi(-idealval(nf,x,(GEN)list[i]));
  tetpil=avma; p2=idealappr0(nf,fact,1);
  if (DEBUGLEVEL>4)
    { fprintferr(" sortie de idealcoprime() : p2 = "); outerr(p2); }
  return gerepile(av,tetpil,p2);
}

/* returns the first index i<=n such that x=v[i] if it exits, 0 otherwise */
long
isinvector(GEN v, GEN x, long n)
{
  long i;

  for (i=1; i<=n; i++)
    if (gegal((GEN)v[i],x)) return i;
  return 0;
}

/* Given an integral ideal x and three algebraic integers a, b and c in a
 * number field nf gives a beta belonging to nf such that beta.x^(-1) is an
 * integral ideal coprime to abc.Z_k
 */
static GEN
idealcoprimeinvabc(GEN nf, GEN x, GEN a, GEN b, GEN c)
{
  long av=avma,tetpil,i,j,r,ra,rb,rc;
  GEN facta,factb,factc,fact,factall,p1,p2,ep;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans idealcoprimeinvabc() :\n");
    fprintferr(" x = "); outerr(x); fprintferr(" a = "); outerr(a);
    fprintferr(" b = "); outerr(b); fprintferr(" c = "); outerr(c);
    flusherr();
  }
  facta=(GEN)idealfactor(nf,a)[1]; factb=(GEN)idealfactor(nf,b)[1];
  factc=(GEN)idealfactor(nf,c)[1]; ra=lg(facta); rb=lg(factb); rc=lg(factc);
  factall=cgetg(ra+rb+rc-2,t_COL);
  for (i=1; i<ra; i++) factall[i]=facta[i]; j=ra-1;
  for (i=1; i<rb; i++)
    if (!isinvector(factall,(GEN)factb[i],j)) factall[++j]=factb[i];
  for (i=1; i<rc; i++)
    if (!isinvector(factall,(GEN)factc[i],j)) factall[++j]=factc[i];
  r=j+1; fact=cgetg(3,t_MAT); p1=cgetg(r,t_COL); ep=cgetg(r,t_COL);
  for (i=1; i<r; i++) p1[i]=factall[i];
  for (i=1; i<r; i++) ep[i]=lstoi(idealval(nf,x,(GEN)p1[i]));
  fact[1]=(long)p1; fact[2]=(long)ep; tetpil=avma; p2=idealappr0(nf,fact,1);
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de idealcoprimeinvabc() : p2 = "); outerr(p2); }
  return gerepile(av,tetpil,p2);
}

/* Solve the equation ((b+aX).Z_k/((a,b).J),M)=Z_k. */
static GEN
findX(GEN nf, GEN a, GEN b, GEN J, GEN M)
{
  long N,i,k,r,v;
  GEN p1,p2,abJ,fact,list,ve,ep,int0,int1,int2,pr;

  if (DEBUGLEVEL>4)
  {
    fprintferr(" entree dans findX() :\n");
    fprintferr(" a = "); outerr(a); fprintferr(" b = "); outerr(b);
    fprintferr(" J = "); outerr(J); fprintferr(" M = "); outerr(M);
  }
  N=lgef(nf[1])-3;
  p1=cgetg(3,t_MAT); p1[1]=(long)a; p1[2]=(long)b;
  if (N==2) p1=idealmul(nf,p1,idmat(2));
  abJ=idealmul(nf,p1,J);
  fact=idealfactor(nf,M); list=(GEN)fact[1]; r=lg(list);
  ve=cgetg(r,t_VEC); ep=cgetg(r,t_VEC);
  int0=cgetg(N+1,t_COL); int1=cgetg(N+1,t_COL); int2=cgetg(N+1,t_COL);
  for (i=2; i<=N; i++) int0[i]=int1[i]=int2[i]=zero;
  int0[1]=zero; int1[1]=un; int2[1]=deux;
  for (i=1; i<r; i++)
  {
    pr=(GEN)list[i]; v=element_val(nf,a,pr);
    if (v)
    {
      ep[i]=un;
      ve[i] = (element_val(nf,b,pr)<=v)? (long)int0: (long)int1;
    }
    else
    {
      v=idealval(nf,abJ,pr);
      p1=element_div(nf,idealaddtoone_i(nf,a,pr),a);
      ep[i]=lstoi(v+1); k=1;
      while (k<=v)
      {
	p1=element_mul(nf,p1,gsub(int2,element_mul(nf,a,p1)));
	k<<=1;
      }
      p1=element_mul(nf,p1,gsub(element_pow(nf,(GEN)pr[2],stoi(v)),b));
      ve[i]=lmod(p1,gpuigs((GEN)pr[1],v+1));
    }
  }
  fact[2]=(long)ep; p2=idealchinese(nf,fact,ve);
  if (DEBUGLEVEL>2) { fprintferr(" sortie de findX() : p2 = "); outerr(p2); }
  return p2;
}

/* A usage interne. Given a, b, c, d in nf, gives an algebraic integer y in
 * nf such that [c,d]-y.[a,b] is "small"
 */
static GEN
nfreducemat(GEN nf, GEN a, GEN b, GEN c, GEN d)
{
  long av=avma,tetpil,i,i1,i2,j,j1,j2,k,N;
  GEN p1,p2,X,M,y,mult,s;

  mult=(GEN)nf[9]; N=lgef(nf[1])-3; X=cgetg(N+1,t_COL);
  for (j=1; j<=N; j++)
  {
    s=gzero;
    for (i=1; i<=N; i++) for (k=1; k<=N; k++)
    {
      p1=gcoeff(mult,k,j+(i-1)*N);
      if (!gcmp0(p1))
	s=gadd(s,gmul(p1,gadd(gmul((GEN)a[i],(GEN)c[k]),
	                      gmul((GEN)b[i],(GEN)d[k]))));
    }
    X[j]=(long)s;
  }
  M=cgetg(N+1,t_MAT);
  for (j2=1; j2<=N; j2++)
  {
    p1=cgetg(N+1,t_COL); M[j2]=(long)p1;
    for (j1=1; j1<=N; j1++)
    {
      s=gzero;
      for (i1=1; i1<=N; i1++)
       for (i2=1; i2<=N; i2++)
        for (k=1; k<=N; k++)
	{
	  p2=gmul(gcoeff(mult,k,j1+(i1-1)*N),gcoeff(mult,k,j2+(i2-1)*N));
	  if (!gcmp0(p2))
            s=gadd(s,gmul(p2,gadd(gmul((GEN)a[i1],(GEN)a[i2]),
                                  gmul((GEN)b[i1],(GEN)b[i2]))));
	}
      p1[j1]=(long)s;
    }
  }
  y=gauss(M,X); tetpil=avma;
  return gerepile(av,tetpil,ground(y));
}

/* Given 3 algebraic integers a,b,c in a number field nf given by their
 * components on the integral basis, gives a three-component vector [d,e,U]
 * whose first two components are algebraic integers d,e and the third a
 * unimodular 3x3-matrix U such that [a,b,c]*U=[0,d,e]
 */
GEN
threetotwo2(GEN nf, GEN a, GEN b, GEN c)
{
  long av=avma,tetpil,i,N;
  GEN y,p1,p2,p3,M,X,Y,J,e,b1,c1,u,v,U,int0,Z,pk;

  if (DEBUGLEVEL>2)
  {
    fprintferr(" On entre dans threetotwo2() : \n");
    fprintferr(" a = "); outerr(a);
    fprintferr(" b = "); outerr(b);
    fprintferr(" c = "); outerr(c);
  }
  if (gcmp0(a))
  {
    y=cgetg(4,t_VEC); y[1]=lcopy(b); y[2]=lcopy(c); y[3]=(long)idmat(3);
    return y;
  }
  if (gcmp0(b))
  {
    y=cgetg(4,t_VEC); y[1]=lcopy(a); y[2]=lcopy(c);
    e = idmat(3); i=e[1]; e[1]=e[2]; e[2]=i;
    y[3]=(long)e; return y;
  }
  if (gcmp0(c))
  {
    y=cgetg(4,t_VEC); y[1]=lcopy(a); y[2]=lcopy(b);
    e = idmat(3); i=e[1]; e[1]=e[3]; e[3]=e[2]; e[2]=i;
    y[3]=(long)e; return y;
  }

  N=lgef(nf[1])-3;
  p1=cgetg(4,t_MAT); p1[1]=(long)a; p1[2]=(long)b;
  p1[3]=(long)c; p1=idealhermite_aux(nf,p1);
  if (DEBUGLEVEL>2)
    { fprintferr(" ideal a.Z_k+b.Z_k+c.Z_k = "); outerr(p1); }
  J=idealdiv(nf,e=idealcoprimeinvabc(nf,p1,a,b,c),p1);
  if (DEBUGLEVEL>2)
    { fprintferr(" ideal J = "); outerr(J); fprintferr(" e = "); outerr(e); }
  p1=cgetg(3,t_MAT); p1[1]=(long)a; p1[2]=(long)b; M=idealmul(nf,p1,J);
  if (DEBUGLEVEL>2)
    { fprintferr(" ideal M=(a.Z_k+b.Z_k).J = "); outerr(M); }
  X=findX(nf,a,b,J,M);
  if (DEBUGLEVEL>2){ fprintferr(" X = "); outerr(X); }
  p1=gadd(b,element_mul(nf,a,X));
  p2=cgetg(3,t_MAT); p2[1]=(long)element_mul(nf,a,p1);
  p2[2]=(long)element_mul(nf,c,p1);
  if (N==2) p2=idealhermite_aux(nf,p2);
  p3=cgetg(3,t_MAT); p3[1]=(long)a; p3[2]=(long)b;
  p3=idealhermite_aux(nf,p3);
  if (DEBUGLEVEL>2)
    { fprintferr(" ideal a.Z_k+b.Z_k = "); outerr(p3); }
  Y=findX(nf,a,c,J,idealdiv(nf,p2,p3));
  if (DEBUGLEVEL>2) { fprintferr(" Y = "); outerr(Y); }
  b1=element_div(nf,p1,e);
  if (DEBUGLEVEL>2) { fprintferr(" b1 = "); outerr(b1); }
  p2=gadd(c,element_mul(nf,a,Y));
  c1=element_div(nf,p2,e);
  if (DEBUGLEVEL>2) { fprintferr(" c1 = "); outerr(c1); }
  p1=idealhermite_aux(nf,b1);
  p2=idealhermite_aux(nf,c1);
  p3=idealaddtoone(nf,p1,p2);
  u=element_div(nf,(GEN)p3[1],b1); v=element_div(nf,(GEN)p3[2],c1);
  if (DEBUGLEVEL>2)
    { fprintferr(" u = "); outerr(u); fprintferr(" v = "); outerr(v); }
  U=cgetg(4,t_MAT);
  p1=cgetg(4,t_COL); p2=cgetg(4,t_COL); p3=cgetg(4,t_COL);
  U[1]=(long)p1; U[2]=(long)p2; U[3]=(long)p3;
  p1[1]=lsub(element_mul(nf,X,c1),element_mul(nf,Y,b1));
  p1[2]=(long)c1; p1[3]=lneg(b1);
  int0 = zerocol(N);
  p2[1]=(long)gscalcol_i(gun,N);
  p2[2]=p2[3]=(long)int0;
  Z=gadd(element_mul(nf,X,u),element_mul(nf,Y,v));
  pk=nfreducemat(nf,c1,(GEN)p1[3],u,v);
  p3[1]=(long)int0; p3[2]=lsub(u,element_mul(nf,pk,c1));
  p3[3]=(long)gadd(v,element_mul(nf,pk,b1));
  e=gadd(e,element_mul(nf,a,gsub(element_mul(nf,pk,(GEN)p1[1]),Z)));
  tetpil=avma;
  y=cgetg(4,t_VEC); y[1]=lcopy(a); y[2]=lcopy(e); y[3]=lcopy(U);
  if (DEBUGLEVEL>2)
    { fprintferr(" sortie de threetotwo2() : y = "); outerr(y); }
  return gerepile(av,tetpil,y);
}

/* Given 3 algebraic integers a,b,c in a number field nf given by their
 * components on the integral basis, gives a three-component vector [d,e,U]
 * whose first two components are algebraic integers d,e and the third a
 * unimodular 3x3-matrix U such that [a,b,c]*U=[0,d,e] Naive method which may
 * not work, but fast and small coefficients.
 */
GEN
threetotwo(GEN nf, GEN a, GEN b, GEN c)
{
  long av=avma,tetpil,i,N;
  GEN pol,p1,p2,p3,p4,y,id,hu,h,V,U,r,vd,q1,q1a,q2,q2a,na,nb,nc,nr;

  nf=checknf(nf); pol=(GEN)nf[1]; N=lgef(pol)-3; id=idmat(N);
  na=gnorml2(a); nb=gnorml2(b); nc=gnorml2(c);
  U=gmul(idmat(3),gmodulsg(1,pol));
  if (gcmp(nc,nb)<0)
  {
    p1=c; c=b; b=p1; p1=nc; nc=nb; nb=p1;
    p1=(GEN)U[3]; U[3]=U[2]; U[2]=(long)p1;
  }
  if (gcmp(nc,na)<0)
  {
    p1=a; a=c; c=p1; p1=na; na=nc; nc=p1;
    p1=(GEN)U[1]; U[1]=U[3]; U[3]=(long)p1;
  }
  while (!gcmp0(gmin(na,nb)))
  {
    p1=cgetg(2*N+1,t_MAT);
    for (i=1; i<=N; i++)
    {
      p1[i]=(long)element_mul(nf,a,(GEN)id[i]);
      p1[i+N]=(long)element_mul(nf,b,(GEN)id[i]);
    }
    hu=hnfall(p1); h=(GEN)hu[1]; V=(GEN)hu[2];
    p2=(GEN)ker(concatsp(h,c))[1]; p3=(GEN)p2[N+1];
    p4=cgetg(N+1,t_COL);
    for (i=1; i<=N; i++) p4[i]=(long)ground(gdiv((GEN)p2[i],p3));
    r=gadd(c,gmul(h,p4));
    vd=cgetg(N+1,t_MAT); for (i=1; i<=N; i++) vd[i]=V[N+i];
    p2=gmul(vd,p4);
    q1=cgetg(N+1,t_COL); q2=cgetg(N+1,t_COL);
    for (i=1; i<=N; i++) { q1[i]=p2[i]; q2[i]=p2[i+N]; }
    q1a=basistoalg(nf,q1); q2a=basistoalg(nf,q2);
    U[3]=(long)gadd((GEN)U[3],gadd(gmul(q1a,(GEN)U[1]),gmul(q2a,(GEN)U[2])));
    nr=gnorml2(r);
    if (gcmp(nr,gmax(na,nb))>=0) err(talker,"threetotwo does not work");
    if (gcmp(na,nb)>=0)
    {
      c=a; nc=na; a=r; na=nr; p1=(GEN)U[1]; U[1]=U[3]; U[3]=(long)p1;
    }
    else
    {
      c=b; nc=nb; b=r; nb=nr; p1=(GEN)U[2]; U[2]=U[3]; U[3]=(long)p1;
    }
  }
  if (!gcmp0(na))
  {
    p1=a; a=b; b=p1; p1=(GEN)U[1]; U[1]=U[2]; U[2]=(long)p1;
  }
  tetpil=avma; y=cgetg(4,t_VEC); y[1]=lcopy(b); y[2]=lcopy(c);
  y[3]=(long)algtobasis(nf,U); return gerepile(av,tetpil,y);
}

/* Given 2 algebraic integers a,b in a number field nf given by their
 * components on the integral basis, gives a three-components vector [d,e,U]
 * whose first two component are algebraic integers d,e and the third a
 * unimodular 2x2-matrix U such that [a,b]*U=[d,e], with d and e hopefully
 * smaller than a and b.
 */
GEN
twototwo(GEN nf, GEN a, GEN b)
{
  long av=avma,tetpil;
  GEN pol,p1,y,U,r,qr,qa,na,nb,nr;

  nf=checknf(nf);
  pol=(GEN)nf[1];
  na=gnorml2(a); nb=gnorml2(b);
  U=gmul(idmat(2),gmodulsg(1,pol));
  if (gcmp(na,nb)>0)
  {
    p1=a; a=b; b=p1; p1=na; na=nb; nb=p1;
    p1=(GEN)U[2]; U[2]=U[1]; U[1]=(long)p1;
  }

  while (!gcmp0(na))
  {
    qr=nfdivres(nf,b,a); r=(GEN)qr[2]; nr=gnorml2(r);
    if (gcmp(nr,na)<0)
    {
      b=a; a=r; nb=na; na=nr; qa=basistoalg(nf,(GEN)qr[1]);
      p1=gsub((GEN)U[2],gmul(qa,(GEN)U[1])); U[2]=U[1]; U[1]=(long)p1;
    }
    else
    {
      if (gcmp(nr,nb)<0)
      {
	qa=basistoalg(nf,(GEN)qr[1]);
	U[2]=lsub((GEN)U[2],gmul(qa,(GEN)U[1]));
      }
      break;
    }
  }
  tetpil=avma; y=cgetg(4,t_VEC); y[1]=lcopy(a); y[2]=lcopy(b);
  y[3]=(long)algtobasis(nf,U); return gerepile(av,tetpil,y);
}

GEN
elt_mul_get_table(GEN nf, GEN x)
{
  long i,lx = lg(x);
  GEN mul=cgetg(lx,t_MAT);

  /* assume w_1 = 1 */
  mul[1]=(long)x;
  for (i=2; i<lx; i++) mul[i] = (long)element_mulid(nf,x,i);
  return mul;
}

GEN
elt_mul_table(GEN mul, GEN z)
{
  long av = avma, i, lx = lg(mul);
  GEN p1 = gmul((GEN)z[1], (GEN)mul[1]);

  for (i=2; i<lx; i++) 
    if (!gcmp0((GEN)z[i])) p1 = gadd(p1, gmul((GEN)z[i], (GEN)mul[i]));
  return gerepileupto(av, p1);
}

GEN
element_mulvec(GEN nf, GEN x, GEN v)
{
  long lv=lg(v),i;
  GEN y = cgetg(lv,t_COL);

  if (typ(x) == t_COL)
  {
    GEN mul = elt_mul_get_table(nf,x);
    for (i=1; i<lv; i++) 
      y[i] = (long)elt_mul_table(mul,(GEN)v[i]);
  }
  else
  { /* scalar */
    for (i=1; i<lv; i++) 
      y[i] = lmul(x, (GEN)v[i]);
  }
  return y;
}

static GEN
element_mulvecrow(GEN nf, GEN x, GEN m, long i, long lim)
{
  long lv,j;
  GEN y, mul = elt_mul_get_table(nf,x);

  lv=min(lg(m),lim+1); y=cgetg(lv,t_VEC);
  for (j=1; j<lv; j++) 
    y[j] = (long)elt_mul_table(mul,gcoeff(m,i,j));
  return y;
}

/* Given an element x and an ideal in matrix form (not necessarily HNF),
 * gives an r such that x-r is in ideal and r is small. No checks
 */
GEN
element_reduce(GEN nf, GEN x, GEN ideal)
{
  long tx=typ(x),av=avma,tetpil,N,i;
  GEN p1,u;

  if (is_extscalar_t(tx))
    x = algtobasis_intern(checknf(nf), x);
  N = lg(x); p1=cgetg(N+1,t_MAT);
  for (i=1; i<N; i++) p1[i]=ideal[i];
  p1[N]=(long)x; u=(GEN)ker(p1)[1];
  p1=(GEN)u[N]; setlg(u,N);
  for (i=1; i<N; i++) u[i]=lround(gdiv((GEN)u[i],p1));
  u=gmul(ideal,u); tetpil=avma;
  return gerepile(av,tetpil,gadd(u,x));
}

/* A torsion-free module M over Z_K will be given by a row vector [A,I] with
 * two components. I=[\a_1,...,\a_k] is a row vector of k fractional ideals
 * given in HNF. A is an nxk matrix (same k and n the rank of the module)
 * such that if A_j is the j-th column of A then M=\a_1A_1+...\a_kA_k. We say
 * that [A,I] is a pseudo-basis if k=n
 */

/* Given a torsion-free module x as above outputs a pseudo-basis for x in
 * Hermite Normal Form
 */
GEN
nfhermite(GEN nf, GEN x)
{
  long av0 = avma, av,lim,i,j,def,k,m;
  GEN p1,p2,y,A,I,J;

  nf=checknf(nf);
  if (typ(x)!=t_VEC || lg(x)!=3) err(talker,"not a module in nfhermite");
  A=(GEN)x[1]; I=(GEN)x[2]; k=lg(A)-1;
  if (typ(A)!=t_MAT) err(talker,"not a matrix in nfhermite");
  if (typ(I)!=t_VEC || lg(I)!=k+1)
    err(talker,"not a correct ideal list in nfhermite");
  if (!k) err(talker,"not a matrix of maximal rank in nfhermite");
  m=lg(A[1])-1;
  if (k<m) err(talker,"not a matrix of maximal rank in nfhermite");

  av = avma; lim = stack_lim(av, 1);
  p1 = cgetg(k+1,t_MAT); for (j=1; j<=k; j++) p1[j]=A[j];
  A = p1; I = dummycopy(I);
  J = cgetg(k+1,t_VEC);
  for (j=1; j<=k; j++)
  {
    if (typ(I[j])!=t_MAT) I[j]=(long)idealhermite_aux(nf,(GEN)I[j]);
    J[j] = zero;
  }

  def = k+1;
  for (i=m; i>=1; i--)
  {
    GEN den,p4,p5,p6,u,v,newid, invnewid = NULL;

    def--; j=def; while (j>=1 && gcmp0(gcoeff(A,i,j))) j--;
    if (!j) err(talker,"not a matrix of maximal rank in nfhermite");
    if (j==def) j--;
    else
    {
      p1=(GEN)A[j]; A[j]=A[def]; A[def]=(long)p1;
      p1=(GEN)I[j]; I[j]=I[def]; I[def]=(long)p1;
    }
    p1=gcoeff(A,i,def); p2=element_inv(nf,p1);
    A[def]=(long)element_mulvec(nf,p2,(GEN)A[def]);
    I[def]=(long)idealmul(nf,p1,(GEN)I[def]);
    for (  ; j; j--)
    {
      p1=gcoeff(A,i,j);
      if (gcmp0(p1)) continue;

      p2=idealmul(nf,p1,(GEN)I[j]);
      newid = idealadd(nf,p2,(GEN)I[def]);
      invnewid = hnfideal_inv(nf,newid);
      p4 = idealmul(nf, p2,        invnewid);
      p5 = idealmul(nf,(GEN)I[def],invnewid);
      y = idealaddtoone(nf,p4,p5);
      u=element_div(nf,(GEN)y[1],p1); v=(GEN)y[2];
      p6=gsub((GEN)A[j],element_mulvec(nf,p1,(GEN)A[def]));
      A[def]=ladd(element_mulvec(nf,u,(GEN)A[j]),
                  element_mulvec(nf,v,(GEN)A[def]));
      A[j]=(long)p6;
      I[j]=(long)idealmul(nf,idealmul(nf,(GEN)I[j],(GEN)I[def]),invnewid);
      I[def]=(long)newid; den=denom((GEN)I[j]);
      if (!gcmp1(den))
      {
        I[j]=lmul(den,(GEN)I[j]);
        A[j]=ldiv((GEN)A[j],den);
      }
    }
    if (!invnewid) invnewid = hnfideal_inv(nf,(GEN)I[def]);
    p1=(GEN)I[def]; J[def]=(long)invnewid;
    for (j=def+1; j<=k; j++)
    {
      p2 = gsub(element_reduce(nf,gcoeff(A,i,j),idealmul(nf,p1,(GEN)J[j])),
                gcoeff(A,i,j));
      A[j] = ladd((GEN)A[j],element_mulvec(nf,p2,(GEN)A[def]));
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[3];
      if(DEBUGMEM>1) err(warnmem,"nfhermite, i = %ld", i);
      gptr[0]=&A; gptr[1]=&I; gptr[2]=&J; gerepilemany(av,gptr,3);
    }
  }
  y = cgetg(3,t_VEC);
  p1 = cgetg(m+1,t_MAT); y[1] = (long)p1;
  p2 = cgetg(m+1,t_VEC); y[2] = (long)p2;
  for (j=1; j<=m; j++) p1[j] = lcopy((GEN)A[j+k-m]);
  for (j=1; j<=m; j++) p2[j] = lcopy((GEN)I[j+k-m]);
  return gerepileupto(av0, y);
}

/* A torsion module M over Z_K will be given by a row vector [A,I,J] with
 * three components. I=[b_1,...,b_n] is a row vector of k fractional ideals
 * given in HNF, J=[a_1,...,a_n] is a row vector of n fractional ideals in
 * HNF. A is an nxn matrix (same n) such that if A_j is the j-th column of A
 * and e_n is the canonical basis of K^n, then
 * M=(b_1e_1+...+b_ne_n)/(a_1A_1+...a_nA_n)
 */

/* We input a torsion module x=[A,I,J] as above, and output the
 * smith normal form as K=[\c_1,...,\c_n] such that x=Z_K/\c_1+...+Z_K/\c_n.
 */
GEN
nfsmith(GEN nf, GEN x)
{
  long av,tetpil,i,j,k,l,lim,c,n,m,N;
  GEN p1,p2,p3,p4,z,b,u,v,w,d,dinv,unnf,A,I,J;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (typ(x)!=t_VEC || lg(x)!=4) err(talker,"not a module in nfsmith");
  A=(GEN)x[1]; I=(GEN)x[2]; J=(GEN)x[3];
  if (typ(A)!=t_MAT) err(talker,"not a matrix in nfsmith");
  n=lg(A)-1;
  if (typ(I)!=t_VEC || lg(I)!=n+1 || typ(J)!=t_VEC || lg(J)!=n+1)
    err(talker,"not a correct ideal list in nfsmith");
  if (!n) err(talker,"not a matrix of maximal rank in nfsmith");
  m=lg(A[1])-1;
  if (n<m) err(talker,"not a matrix of maximal rank in nfsmith");
  if (n>m) err(impl,"nfsmith for non square matrices");

  av=avma; lim=stack_lim(av,1);
  p1 = cgetg(n+1,t_MAT); for (j=1; j<=n; j++) p1[j]=A[j];
  A = p1; I = dummycopy(I); J=dummycopy(J);
  for (j=1; j<=n; j++)
    if (typ(I[j])!=t_MAT) I[j]=(long)idealhermite_aux(nf,(GEN)I[j]);
  for (j=1; j<=n; j++)
    if (typ(J[j])!=t_MAT) J[j]=(long)idealhermite_aux(nf,(GEN)J[j]);
  for (i=n; i>=2; i--)
  {
    do
    {
      c=0;
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(A,i,j);
	if (!gcmp0(p1))
	{
	  p2=gcoeff(A,i,i);
	  d=nfbezout(nf,p2,p1,(GEN)J[i],(GEN)J[j],&u,&v,&w,&dinv);
	  if (!gcmp0(u))
	  {
	    if (!gcmp0(v))
	      b=gadd(element_mulvec(nf,u,(GEN)A[i]),
	             element_mulvec(nf,v,(GEN)A[j]));
	    else b=element_mulvec(nf,u,(GEN)A[i]);
	  }
	  else b=element_mulvec(nf,v,(GEN)A[j]);
	  A[j]=lsub(element_mulvec(nf,p2,(GEN)A[j]),
	            element_mulvec(nf,p1,(GEN)A[i]));
	  A[i]=(long)b; J[j]=(long)w; J[i]=(long)d;
	}
      }
      for (j=i-1; j>=1; j--)
      {
	p1=gcoeff(A,j,i);
	if (!gcmp0(p1))
	{
	  p2=gcoeff(A,i,i);
	  d=nfbezout(nf,p2,p1,(GEN)I[i],(GEN)I[j],&u,&v,&w,&dinv);
	  if (gcmp0(u))
	    b=element_mulvecrow(nf,v,A,j,i);
	  else
	  {
	    if (gcmp0(v))
	      b=element_mulvecrow(nf,u,A,i,i);
	    else
	      b=gadd(element_mulvecrow(nf,u,A,i,i),
	             element_mulvecrow(nf,v,A,j,i));
	  }
	  p3=gsub(element_mulvecrow(nf,p2,A,j,i),
	          element_mulvecrow(nf,p1,A,i,i));
	  for (k=1; k<=i; k++) { coeff(A,j,k)=p3[k]; coeff(A,i,k)=b[k]; }
	  I[j]=(long)w; I[i]=(long)d; c++;
	}
      }
      if (!c)
      {
	b=gcoeff(A,i,i); if (gcmp0(b)) break;

	b=idealmul(nf,b,idealmul(nf,(GEN)J[i],(GEN)I[i]));
	for (k=1; k<i; k++)
	  for (l=1; l<i; l++)
	  {
	    p3 = gcoeff(A,k,l);
	    if (!gcmp0(p3))
            {
              p4 = idealmul(nf,p3,idealmul(nf,(GEN)J[l],(GEN)I[k]));
	      if (!gegal(idealadd(nf,b,p4), b))
              {
                b=idealdiv(nf,(GEN)I[k],(GEN)I[i]);
                p4=gauss(idealdiv(nf,(GEN)J[i],idealmul(nf,p3,(GEN)J[l])),b);
                l=1; while (l<=N && gcmp1(denom((GEN)p4[l]))) l++;
                if (l>N) err(talker,"bug2 in nfsmith");
                p3=element_mulvecrow(nf,(GEN)b[l],A,k,i);
                for (l=1; l<=i; l++)
                  coeff(A,i,l) = ladd(gcoeff(A,i,l),(GEN)p3[l]);
              
                k = l = i; c = 1;
              }
            }
	  }
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        GEN *gptr[3];
	if(DEBUGMEM>1) err(warnmem,"nfsmith");
        gptr[0]=&A; gptr[1]=&I; gptr[2]=&J; gerepilemany(av,gptr,3);
      }
    }
    while (c);
  }
  unnf=gscalcol_i(gun,N);
  p1=gcoeff(A,1,1); coeff(A,1,1)=(long)unnf;
  J[1]=(long)idealmul(nf,p1,(GEN)J[1]);
  for (i=2; i<=n; i++)
    if (!gegal(gcoeff(A,i,i),unnf)) err(talker,"bug in nfsmith");
  tetpil=avma; z=cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++) z[i]=(long)idealmul(nf,(GEN)I[i],(GEN)J[i]);
  return gerepile(av,tetpil,z);
}

/*******************************************************************/
/*                                                                 */
/*          ALGEBRE LINEAIRE DANS LES CORPS DE NOMBRES             */
/*                                                                 */
/*******************************************************************/

#define trivlift(x) ((typ(x)==t_POLMOD)? (GEN)x[2]: lift_intern(x))

GEN
element_mulmodpr2(GEN nf, GEN x, GEN y, GEN prhall)
{
  long av=avma;
  GEN p1;

  nf=checknf(nf); checkprhall(prhall);
  p1 = element_mul(nf,x,y);
  return gerepileupto(av,nfreducemodpr(nf,p1,prhall));
}

/* On ne peut PAS definir ca comme les autres par
 * #define element_divmodpr() nfreducemodpr(element_div())
 * car le element_div ne marche pas en general
 */
GEN
element_divmodpr(GEN nf, GEN x, GEN y, GEN prhall)
{
  long av=avma;
  GEN p1;

  nf=checknf(nf); checkprhall(prhall);
  p1=lift_intern(gdiv(gmodulcp(gmul((GEN)nf[7],trivlift(x)), (GEN)nf[1]),
                      gmodulcp(gmul((GEN)nf[7],trivlift(y)), (GEN)nf[1])));
  p1=algtobasis_intern(nf,p1);
  return gerepileupto(av,nfreducemodpr(nf,p1,prhall));
}

GEN
element_invmodpr(GEN nf, GEN y, GEN prhall)
{
  long av=avma;
  GEN p1;

  p1=ginvmod(gmul((GEN)nf[7],trivlift(y)), (GEN)nf[1]);
  p1=algtobasis_intern(nf,p1);
  return gerepileupto(av,nfreducemodpr(nf,p1,prhall));
}

GEN
element_powmodpr(GEN nf,GEN x,GEN k,GEN prhall)
{
  long av=avma,N,s;
  GEN y,z;

  nf=checknf(nf); checkprhall(prhall);
  N=lgef(nf[1])-3;
  s=signe(k); k=(s>=0)?k:negi(k);
  z=x; y = gscalcol_i(gun,N);
  for(;;)
  {
    if (mpodd(k)) y=element_mulmodpr(nf,z,y,prhall);
    k=shifti(k,-1);
    if (signe(k)) z=element_sqrmodpr(nf,z,prhall);
    else
    {
      cgiv(k); if (s<0) y = element_invmodpr(nf,y,prhall);
      return gerepileupto(av,y);
    }
  }
}

/* x est une matrice dont les coefficients sont des vecteurs dans la base
 * d'entiers modulo un ideal premier prhall, sous forme reduite modulo prhall.
 */
GEN
nfkermodpr(GEN nf, GEN x, GEN prhall)
{
  long i,j,k,r,t,n,m,av0,av,av1,av2,N,lim;
  GEN c,d,y,unnf,munnf,zeromodp,zeronf,p,pp,prh;

  nf=checknf(nf); checkprhall(prhall);
  if (typ(x)!=t_MAT) err(typeer,"nfkermodpr");
  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  prh=(GEN)prhall[1]; av0=avma;
  N=lgef(nf[1])-3; pp=gcoeff(prh,1,1);

  zeromodp=gmodulsg(0,pp);
  unnf=cgetg(N+1,t_COL); unnf[1]=(long)gmodulsg(1,pp);
  zeronf=cgetg(N+1,t_COL); zeronf[1]=(long)zeromodp;

  av=avma; munnf=cgetg(N+1,t_COL); munnf[1]=(long)gmodulsg(-1,pp);
  for (i=2; i<=N; i++)
    zeronf[i] = munnf[i] = unnf[i] = (long)zeromodp;

  m=lg(x[1])-1; x=dummycopy(x); r=0;
  c=new_chunk(m+1); for (k=1; k<=m; k++) c[k]=0;
  d=new_chunk(n+1); av1=avma; lim=stack_lim(av1,1);
  for (k=1; k<=n; k++)
  {
    j=1;
    while (j<=m && (c[j] || gcmp0(gcoeff(x,j,k)))) j++;
    if (j > m) { r++; d[k]=0; continue; }

      p=element_divmodpr(nf,munnf,gcoeff(x,j,k),prhall);
      c[j]=k; d[k]=j; coeff(x,j,k)=(long)munnf;
      for (i=k+1; i<=n; i++)
	coeff(x,j,i)=(long)element_mulmodpr(nf,p,gcoeff(x,j,i),prhall);
      for (t=1; t<=m; t++)
	if (t!=j)
	{
        p = gcoeff(x,t,k); if (gcmp0(p)) continue;
        coeff(x,t,k) = (long)zeronf;
	  for (i=k+1; i<=n; i++)
            coeff(x,t,i)=ladd(gcoeff(x,t,i),
	                      element_mulmodpr(nf,p,gcoeff(x,j,i),prhall));
          if (low_stack(lim, stack_lim(av1,1)))
          {
            if (DEBUGMEM>1) err(warnmem,"nfkermodpr, k = %ld / %ld",k,n);
            av2=avma; x=gerepile(av1,av2,gcopy(x));
          }
	}
  }
  if (!r) { avma=av0; return cgetg(1,t_MAT); }
  av1=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    p=cgetg(n+1,t_COL); y[j]=(long)p; while (d[k]) k++;
    for (i=1; i<k; i++) p[i]=d[i]? lcopy(gcoeff(x,d[i],k)): (long)zeronf;
    p[k]=(long)unnf; for (i=k+1; i<=n; i++) p[i]=(long)zeronf;
  }
  return gerepile(av,av1,y);
}

/* a.x=b ou b est un vecteur */
GEN
nfsolvemodpr(GEN nf, GEN a, GEN b, GEN prhall)
{
  long nbli,nbco,i,j,k,av=avma,tetpil;
  GEN aa,x,p,m,u;

  nf=checknf(nf); checkprhall(prhall);
  if (typ(a)!=t_MAT) err(typeer,"nfsolvemodpr");
  nbco=lg(a)-1; nbli=lg(a[1])-1;
  if (typ(b)!=t_COL) err(typeer,"nfsolvemodpr");
  if (lg(b)!=nbco+1) err(mattype1,"nfsolvemodpr");
  x=cgetg(nbli+1,t_COL);
  for (j=1; j<=nbco; j++) x[j]=b[j];
  aa=cgetg(nbco+1,t_MAT);
  for (j=1; j<=nbco; j++)
  {
    aa[j]=lgetg(nbli+1,t_COL);
    for (i=1; i<=nbli; i++) coeff(aa,i,j)=coeff(a,i,j);
  }
  for (i=1; i<nbli; i++)
  {
    p=gcoeff(aa,i,i); k=i;
    if (gcmp0(p))
    {
      k=i+1; while (k<=nbli && gcmp0(gcoeff(aa,k,i))) k++;
      if (k>nbco) err(matinv1);
      for (j=i; j<=nbco; j++)
      {
	u=gcoeff(aa,i,j); coeff(aa,i,j)=coeff(aa,k,j);
	coeff(aa,k,j)=(long)u;
      }
      u=(GEN)x[i]; x[i]=x[k]; x[k]=(long)u;
      p=gcoeff(aa,i,i);
    }
    for (k=i+1; k<=nbli; k++)
    {
      m=gcoeff(aa,k,i);
      if (!gcmp0(m))
      {
	m=element_divmodpr(nf,m,p,prhall);
	for (j=i+1; j<=nbco; j++)
	  coeff(aa,k,j)=lsub(gcoeff(aa,k,j),
	                     element_mulmodpr(nf,m,gcoeff(aa,i,j),prhall));
	x[k]=lsub((GEN)x[k],element_mulmodpr(nf,m,(GEN)x[i],prhall));
      }
    }
  }
  /* Resolution systeme triangularise */
  p=gcoeff(aa,nbli,nbco); if (gcmp0(p)) err(matinv1);

  x[nbli]=(long)element_divmodpr(nf,(GEN)x[nbli],p,prhall);
  for (i=nbli-1; i>0; i--)
  {
    m=(GEN)x[i];
    for (j=i+1; j<=nbco; j++)
      m=gsub(m,element_mulmodpr(nf,gcoeff(aa,i,j),(GEN)x[j],prhall));
    x[i]=(long)element_divmodpr(nf,m,gcoeff(aa,i,i),prhall);
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(x));
}

GEN
nfsuppl(GEN nf, GEN x, long n, GEN prhall)
{
  long av=avma,av2,k,s,t,N,lx=lg(x);
  GEN y,p1,p2,p,unmodp,zeromodp,unnf,zeronf,prh;
  stackzone *zone;

  k=lx-1; if (k>n) err(suppler2);
  if (k && lg(x[1])!=n+1) err(talker,"incorrect dimension in nfsupl");
  N=lgef(nf[1])-3; prh=(GEN)prhall[1]; p=gcoeff(prh,1,1);

  zone  = switch_stack(NULL, 2*(3 + 2*lg(p) + N+1) + (n+3)*(n+1));
  switch_stack(zone,1);
  unmodp=gmodulsg(1,p); zeromodp=gmodulsg(0,p);
  unnf=gscalcol_proto(unmodp,zeromodp,N);
  zeronf=gscalcol_proto(zeromodp,zeromodp,N);
  y = idmat_intern(n,unnf,zeronf);
  switch_stack(zone,0); av2=avma;

  for (s=1; s<=k; s++)
  {
    p1=nfsolvemodpr(nf,y,(GEN)x[s],prhall); t=s;
    while (t<=n && gcmp0((GEN)p1[t])) t++;
    avma=av2; if (t>n) err(suppler2);
    p2=(GEN)y[s]; y[s]=x[s]; if (s!=t) y[t]=(long)p2;
  }
  avma=av; y=gcopy(y);
  free(zone); return y;
}

/* Given two fractional ideals a and b, gives x in a, y in b, z in b^-1,
   t in a^-1 such that xt-yz=1. In the present version, z is in Z. */
GEN
nfidealdet1(GEN nf, GEN a, GEN b)
{
  long av=avma;
  GEN x,p1,res,da,db;

  a = idealinv(nf,a);
  da = denom(a); if (!gcmp1(da)) a = gmul(da,a);
  db = denom(b); if (!gcmp1(db)) b = gmul(db,b);
  x = idealcoprime(nf,a,b);
  p1 = idealaddtoone(nf, idealmul(nf,x,a), b);

  res = cgetg(5,t_VEC);
  res[1] = lmul(x,da);
  res[2] = ldiv((GEN)p1[2],db);
  res[3] = lnegi(db);
  res[4] = (long) element_div(nf,(GEN)p1[1],(GEN)res[1]);
  return gerepileupto(av,res);
}

/* Given a pseudo-basis pseudo, outputs a multiple of its ideal determinant */
GEN
nfdetint(GEN nf,GEN pseudo)
{
  GEN pass,c,v,det1,piv,pivprec,vi,p1,x,I,unnf,zeronf,id,idprod;
  long i,j,k,rg,n,n1,m,m1,av=avma,av1,tetpil,lim,cm=0,N;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (typ(pseudo)!=t_VEC || lg(pseudo)!=3)
    err(talker,"not a module in nfdetint");
  x=(GEN)pseudo[1]; I=(GEN)pseudo[2];
  if (typ(x)!=t_MAT) err(talker,"not a matrix in nfdetint");
  n1=lg(x); n=n1-1; if (!n) return gun;

  m1=lg(x[1]); m=m1-1;
  if (typ(I)!=t_VEC || lg(I)!=n1)
    err(talker,"not a correct ideal list in nfdetint");

  unnf=gscalcol_i(gun,N); zeronf=zerocol(N);
  id=idmat(N); c=new_chunk(m1); for (k=1; k<=m; k++) c[k]=0;
  piv = pivprec = unnf;

  av1=avma; lim=stack_lim(av1,1);
  det1=idprod=gzero; /* dummy for gerepilemany */
  pass=cgetg(m1,t_MAT); v=cgetg(m1,t_COL);
  for (j=1; j<=m; j++)
  {
    v[j] = zero; /* dummy */
    p1=cgetg(m1,t_COL); pass[j]=(long)p1;
    for (i=1; i<=m; i++) p1[i]=(long)zeronf;
  }
  for (rg=0,k=1; k<=n; k++)
  {
    long t = 0;
    for (i=1; i<=m; i++)
      if (!c[i])
      {
	vi=element_mul(nf,piv,gcoeff(x,i,k));
	for (j=1; j<=m; j++)
	  if (c[j]) vi=gadd(vi,element_mul(nf,gcoeff(pass,i,j),gcoeff(x,j,k)));
	v[i]=(long)vi; if (!t && !gcmp0(vi)) t=i;
      }
    if (t)
    {
      pivprec = piv;
      if (rg == m-1)
      {
        if (!cm)
        {
          cm=1; idprod = id;
          for (i=1; i<=m; i++)
            if (i!=t)
              idprod = (idprod==id)? (GEN)I[c[i]]
                                   : idealmul(nf,idprod,(GEN)I[c[i]]);
        }
        p1 = idealmul(nf,(GEN)v[t],(GEN)I[k]); c[t]=0;
        det1 = (typ(det1)==t_INT)? p1: idealadd(nf,p1,det1);
      }
      else
      {
        rg++; piv=(GEN)v[t]; c[t]=k;
	for (i=1; i<=m; i++)
	  if (!c[i])
          {
	    for (j=1; j<=m; j++)
	      if (c[j] && j!=t)
	      {
		p1=gsub(element_mul(nf,piv,gcoeff(pass,i,j)),
		        element_mul(nf,(GEN)v[i],gcoeff(pass,t,j)));
		coeff(pass,i,j) = rg>1? (long) element_div(nf,p1,pivprec)
		                      : (long) p1;
	      }
            coeff(pass,i,t)=lneg((GEN)v[i]);
          }
      }
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[6];
      if(DEBUGMEM>1) err(warnmem,"nfdetint");
      gptr[0]=&det1; gptr[1]=&piv; gptr[2]=&pivprec; gptr[3]=&pass;
      gptr[4]=&v; gptr[5]=&idprod; gerepilemany(av1,gptr,6);
    }
  }
  if (!cm) { avma=av; return gscalmat(gzero,N); }
  tetpil=avma; return gerepile(av,tetpil,idealmul(nf,idprod,det1));
}

/* clean in place (destroy x) */
static void
nfcleanmod(GEN nf, GEN x, long lim, GEN detmat)
{
  long lx=lg(x),i;

  if (lim<=0 || lim>=lx) lim=lx-1;
  for (i=1; i<=lim; i++)
    x[i]=(long)element_reduce(nf,(GEN)x[i],detmat);
}

static GEN
zero_nfbezout(GEN nf,GEN b, GEN A,GEN B,GEN *u,GEN *v,GEN *w,GEN *di)
{
  long av, tetpil;
  GEN pab,d;

  d=idealmulelt(nf,b,B); *di=idealinv(nf,idealmat_to_hnf(nf,d));
  av=avma; pab=idealmul(nf,A,B); tetpil=avma;
  *w=gerepile(av,tetpil, idealmul(nf,pab,*di));
  *v=element_inv(nf,b);
  *u=gzero; return d;
}

/* Given elements a,b and ideals A, B, outputs d = a.A+b.B and gives
 * di=d^-1, w=A.B.di, u, v such that au+bv=1 and u in A.di, v in
 * B.di. Assume A, B non-zero, but a or b can be zero (not both)
 */
static GEN
nfbezout(GEN nf,GEN a,GEN b, GEN A,GEN B, GEN *u,GEN *v,GEN *w,GEN *di)
{
  GEN pab,pu,pv,pw,uv,d,dinv,pa,pb,pa1,pb1, *gptr[5];
  long av,tetpil;

  if (gcmp0(a))
  {
    if (gcmp0(b)) err(talker,"both elements zero in nfbezout");
    return zero_nfbezout(nf,b,A,B,u,v,w,di);
  }
  if (gcmp0(b))
    return zero_nfbezout(nf,a,B,A,v,u,w,di);

  av = avma;
  pa=idealmulelt(nf,a,A);
  pb=idealmulelt(nf,b,B);

  d=idealadd(nf,pa,pb); dinv=idealinv(nf,d);
  pa1=idealmullll(nf,pa,dinv);
  pb1=idealmullll(nf,pb,dinv);
  uv=idealaddtoone(nf,pa1,pb1);
  pab=idealmul(nf,A,B); tetpil=avma;

  pu=element_div(nf,(GEN)uv[1],a);
  pv=element_div(nf,(GEN)uv[2],b);
  d=gcopy(d); dinv=gcopy(dinv);
  pw=idealmul(nf,pab,dinv);

  *u=pu; *v=pv; *w=pw; *di=dinv;
  gptr[0]=u; gptr[1]=v; gptr[2]=w; gptr[3]=di;
  gptr[4]=&d; gerepilemanysp(av,tetpil,gptr,5);
  return d;
}

/* A usage interne. Pas de verifs ni gestion de pile */
GEN
idealoplll(GEN op(GEN,GEN,GEN), GEN nf, GEN x, GEN y)
{
  GEN z = op(nf,x,y), den = denom(z);

  if (gcmp1(den)) den = NULL; else z=gmul(den,z);
  z=gmul(z,lllintpartial(z));
  return den? gdiv(z,den): z;
}

/* A usage interne. Pas de verifs ni gestion de pile */
GEN
idealmulelt(GEN nf, GEN elt, GEN x)
{
  long t = typ(elt);
  GEN z;
  if (t == t_POL || t == t_POLMOD) elt = algtobasis(nf,elt);
  if (isnfscalar(elt)) elt = (GEN)elt[1];
  z = element_mulvec(nf, elt, x);
  settyp(z, t_MAT); return z;
}

GEN
nfhermitemod(GEN nf, GEN pseudo, GEN detmat)
{
  long av0=avma,li,co,av,tetpil,i,j,jm1,def,ldef,lim,N;
  GEN b,q,w,p1,p2,d,u,v,den,x,I,J,dinv,unnf,wh;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (typ(pseudo)!=t_VEC || lg(pseudo)!=3)
    err(talker,"not a module in nfhermitemod");
  x=(GEN)pseudo[1]; I=(GEN)pseudo[2];
  if (typ(x)!=t_MAT) err(talker,"not a matrix in nfhermitemod");
  co=lg(x);
  if (typ(I)!=t_VEC || lg(I)!=co)
    err(talker,"not a correct ideal list in nfhermitemod");
  if (co==1) return cgetg(1,t_MAT);

  li=lg(x[1]); x=dummycopy(x); I=dummycopy(I);
  unnf=gscalcol_i(gun,N);
  for (j=1; j<co; j++)
    if (typ(I[j])!=t_MAT) I[j]=(long)idealhermite_aux(nf,(GEN)I[j]);

  den=denom(detmat); if (!gcmp1(den)) detmat=gmul(den,detmat);
  detmat=gmul(detmat,lllintpartial(detmat));

  av=avma; lim=stack_lim(av,1);
  def=co; ldef=(li>co)?li-co+1:1;
  for (i=li-1; i>=ldef; i--)
  {
    def--; j=def-1; while (j && gcmp0(gcoeff(x,i,j))) j--;
    while (j)
    {
      jm1=j-1; if (!jm1) jm1=def;
      d=nfbezout(nf,gcoeff(x,i,j),gcoeff(x,i,jm1),(GEN)I[j],(GEN)I[jm1],
                 &u,&v,&w,&dinv);
      if (gcmp0(u))
        p1 = element_mulvec(nf,v,(GEN)x[jm1]);
      else
      {
	p1 = element_mulvec(nf,u,(GEN)x[j]);
	if (!gcmp0(v)) p1=gadd(p1, element_mulvec(nf,v,(GEN)x[jm1]));
      }
      x[j]=lsub(element_mulvec(nf,gcoeff(x,i,j),(GEN)x[jm1]),
                element_mulvec(nf,gcoeff(x,i,jm1),(GEN)x[j]));
      nfcleanmod(nf,(GEN)x[j],i,idealdivlll(nf,detmat,w));
      nfcleanmod(nf,p1,i,idealmullll(nf,detmat,dinv));
      x[jm1]=(long)p1; I[j]=(long)w; I[jm1]=(long)d;
      j--; while (j && gcmp0(gcoeff(x,i,j))) j--;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[2];
      if(DEBUGMEM>1) err(warnmem,"[1]: nfhermitemod");
      gptr[0]=&x; gptr[1]=&I; gerepilemany(av,gptr,2);
    }
  }
  b=detmat; wh=cgetg(li,t_MAT); def--;
  for (i=li-1; i>=1; i--)
  {
    d = nfbezout(nf,gcoeff(x,i,i+def),unnf,(GEN)I[i+def],b,&u,&v,&w,&dinv);
    p1 = element_mulvec(nf,u,(GEN)x[i+def]);
    nfcleanmod(nf,p1,i,idealmullll(nf,b,dinv));
    wh[i]=(long)p1; coeff(wh,i,i)=(long)unnf; I[i+def]=(long)d;
    if (i>1) b=idealmul(nf,b,dinv);
  }
  J=cgetg(li,t_VEC); J[1]=zero;
  for (j=2; j<li; j++) J[j]=(long)idealinv(nf,(GEN)I[j+def]);
  for (i=li-2; i>=1; i--)
  {
    for (j=i+1; j<li; j++)
    {
      q=idealmul(nf,(GEN)I[i+def],(GEN)J[j]);
      p1=gsub(element_reduce(nf,gcoeff(wh,i,j),q),gcoeff(wh,i,j));
      wh[j]=(long)gadd((GEN)wh[j],element_mulvec(nf,p1,(GEN)wh[i]));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[3];
      if(DEBUGMEM>1) err(warnmem,"[2]: nfhermitemod");
      gptr[0]=&wh; gptr[1]=&I; gptr[2]=&J; gerepilemany(av,gptr,3);
    }
  }
  tetpil=avma; p1=cgetg(3,t_VEC); p1[1]=lcopy(wh);
  p2=cgetg(li,t_VEC); p1[2]=(long)p2;
  for (j=1; j<li; j++) p2[j]=lcopy((GEN)I[j+def]);
  return gerepile(av0,tetpil,p1);
}
