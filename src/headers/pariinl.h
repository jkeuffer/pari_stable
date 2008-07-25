/*******************************************************************/
/*                                                                 */
/*                          CONSTRUCTORS                           */
/*                                                                 */
/*******************************************************************/
INLINE GEN
mkintmod(GEN x, GEN y) { GEN v = cgetg(3, t_INTMOD);
  gel(v,1) = y; gel(v,2) = x; return v; }
INLINE GEN
mkintmodu(ulong x, ulong y) {
  GEN v = cgetg(3,t_INTMOD);
  gel(v,1) = utoipos(y);
  gel(v,2) = utoi(x); return v;
}
INLINE GEN
mkpolmod(GEN x, GEN y) { GEN v = cgetg(3, t_POLMOD);
  gel(v,1) = y; gel(v,2) = x; return v; }
INLINE GEN
mkfrac(GEN x, GEN y) { GEN v = cgetg(3, t_FRAC);
  gel(v,1) = x; gel(v,2) = y; return v; }
INLINE GEN
mkfraccopy(GEN x, GEN y) { GEN v = cgetg(3, t_FRAC);
  gel(v,1) = icopy(x); gel(v,2) = icopy(y); return v; }
INLINE GEN
mkrfrac(GEN x, GEN y) { GEN v = cgetg(3, t_RFRAC);
  gel(v,1) = x; gel(v,2) = y; return v; }
INLINE GEN
mkcomplex(GEN x, GEN y) { GEN v = cgetg(3, t_COMPLEX);
  gel(v,1) = x; gel(v,2) = y; return v; }
INLINE GEN
mkquad(GEN n, GEN x, GEN y) { GEN v = cgetg(4, t_QUAD);
  gel(v,1) = n; gel(v,2) = x; gel(v,3) = y; return v; }
/* vecsmall */
INLINE GEN
mkvecsmall(long x) { GEN v = cgetg(2, t_VECSMALL); v[1] = x; return v; }
INLINE GEN
mkvecsmall2(long x,long y) { GEN v = cgetg(3, t_VECSMALL);
  v[1]=x; v[2]=y; return v; }
INLINE GEN
mkvecsmall3(long x,long y,long z) { GEN v = cgetg(4, t_VECSMALL);
  v[1]=x; v[2]=y; v[3]=z; return v; }
INLINE GEN
mkvecsmall4(long x,long y,long z,long t) { GEN v = cgetg(5, t_VECSMALL);
  v[1]=x; v[2]=y; v[3]=z; v[4]=t; return v; }
/* vec */
INLINE GEN
mkvec(GEN x) { GEN v = cgetg(2, t_VEC); gel(v,1) = x; return v; }
INLINE GEN
mkvec2(GEN x, GEN y) {
  GEN v = cgetg(3,t_VEC); gel(v,1) = x; gel(v,2) = y; return v; }
INLINE GEN
mkvec3(GEN x, GEN y, GEN z) {
  GEN v=cgetg(4,t_VEC); gel(v,1) = x; gel(v,2) = y; gel(v,3) = z; return v; }
INLINE GEN
mkvec4(GEN x, GEN y, GEN z, GEN t) {
  GEN v=cgetg(5,t_VEC); gel(v,1) = x; gel(v,2) = y; gel(v,3) = z; gel(v,4) = t;
  return v; }
INLINE GEN
mkvec5(GEN x, GEN y, GEN z, GEN t, GEN u) {
  GEN v=cgetg(6,t_VEC); gel(v,1) = x; gel(v,2) = y; gel(v,3) = z; 
  gel(v,4) = t; gel(v,5) = u; return v; }
INLINE GEN
mkvecs(long x) { GEN v = cgetg(2, t_VEC); gel(v,1) = stoi(x); return v; }
INLINE GEN
mkvec2s(long x, long y) {
  GEN v = cgetg(3,t_VEC); gel(v,1) = stoi(x); gel(v,2) = stoi(y); return v; }
INLINE GEN
mkvec3s(long x, long y, long z) {
  GEN v=cgetg(4,t_VEC);
  gel(v,1)=stoi(x); gel(v,2)=stoi(y); gel(v,3)=stoi(z); return v;
}
INLINE GEN
mkveccopy(GEN x) { GEN v = cgetg(2, t_VEC); gel(v,1) = gcopy(x); return v; }
INLINE GEN
mkvec2copy(GEN x, GEN y) {
  GEN v = cgetg(3,t_VEC); gel(v,1) = gcopy(x); gel(v,2) = gcopy(y); return v; }
/* col */
INLINE GEN
mkcol(GEN x) { GEN v = cgetg(2, t_COL); gel(v,1) = x; return v; }
INLINE GEN
mkcol2(GEN x, GEN y) {
  GEN v = cgetg(3,t_COL); gel(v,1) = x; gel(v,2) = y; return v; }
INLINE GEN
mkcolcopy(GEN x) { GEN v = cgetg(2, t_COL); gel(v,1) = gcopy(x); return v; }
/* mat */
INLINE GEN
mkmat(GEN x) { GEN v = cgetg(2, t_MAT); gel(v,1) = x; return v; }
INLINE GEN
mkmat2(GEN x, GEN y) { GEN v=cgetg(3,t_MAT); gel(v,1)=x; gel(v,2)=y; return v; }
INLINE GEN
mkmatcopy(GEN x) { GEN v = cgetg(2, t_MAT); gel(v,1) = gcopy(x); return v; }
/* pol */
INLINE GEN
pol_x(long v) {
  GEN p = cgetg(4, t_POL);
  p[1] = evalsigne(1)|evalvarn(v);
  gel(p,2) = gen_0;
  gel(p,3) = gen_1; return p;
}
INLINE GEN
pol_1(long v) {
  GEN p = cgetg(3, t_POL);
  p[1] = evalsigne(1)|evalvarn(v);
  gel(p,2) = gen_1; return p;
}

INLINE GEN
const_vec(long n, GEN x)
{
  GEN v = cgetg(n+1, t_VEC);
  long i;
  for (i = 1; i <= n; i++) gel(v,i) = x;
  return v;
}
INLINE GEN
const_col(long n, GEN x)
{
  GEN v = cgetg(n+1, t_COL);
  long i;
  for (i = 1; i <= n; i++) gel(v,i) = x;
  return v;
}
INLINE GEN
const_vecsmall(long n, long c)
{
  long i;
  GEN V = cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) V[i] = c;
  return V;
}

/***   ZERO   ***/
/* O(p^e) */
INLINE GEN
zeropadic(GEN p, long e)
{
  GEN y = cgetg(5,t_PADIC);
  gel(y,4) = gen_0;
  gel(y,3) = gen_1;
  copyifstack(p,gel(y,2));
  y[1] = evalvalp(e) | evalprecp(0);
  return y;
}
/* O(pol_x(v)^e) */
INLINE GEN
zeroser(long v, long e)
{
  GEN x = cgetg(2, t_SER);
  x[1] = evalvalp(e) | evalvarn(v); return x;
}
/* 0 * pol_x(v) */
INLINE GEN
zeropol(long v)
{
  GEN x = cgetg(2,t_POL);
  x[1] = evalvarn(v); return x;
}
/* vector(n) */
INLINE GEN
zerocol(long n)
{
  GEN y = cgetg(n+1,t_COL);
  long i; for (i=1; i<=n; i++) gel(y,i) = gen_0;
  return y;
}
/* vectorv(n) */
INLINE GEN
zerovec(long n)
{
  GEN y = cgetg(n+1,t_VEC);
  long i; for (i=1; i<=n; i++) gel(y,i) = gen_0;
  return y;
}
/* matrix(m, n) */
INLINE GEN
zeromat(long m, long n)
{
  GEN y = cgetg(n+1,t_MAT);
  GEN v = zerocol(m);
  long i; for (i=1; i<=n; i++) gel(y,i) = v;
  return y;
}
/* = zero_zx, sv is a evalvarn()*/
INLINE GEN
zero_Flx(long sv)
{
  GEN x = cgetg(2, t_VECSMALL);
  x[1] = sv; return x;
}
INLINE GEN
zero_Flv(long n)
{
  GEN y = cgetg(n+1,t_VECSMALL);
  long i; for (i=1; i<=n; i++) y[i] = 0;
  return y;
}
/* matrix(m, n) */
INLINE GEN
zero_Flm(long m, long n)
{
  GEN y = cgetg(n+1,t_MAT);
  GEN v = zero_Flv(m);
  long i; for (i=1; i<=n; i++) gel(y,i) = v;
  return y;
}
/* matrix(m, n) */
INLINE GEN
zeromatcopy(long m, long n)
{
  GEN y = cgetg(n+1,t_MAT);
  long i; for (i=1; i<=n; i++) gel(y,i) = zerocol(m);
  return y;
}

/* i-th vector in the standard basis */
INLINE GEN
col_ei(long n, long i) { GEN e = zerocol(n); gel(e,i) = gen_1; return e; }
INLINE GEN
vec_ei(long n, long i) { GEN e = zerovec(n); gel(e,i) = gen_1; return e; }
INLINE GEN
vecsmall_ei(long n, long i) { GEN e = const_vecsmall(n,0); e[i] = 1; return e; }

/*******************************************************************/
/*                                                                 */
/*                    CONVERSION / ASSIGNMENT                      */
/*                                                                 */
/*******************************************************************/
INLINE GEN gtofp(GEN z, long prec);
INLINE GEN
ctofp(GEN x, long prec) { GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = gtofp(gel(x,1),prec);
  gel(z,2) = gtofp(gel(x,2),prec); return z;
}
INLINE double
gtodouble(GEN x)
{
  if (typ(x)!=t_REAL) {
    pari_sp av = avma;
    x = gtofp(x, DEFAULTPREC);
    avma = av;
  }
  return rtodbl(x);
}

/* Force z to be of type real/complex with floating point components */
INLINE GEN
gtofp(GEN z, long prec)
{
  switch(typ(z))
  {
    case t_INT:  return itor(z, prec);
    case t_FRAC: return fractor(z, prec);
    case t_REAL: return rtor(z, prec);
    case t_COMPLEX: return isrationalzero(gel(z,2))? gtofp(gel(z,1), prec)
                                                   : ctofp(z, prec);
    case t_QUAD: return quadtoc(z, prec);
    default: pari_err(typeer,"gtofp"); return NULL; /* not reached */
  }
}
/* y a t_REAL */
INLINE void
affgr(GEN x, GEN y)
{
  pari_sp av;
  switch(typ(x)) {
    case t_INT:  affir(x,y); break;
    case t_REAL: affrr(x,y); break;
    case t_FRAC: rdiviiz(gel(x,1),gel(x,2), y); break;
    case t_QUAD: av = avma; affgr(quadtoc(x,lg(y)), y); avma = av; break;
    default: pari_err(operf,"",x,y);
  }
}

INLINE GEN
affc_fixlg(GEN x, GEN res)
{
  if (typ(x) == t_COMPLEX)
  {
    affrr_fixlg(gel(x,1), gel(res,1));
    affrr_fixlg(gel(x,2), gel(res,2));
  }
  else
  {
    avma = (pari_sp)(res+3);
    res = cgetr(lg(gel(res,1)));
    affrr_fixlg(x, res);
  }
  return res;
}

/*******************************************************************/
/*                                                                 */
/*                          GEN SUBTYPES                           */
/*                                                                 */
/*******************************************************************/

INLINE int
is_const_t(long t) { return (t < t_POLMOD); }
INLINE int
is_extscalar_t(long t) { return (t <= t_POL); }
INLINE int
is_intreal_t(long t) { return (t <= t_REAL); }
INLINE int
is_matvec_t(long t) { return (t >= t_VEC && t <= t_MAT); }
INLINE int
is_noncalc_t(long tx) { return (tx) >= t_LIST; }
INLINE int
is_rational_t(long t) { return (t == t_INT || t == t_FRAC); }
INLINE int
is_recursive_t(long t) { return lontyp[t]; }
INLINE int
is_scalar_t(long t) { return (t < t_POL); }
INLINE int
is_vec_t(long t) { return (t == t_VEC || t == t_COL); }

/*******************************************************************/
/*                                                                 */
/*                         MISCELLANEOUS                           */
/*                                                                 */
/*******************************************************************/
/* POLYNOMIALS */
INLINE GEN
constant_term(GEN x) { return signe(x)? gel(x,2): gen_0; }
INLINE GEN
leading_term(GEN x) { return lg(x) == 2? gen_0: gel(x,lg(x)-1); }

INLINE GEN
RgX_div(GEN x, GEN y) { return RgX_divrem(x,y,NULL); }
INLINE GEN
RgX_rem(GEN x, GEN y) { return RgX_divrem(x,y,ONLY_REM); }
INLINE GEN
RgXQX_div(GEN x, GEN y, GEN T) { return RgXQX_divrem(x,y,T,NULL); }
INLINE GEN
RgXQX_rem(GEN x, GEN y, GEN T) { return RgXQX_divrem(x,y,T,ONLY_REM); }
INLINE GEN
FpX_div(GEN x, GEN y, GEN p) { return FpX_divrem(x,y,p, NULL); }
INLINE GEN
FpX_rem(GEN x, GEN y, GEN p) { return FpX_divrem(x,y,p, ONLY_REM); }
INLINE GEN
Flx_div(GEN x, GEN y, ulong p) { return Flx_divrem(x,y,p, NULL); }
INLINE GEN
FpV_FpC_mul(GEN x, GEN y, GEN p) { return FpV_dotproduct(x,y,p); }
INLINE GEN
F2x_div(GEN x, GEN y) { return F2x_divrem(x,y, NULL); }
INLINE GEN
zero_zx(long sv) { return zero_Flx(sv); }
INLINE GEN
polx_zx(long sv) { return polx_Flx(sv); }
INLINE GEN
zx_shift(GEN x, long n) { return Flx_shift(x,n); }
INLINE GEN
zx_renormalize(GEN x, long l) { return Flx_renormalize(x,l); }
INLINE GEN
zero_F2x(long sv) { return zero_Flx(sv); }
INLINE GEN
pol1_F2x(long sv) { return pol1_Flx(sv); }
INLINE int
F2x_cmp1(GEN x) { return Flx_cmp1(x); }
INLINE GEN
FpX_renormalize(GEN x, long lx)   { return ZX_renormalize(x,lx); }
INLINE GEN
FpXX_renormalize(GEN x, long lx)  { return ZX_renormalize(x,lx); }
INLINE GEN
FpXQX_renormalize(GEN x, long lx) { return ZX_renormalize(x,lx); }
INLINE GEN
F2x_renormalize(GEN x, long lx)   { return Flx_renormalize(x,lx); }

INLINE GEN
ZX_mul(GEN x, GEN y) { return RgX_mul(x, y); }
INLINE GEN
ZX_sqr(GEN x) { return RgX_sqr(x); }
INLINE GEN
ZX_ZXY_resultant(GEN a, GEN b) { return ZX_ZXY_rnfequation(a,b,NULL); }
INLINE long
sturm(GEN x) { return sturmpart(x, NULL, NULL); }
INLINE GEN
resultant(GEN x, GEN y) { return resultant_all(x,y,NULL); }

INLINE long
gval(GEN x, long v) {
  pari_sp av = avma;
  long n = ggval(x, pol_x(v));
  avma = av; return n;
}

/* LINEAR ALGEBRA */
INLINE GEN
zv_to_ZV(GEN x) { return vecsmall_to_vec(x); }
INLINE GEN
zc_to_ZC(GEN x) { return vecsmall_to_col(x); }
INLINE GEN
ZV_to_zv(GEN x) { return vec_to_vecsmall(x); }
INLINE GEN
zx_to_zv(GEN x, long N) { return Flx_to_Flv(x,N); }
INLINE GEN
zv_to_zx(GEN x, long sv) { return Flv_to_Flx(x,sv); }
INLINE GEN
zm_to_zxV(GEN x, long sv) { return Flm_to_FlxV(x,sv); }
INLINE GEN
zero_zm(long x, long y) { return zero_Flm(x,y); }
INLINE GEN
zero_zv(long x) { return zero_Flv(x); }
INLINE GEN
zm_transpose(GEN x) { return Flm_transpose(x); }
INLINE GEN
zm_copy(GEN x) { return Flm_copy(x); }
INLINE GEN
zv_copy(GEN x) { return Flv_copy(x); }
INLINE GEN
row_zm(GEN x, long i) { return row_Flm(x,i); }

INLINE GEN
ZC_hnfrem(GEN x, GEN y) { return ZC_hnfremdiv(x,y,NULL); }
INLINE GEN
ZM_hnfrem(GEN x, GEN y) { return ZM_hnfremdiv(x,y,NULL); }
INLINE GEN
ZM_lll(GEN x, double D, long f) { return ZM_lll_norms(x,D,f,NULL); }
INLINE GEN
RgM_inv(GEN a) { return RgM_solve(a, NULL); }

/* ARITHMETIC */
INLINE GEN
matpascal(long n) { return matqpascal(n, NULL); }
INLINE long
Z_issquare(GEN x) { return Z_issquareall(x, NULL); }
INLINE GEN
sqrti(GEN x) { return sqrtremi(x,NULL); }
INLINE GEN
gaddgs(GEN y, long s) { return gaddsg(s,y); }
INLINE int
gcmpgs(GEN y, long s) { return -gcmpsg(s,y); }
INLINE int
gequalgs(GEN y, long s) { return gequalsg(s,y); }
INLINE GEN
gmaxsg(long s, GEN y) { return gmaxgs(y,s); }
INLINE GEN
gminsg(long s, GEN y) { return gmings(y,s); }
INLINE GEN
gmulgs(GEN y, long s) { return gmulsg(s,y); }
INLINE GEN
gsubgs(GEN y, long s) { return gaddgs(y, -s); }
INLINE GEN
gdivsg(long s, GEN y) { return gdiv(stoi(s), y); }

/* negate in place */
INLINE void
togglesign(GEN x)
{
  if (x[1] & SIGNBITS) { x[1] ^= HIGHBIT; }
}
/* negate in place, except universal constants */
INLINE void
togglesign_safe(GEN *px)
{
  if      (*px == gen_1)  *px = gen_m1;
  else if (*px == gen_m1) *px = gen_1;
  else if (*px == gen_2)  *px = gen_m2;
  else if (*px == gen_m2) *px = gen_2;
  else togglesign(*px);
}

INLINE void
normalize_frac(GEN z) {
  if (signe(z[2]) < 0) { togglesign(gel(z,1)); setsigne(gel(z,2),1); }
}


INLINE GEN
powii(GEN x, GEN n)
{
  long ln = lgefint(n);
  if (ln == 3) {
    GEN z;
    if (signe(n) > 0) return powiu(x, n[2]);
    z = cgetg(3, t_FRAC);
    gel(z,1) = gen_1;
    gel(z,2) = powiu(x, n[2]);
    return z;
  }
  if (ln == 2) return gen_1; /* rare */
  /* should never happen */
  return powgi(x, n); /* overflow unless x = 0, 1, -1 */
}
/*******************************************************************/
/*                                                                 */
/*                    ALGEBRAIC NUMBER THEORY                      */
/*                                                                 */
/*******************************************************************/
INLINE GEN pr_get_p(GEN pr)  { return gel(pr,1); }
INLINE GEN pr_get_gen(GEN pr){ return gel(pr,2); }
/* .[2] instead of itos works: e and f are small positive integers */
INLINE long pr_get_e(GEN pr) { return gel(pr,3)[2]; }
INLINE long pr_get_f(GEN pr) { return gel(pr,4)[2]; }
INLINE GEN pr_get_tau(GEN pr){ return gel(pr,5); }
INLINE int
pr_is_inert(GEN P) { return pr_get_f(P) == lg(pr_get_gen(P))-1; }
INLINE GEN
pr_norm(GEN pr) { return powiu(pr_get_p(pr), pr_get_f(pr)); }

/* assume nf a genuine nf */
INLINE long
nf_get_degree(GEN nf) { return degpol(gel(nf,1)); }
INLINE long
nf_get_r1(GEN nf) { GEN x = gel(nf,2); return itou(gel(x,1)); }
INLINE long
nf_get_r2(GEN nf) { GEN x = gel(nf,2); return itou(gel(x,2)); }
INLINE void
nf_get_sign(GEN nf, long *r1, long *r2)
{
  GEN x = gel(nf,2);
  *r1 = itou(gel(x,1));
  *r2 = itou(gel(x,2));
}

