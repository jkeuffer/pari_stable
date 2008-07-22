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
INLINE GEN
mkvec(GEN x) { GEN v = cgetg(2, t_VEC); gel(v,1) = x; return v; }
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
INLINE GEN
mkcol(GEN x) { GEN v = cgetg(2, t_COL); gel(v,1) = x; return v; }
INLINE GEN
mkcol2(GEN x, GEN y) {
  GEN v = cgetg(3,t_COL); gel(v,1) = x; gel(v,2) = y; return v; }
INLINE GEN
mkcolcopy(GEN x) { GEN v = cgetg(2, t_COL); gel(v,1) = gcopy(x); return v; }
INLINE GEN
mkmat(GEN x) { GEN v = cgetg(2, t_MAT); gel(v,1) = x; return v; }
INLINE GEN
mkmat2(GEN x, GEN y) { GEN v=cgetg(3,t_MAT); gel(v,1)=x; gel(v,2)=y; return v; }
INLINE GEN
mkmatcopy(GEN x) { GEN v = cgetg(2, t_MAT); gel(v,1) = gcopy(x); return v; }
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

INLINE GEN
constant_term(GEN x) { return signe(x)? gel(x,2): gen_0; }
INLINE GEN
leading_term(GEN x) { return lg(x) == 2? gen_0: gel(x,lg(x)-1); }

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

/*******************************************************************/
/*                                                                 */
/*                    ALGEBRAIC NUMBER THEORY                      */
/*                                                                 */
/*******************************************************************/
INLINE int
pr_is_inert(GEN P) { return pr_get_f(P) == lg(pr_get_gen(P))-1; }

