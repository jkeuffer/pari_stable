/*******************************************************************/
/*                                                                 */
/*                      Fichier Include PARI                       */
/*                    declarations generales                       */
/*                                                                 */
/*******************************************************************/
/* $Id$ */

/* alglin1.c */

GEN     concat(GEN x, GEN y);
GEN     concatsp(GEN x, GEN y);
GEN     deplin(GEN x);
GEN     det(GEN a);
GEN     det0(GEN a,long flag);
GEN     det2(GEN a);
GEN     dethnf(GEN x);
GEN     dethnf_i(GEN mat);
GEN     detint(GEN x);
GEN     diagonal(GEN x);
GEN     eigen(GEN x, long prec);
GEN     extract(GEN x, GEN l);
GEN     extract0(GEN x, GEN l1, GEN l2);
GEN     gaddmat(GEN x, GEN y);
GEN     gauss(GEN a, GEN b);
GEN     gaussmodulo(GEN M, GEN D, GEN Y);
GEN     gaussmodulo2(GEN M, GEN D, GEN Y);
GEN     gscalcol(GEN x, long n);
GEN     gscalcol_i(GEN x, long n);
GEN     gscalcol_proto(GEN z, GEN myzero, long n);
GEN     gscalmat(GEN x, long n);
GEN     gscalsmat(long x, long n);
GEN     gtomat(GEN x);
GEN     gtrans(GEN x);
GEN     hnfadd(GEN mit,GEN perm,GEN* ptdep,GEN* ptA,GEN* ptC,GEN extramat,GEN extraC);
GEN     hnfspec(long** mat,GEN perm,GEN* ptdep,GEN* ptA,GEN* ptC,long k0);
GEN     idmat(long n);
GEN     idmat_intern(long n,GEN myun,GEN myzero);
GEN     image(GEN x);
GEN     image2(GEN x);
GEN     image_mod_p(GEN x, GEN p);
GEN     imagecompl(GEN x);
GEN     imagereel(GEN x, long prec);
GEN     indexrank(GEN x);
GEN     inverseimage(GEN mat, GEN y);
long    isdiagonal(GEN x);
GEN     ker(GEN x);
GEN     ker_mod_p(GEN x, GEN p);
GEN     keri(GEN x);
GEN     matextract(GEN x, GEN l1, GEN l2);
GEN     matimage0(GEN x,long flag);
GEN     matker0(GEN x, long flag);
GEN     matmuldiagonal(GEN x, GEN d);
GEN     matmultodiagonal(GEN x, GEN y);
GEN     matsolvemod0(GEN M, GEN D, GEN Y,long flag);
GEN     mattodiagonal(GEN m);
long    rank(GEN x);
long    rank_mod_p(GEN x, GEN p);
GEN     suppl(GEN x);
GEN     suppl_intern(GEN x, GEN myid);
GEN     zerocol(long n);

/* alglin2.c */

GEN     adj(GEN x);
GEN     assmat(GEN x);
GEN     caract(GEN x, int v);
GEN     caract2(GEN p, GEN x, int v);
GEN     caradj(GEN x, long v, GEN *py);
GEN     caradj0(GEN x, long v);
GEN     carhess(GEN x, long v);
GEN     charpoly0(GEN x, int v,long flag);
GEN     conjvec(GEN x,long prec);
GEN     gconj(GEN x);
GEN     gnorm(GEN x);
GEN     gnorml2(GEN x);
GEN     gtrace(GEN x);
GEN     hess(GEN x);
GEN     hnf(GEN x);
GEN     hnfall(GEN x);
GEN     hnfhavas(GEN x);
GEN     hnflll(GEN x);
GEN     hnfmod(GEN x, GEN detmat);
GEN     hnfmodid(GEN x,GEN p);
GEN     hnfperm(GEN x);
GEN     intersect(GEN x, GEN y);
GEN     jacobi(GEN a, long prec);
GEN     matrixqz(GEN x, GEN pp);
GEN     matrixqz0(GEN x, GEN pp);
GEN     matrixqz2(GEN x);
GEN     matrixqz3(GEN x);
GEN     signat(GEN a);
GEN     smith(GEN x);
GEN     smith2(GEN x);
GEN     smithclean(GEN z);
GEN     sqred(GEN a);
GEN     sqred1(GEN a);
GEN     sqred1intern(GEN a, long flag);
GEN     sqred3(GEN a);

/* anal.c */

entree  *fetch_named_var(char *s, int doerr);
entree  *gp_variable(char *s);
void    delete_named_var(entree *ep);
long    delete_var(void);
long    fetch_user_var(char *s);
long    fetch_var(void);
GEN     flisexpr(char *t);
void    freeep(entree *ep);
long    hashvalue(char *s);
entree* install(void *f, char *name, char *code);
GEN     lisexpr(char *t);
GEN     lisseq(char *t);
long    manage_var(long n, entree *ep);
void    name_var(long n, char *s);
GEN     readseq(char *c, int strict);
GEN     strtoGENstr(char *s, long flag);

/* arith1.c */

GEN     bestappr(GEN x, GEN k);
GEN     bezout(GEN a, GEN b, GEN *u, GEN *v);
GEN     binaire(GEN x);
long    bittest(GEN x, long n);
long    carrecomplet(GEN x, GEN *pt);
long    cbezout(long a,long b,long *uu,long *vv);
long    cgcd(long a,long b);
GEN     chinois(GEN x, GEN y);
GEN     classno(GEN x);
GEN     classno2(GEN x);
GEN     fibo(long n);
GEN     fundunit(GEN x);
GEN     gbittest(GEN x, GEN n);
GEN     gboundcf(GEN x, long k);
GEN     gcarrecomplet(GEN x, GEN *pt);
GEN     gcarreparfait(GEN x);
GEN     gcf(GEN x);
GEN     gcf2(GEN b, GEN x);
GEN     gener(GEN m);
GEN     gfundunit(GEN x);
GEN     ggener(GEN m);
GEN     gisfundamental(GEN x);
GEN     gisprime(GEN x);
GEN     gispsp(GEN x);
GEN     gkrogs(GEN x, long y);
GEN     gkronecker(GEN x, GEN y);
GEN     gmillerrabin(GEN n, long k);
GEN     gnextprime(GEN n);
GEN     gprecprime(GEN n);
GEN     gracine(GEN a);
GEN     gregula(GEN x, long prec);
GEN     hclassno(GEN x);
long    hil(GEN x, GEN y, GEN p);
long    hil0(GEN x, GEN y, GEN p);
long    isfundamental(GEN x);
long    isprime(GEN x);
long    ispsp(GEN x);
long    krogs(GEN x, long y);
long    kronecker(GEN x, GEN y);
long    krosg(long s, GEN x);
long    kross(long x, long y);
void    lucas(long n, GEN *ln, GEN *ln1);
long    millerrabin(GEN n, long k);
GEN     mpfact(long n);
GEN     mpfactr(long n, long prec);
GEN     mpinvmod(GEN a, GEN m);
GEN     mppgcd(GEN a, GEN b);
GEN     mpsqrtmod(GEN a, GEN p);
GEN     order(GEN x);
GEN     pnqn(GEN x);
GEN     powmodulo(GEN a, GEN n, GEN m);
GEN     qfbclassno0(GEN x,long flag);
GEN     quaddisc(GEN x);
GEN     racine(GEN a);
GEN     regula(GEN x, long prec);
GEN     sfcont(GEN x, GEN x1, long k);
GEN     sfcont0(GEN x, GEN b, long flag);
GEN     znstar(GEN x);

/* arith2.c */

GEN     Qfb0(GEN x, GEN y, GEN z, GEN d, long prec);
GEN     addprimes(GEN primes);
GEN     auxdecomp(GEN n, long all);
long    bigomega(GEN n);
GEN     boundfact(GEN n, long lim);
GEN     compimag(GEN x, GEN y);
GEN     compimagraw(GEN x, GEN y);
GEN     compraw(GEN x, GEN y);
GEN     compreal(GEN x, GEN y);
GEN     comprealraw(GEN x, GEN y);
GEN     core(GEN n);
GEN     core0(GEN n,long flag);
GEN     core2(GEN n);
GEN     coredisc(GEN n);
GEN     coredisc0(GEN n,long flag);
GEN     coredisc2(GEN n);
GEN     decomp(GEN n);
GEN     divisors(GEN n);
GEN     factorint(GEN n, long flag);
GEN     gbigomega(GEN n);
GEN     gboundfact(GEN n, long lim);
GEN     gissquarefree(GEN x);
GEN     gmu(GEN n);
GEN     gnumbdiv(GEN n);
GEN     gomega(GEN n);
GEN     gphi(GEN n);
GEN     gsumdiv(GEN n);
GEN     gsumdivk(GEN n,long k);
byteptr initprimes(long maxnum);
long    issquarefree(GEN x);
long    mu(GEN n);
GEN     nucomp(GEN x, GEN y, GEN l);
GEN     nudupl(GEN x, GEN l);
GEN     numbdiv(GEN n);
GEN     nupow(GEN x, GEN n);
long    omega(GEN n);
GEN     phi(GEN n);
GEN     powraw(GEN x, long n);
GEN     powrealraw(GEN x, long n);
GEN     prime(long n);
GEN     primeform(GEN x, GEN p, long prec);
GEN     primes(long n);
GEN     qfbred0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD);
GEN     qfi(GEN x, GEN y, GEN z);
GEN     qfr(GEN x, GEN y, GEN z, GEN d);
GEN     redimag(GEN x);
GEN     redreal(GEN x);
GEN     redrealnod(GEN x, GEN isqrtD);
GEN     removeprimes(GEN primes);
GEN     rhoreal(GEN x);
GEN     rhorealnod(GEN x, GEN isqrtD);
GEN     smallfact(GEN n);
GEN     sqcompimag(GEN x);
GEN     sqcompreal(GEN x);
GEN     sumdiv(GEN n);
GEN     sumdivk(GEN n,long k);

/* base1.c */

GEN     bnfnewprec(GEN nf, long prec);
void    check_pol_int(GEN x);
GEN     check_units(GEN x, char *f);
void    checkbid(GEN bid);
GEN     checkbnf(GEN bnf);
void    checkbnr(GEN bnr);
void    checkbnrgen(GEN bnr);
void    checkid(GEN x, long N);
GEN     checknf(GEN nf);
void    checkprhall(GEN prhall);
void    checkprimeid(GEN bid);
void    checkrnf(GEN rnf);
GEN     differente(GEN nf, GEN premiers);
GEN     galois(GEN x, long prec);
GEN     galoisapply(GEN nf, GEN aut, GEN x);
GEN     get_bnf(GEN x,int *t);
GEN     get_nf(GEN x,int *t);
GEN     get_primeid(GEN x);
GEN     glambdak(GEN nfz, GEN s, long prec);
int     gpolcomp(GEN p1, GEN p2);
GEN     gsmith(GEN x);
GEN     gsmith2(GEN x);
GEN     gzetak(GEN nfz, GEN s, long prec);
GEN     gzetakall(GEN nfz, GEN s, long flag, long prec);
GEN     initalg(GEN x, long prec);
GEN     initalgred(GEN x, long prec);
GEN     initalgred2(GEN x, long prec);
GEN     initzeta(GEN pol, long prec);
GEN     mathnf0(GEN x,long flag);
GEN     matsnf0(GEN x,long flag);
GEN     nfinit0(GEN x,long flag, long prec);
GEN     nfnewprec(GEN nf, long prec);
GEN     rootsof1(GEN x);
GEN     tschirnhaus(GEN x);

/* base2.c */

GEN     allbase4(GEN f, long code, GEN *y, GEN *ptw);
GEN     base(GEN x, GEN *y);
GEN     base2(GEN x, GEN *y);
GEN     compositum(GEN pol1, GEN pol2);
GEN     compositum2(GEN pol1, GEN pol2);
GEN     discf(GEN x);
GEN     discf2(GEN x);
GEN     factcp(GEN p,GEN f,GEN beta);
GEN     factoredbase(GEN x, GEN p, GEN *y);
GEN     factoreddiscf(GEN x, GEN p);
GEN     gcdpm(GEN f1,GEN f2,GEN pm);
long    idealval(GEN nf,GEN ix,GEN vp);
GEN     nfbasis(GEN x, GEN *y,long flag,GEN p);
GEN     nfbasis0(GEN x,long flag,GEN p);
GEN     nfdiscf0(GEN x,long flag, GEN p);
GEN     nfreducemodideal(GEN nf,GEN x,GEN ideal);
GEN     nfreducemodpr(GEN nf, GEN x, GEN prhall);
GEN     nfreducemodpr2(GEN nf, GEN x, GEN prhall);
GEN     polcompositum0(GEN pol1, GEN pol2,long flag);
GEN     primedec(GEN nf,GEN p);
GEN     rnfbasis(GEN bnf, GEN order);
GEN     rnfdet(GEN nf, GEN order);
GEN     rnfdet0(GEN nf, GEN x, GEN y);
GEN     rnfdet2(GEN nf, GEN A, GEN I);
GEN     rnfdiscf(GEN nf, GEN pol);
GEN     rnfequation(GEN nf, GEN pol2);
GEN     rnfequation2(GEN nf, GEN pol);
GEN     rnfequation0(GEN nf, GEN pol2, long flall);
GEN     rnfhermitebasis(GEN bnf, GEN order);
long    rnfisfree(GEN bnf, GEN order);
GEN     rnflllgram(GEN nf, GEN pol, GEN order,long prec);
GEN     rnfpolred(GEN nf, GEN pol, long prec);
GEN     rnfpolredabs(GEN nf, GEN pol, long flag, long prec);
GEN     rnfpseudobasis(GEN nf, GEN pol);
GEN     rnfsimplifybasis(GEN bnf, GEN order);
GEN     rnfsteinitz(GEN nf, GEN order);
GEN     smallbase(GEN x, GEN *y);
GEN     smalldiscf(GEN x);
GEN     subcyclo(GEN p, GEN d, int n);

/* base3.c */

GEN     algtobasis(GEN nf, GEN x);
GEN     algtobasis_intern(GEN nf,GEN x);
GEN     basistoalg(GEN nf, GEN x);
GEN     element_div(GEN nf, GEN x, GEN y);
GEN     element_inv(GEN nf, GEN x);
GEN     element_invmodideal(GEN nf, GEN x, GEN ideal);
GEN     element_mul(GEN nf,GEN x,GEN y);
GEN     element_mulid(GEN nf, GEN x, long i);
GEN     element_mulvec(GEN nf, GEN x, GEN v);
GEN     element_pow(GEN nf,GEN x,GEN k);
GEN     element_pow_mod_p(GEN nf, GEN x, GEN n, GEN p);
GEN     element_powmodideal(GEN nf,GEN x,GEN k,GEN ideal);
GEN     element_powmodidele(GEN nf,GEN x,GEN k,GEN idele,GEN structarch);
GEN     element_sqr(GEN nf,GEN x);
long    element_val(GEN nf, GEN x, GEN vp);
long    element_val2(GEN nf, GEN x, GEN d, GEN vp);
GEN     ideallist(GEN nf,long bound);
GEN     ideallist0(GEN nf,long bound, long flag);
GEN     ideallistarch(GEN nf, GEN list, GEN arch);
GEN     ideallistarch0(GEN nf, GEN list, GEN arch,long flag);
GEN     ideallistarchgen(GEN nf, GEN list, GEN arch);
GEN     ideallistunit(GEN nf,long bound);
GEN     ideallistunitarch(GEN bnf,GEN list,GEN arch);
GEN     ideallistunitarchgen(GEN bnf,GEN list,GEN arch);
GEN     ideallistunitgen(GEN nf,long bound);
GEN     ideallistzstar(GEN nf,long bound);
GEN     ideallistzstargen(GEN nf,long bound);
GEN     idealstar0(GEN nf, GEN x,long flag);
int     isnfscalar(GEN x);
GEN     lllreducemodmatrix(GEN x,GEN y);
GEN     nfdiveuc(GEN nf, GEN a, GEN b);
GEN     nfdivres(GEN nf, GEN a, GEN b);
GEN     nfmod(GEN nf, GEN a, GEN b);
GEN     nfreducemodidele(GEN nf,GEN g,GEN idele,GEN structarch);
GEN     nfshanks(GEN nf,GEN x,GEN g0,GEN pr,GEN prhall);
GEN     reducemodmatrix(GEN x, GEN y);
GEN     zarchstar(GEN nf,GEN x,GEN arch,long nba);
GEN     zideallog(GEN nf,GEN x,GEN bigideal);
GEN     zidealstar(GEN nf, GEN x);
GEN     zidealstarinit(GEN nf, GEN x);
GEN     zidealstarinitall(GEN nf, GEN x,long flun);
GEN     zidealstarinitgen(GEN nf, GEN x);
GEN     zidealstarinitjoin(GEN nf, GEN bid1, GEN bid2);
GEN     zidealstarinitjoinarch(GEN nf, GEN bid1, GEN arch, long nba);
GEN     zidealstarinitjoinarchgen(GEN nf, GEN bid1, GEN arch, long nba);
GEN     zidealstarinitjoingen(GEN nf, GEN bid1, GEN bid2);
GEN     znlog(GEN x, GEN g);
GEN     zsigne(GEN nf,GEN alpha,GEN arch);

/* base4.c */

GEN     element_divmodpr(GEN nf, GEN x, GEN y, GEN prhall);
GEN     element_invmodpr(GEN nf, GEN y, GEN prhall);
GEN     element_mulmodpr2(GEN nf, GEN x, GEN y, GEN prhall);
GEN     element_powmodpr(GEN nf, GEN x, GEN k, GEN prhall);
GEN     element_reduce(GEN nf, GEN x, GEN ideal);
GEN     ideal_two_elt(GEN nf, GEN ix);
GEN     ideal_two_elt0(GEN nf, GEN ix, GEN a);
GEN     ideal_two_elt2(GEN nf, GEN x, GEN a);
GEN     idealadd(GEN nf, GEN x, GEN y);
GEN     idealaddmultoone(GEN nf, GEN list);
GEN     idealaddtoone(GEN nf, GEN x, GEN y);
GEN     idealaddtoone0(GEN nf, GEN x, GEN y);
GEN     idealappr(GEN nf, GEN x);
GEN     idealappr0(GEN nf, GEN x, long fl);
GEN     idealapprfact(GEN nf, GEN x);
GEN     idealchinese(GEN nf, GEN x, GEN y);
GEN     idealcoprime(GEN nf, GEN x, GEN y);
GEN     idealdiv(GEN nf, GEN x, GEN y);
GEN     idealdiv0(GEN nf, GEN x, GEN y,long flag);
GEN     idealdivexact(GEN nf, GEN x, GEN y);
GEN     idealfactor(GEN nf, GEN x);
GEN     idealhermite(GEN nf, GEN x);
GEN     idealhermite2(GEN nf, GEN a, GEN b);
GEN     idealhnf0(GEN nf, GEN a, GEN b);
GEN     idealintersect(GEN nf, GEN x, GEN y);
GEN     idealinv(GEN nf, GEN ix);
GEN     idealinv0(GEN nf, GEN ix,long flag);
GEN     ideallllred(GEN nf,GEN ix,GEN vdir,long prec);
GEN     ideallllredall(GEN nf, GEN ix, GEN vdir, long prec, long precint);
GEN     idealmul(GEN nf, GEN ix, GEN iy);
GEN     idealmul0(GEN nf, GEN ix, GEN iy, long flag, long prec);
GEN     idealmulelt(GEN nf, GEN elt, GEN x);
GEN     idealmulh(GEN nf, GEN ix, GEN iy);
GEN     idealmulprime(GEN nf,GEN ix,GEN vp);
GEN     idealmulred(GEN nf, GEN ix, GEN iy, long prec);
GEN     idealnorm(GEN nf, GEN x);
GEN     idealoplll(GEN op(GEN,GEN,GEN), GEN nf, GEN x, GEN y);
GEN     idealpow(GEN nf, GEN ix, GEN n);
GEN     idealpow0(GEN nf, GEN ix, GEN n, long flag, long prec);
GEN     idealpowred(GEN nf, GEN ix, GEN n,long prec);
GEN     idealpows(GEN nf, GEN ideal, long iexp);
GEN     ideleaddone(GEN nf, GEN x, GEN idele);
int     ishnfall(GEN x);
long    isideal(GEN nf,GEN x);
long    isinvector(GEN v, GEN x, long n);
GEN     minideal(GEN nf,GEN ix,GEN vdir,long prec);
GEN     nfdetint(GEN nf,GEN pseudo);
GEN     nfhermite(GEN nf, GEN x);
GEN     nfhermitemod(GEN nf, GEN x, GEN detmat);
GEN     nfkermodpr(GEN nf, GEN x, GEN prhall);
GEN     nfmodprinit(GEN nf, GEN pr);
GEN     nfsmith(GEN nf, GEN x);
GEN     nfsolvemodpr(GEN nf, GEN a, GEN b, GEN prhall);
GEN     oldidealinv(GEN nf, GEN ix);
GEN     prime_to_ideal(GEN nf, GEN vp);
GEN     principalideal(GEN nf, GEN a);
GEN     principalidele(GEN nf, GEN a, long prec);
GEN     threetotwo(GEN nf, GEN a, GEN b, GEN c);
GEN     threetotwo2(GEN nf, GEN a, GEN b, GEN c);
GEN     twototwo(GEN nf, GEN a, GEN b);

/* base5.c */

GEN     lift_to_pol(GEN x);
GEN     matalgtobasis(GEN nf, GEN x);
GEN     matbasistoalg(GEN nf, GEN x);
GEN     rnfalgtobasis(GEN rnf, GEN x);
GEN     rnfbasistoalg(GEN rnf, GEN x);
GEN     rnfelementabstorel(GEN rnf, GEN x);
GEN     rnfelementdown(GEN rnf, GEN x);
GEN     rnfelementreltoabs(GEN rnf, GEN x);
GEN     rnfelementup(GEN rnf, GEN x);
GEN     rnfidealabstorel(GEN rnf, GEN x);
GEN     rnfidealdown(GEN rnf, GEN x);
GEN     rnfidealhermite(GEN rnf, GEN x);
GEN     rnfidealmul(GEN rnf,GEN x,GEN y);
GEN     rnfidealnormabs(GEN rnf, GEN x);
GEN     rnfidealnormrel(GEN rnf, GEN x);
GEN     rnfidealreltoabs(GEN rnf, GEN x);
GEN     rnfidealtwoelement(GEN rnf,GEN x);
GEN     rnfidealup(GEN rnf, GEN x);
GEN     rnfinitalg(GEN nf,GEN pol,long prec);

/* bibli1.c */

GEN     algdep(GEN x, long n, long prec);
GEN     algdep0(GEN x, long n, long bit,long prec);
GEN     algdep2(GEN x, long n, long bit);
GEN     factoredpolred(GEN x, GEN p, long prec);
GEN     factoredpolred2(GEN x, GEN p, long prec);
GEN     fincke_pohst(GEN a, GEN borne, GEN stockmax, long flag, long prec, GEN (*check)(GEN));
GEN     kerint(GEN x);
GEN     kerint1(GEN x);
GEN     kerint2(GEN x);
GEN     lindep(GEN x, long prec);
GEN     lindep0(GEN x, long flag,long prec);
GEN     lindep2(GEN x, long bit);
GEN     lll(GEN x, long prec);
GEN     lll1(GEN x, long prec);
GEN     lllgen(GEN x);
GEN     lllgram(GEN x, long prec);
GEN     lllgram1(GEN x, long prec);
GEN     lllgramgen(GEN x);
GEN     lllgramint(GEN x);
GEN     lllgramintern(GEN x, long alpha, long flag, long prec);
GEN     lllgramkerim(GEN x);
GEN     lllgramkerimgen(GEN x);
GEN     lllint(GEN x);
GEN     lllintern(GEN x, long flag, long prec);
GEN     lllintpartial(GEN mat);
GEN     lllkerim(GEN x);
GEN     lllkerimgen(GEN x);
GEN     lllrat(GEN x);
GEN     matkerint0(GEN x,long flag);
GEN     minim(GEN a, GEN borne, GEN stockmax);
GEN     minim0(GEN a, GEN borne, GEN stockmax,long flag, long prec);
GEN     minim2(GEN a, GEN borne, GEN stockmax);
GEN     ordred(GEN x, long prec);
GEN     perf(GEN a);
GEN     polred(GEN x, long prec);
GEN     polred0(GEN x, long flag, GEN p, long prec);
GEN     polred2(GEN x, long prec);
GEN     polredabs(GEN x, long prec);
GEN     polredabs0(GEN x, long flag, long prec);
GEN     polredabs2(GEN x, long prec);
GEN     polredabsall(GEN x, long flun, long prec);
GEN     polredabsnored(GEN x, long prec);
GEN     qflll0(GEN x, long flag, long prec);
GEN     qflllgram0(GEN x, long flag, long prec);
GEN     smallpolred(GEN x, long prec);
GEN     smallpolred2(GEN x, long prec);

/* bibli2.c */

GEN     binome(GEN x, long k);
int     cmp_pol(GEN x, GEN y);
int     cmp_prime_ideal(GEN x, GEN y);
int     cmp_prime_over_p(GEN x, GEN y);
int     cmp_vecint(GEN x, GEN y);
GEN     convol(GEN x, GEN y);
GEN     cyclo(long n, long v);
GEN     dirdiv(GEN x, GEN y);
GEN     dirmul(GEN x, GEN y);
GEN     dirzetak(GEN nf, GEN b);
GEN     gen_sort(GEN x, int flag, int (*cmp)(GEN,GEN));
GEN     genrand(GEN N);
GEN     getheap(void);
long    getrand(void);
long    getstack(void);
long    gettime(void);
GEN     gprec(GEN x, long l);
GEN     gprec_w(GEN x, long pr);
GEN     grando0(GEN x, long n, long do_clone);
GEN     gtoset(GEN x);
GEN     indexlexsort(GEN x);
GEN     indexsort(GEN x);
GEN     laplace(GEN x);
GEN     legendre(long n, long v);
GEN     lexsort(GEN x);
GEN     mathilbert(long n);
GEN     matqpascal(long n, GEN q);
long    mymyrand(void);
int     pari_compare_int(int *a,int *b);
int     pari_compare_long(long *a,long *b);
GEN     permute(long n, GEN x);
GEN     permuteInv(GEN x);
GEN     polint(GEN xa, GEN ya, GEN x, GEN *dy);
GEN     polrecip(GEN x);
GEN     polymodrecip(GEN x);
GEN     setintersect(GEN x, GEN y);
long    setisset(GEN x);
GEN     setminus(GEN x, GEN y);
long    setrand(long seed);
long    setsearch(GEN x, GEN y, long flag);
GEN     setunion(GEN x, GEN y);
GEN     sindexlexsort(GEN x);
GEN     sindexsort(GEN x);
GEN     sort(GEN x);
long    tablesearch(GEN T, GEN x, int (*cmp)(GEN,GEN));
GEN     tayl(GEN x, long v, long precdl);
GEN     tchebi(long n, long v);
GEN     vecsort(GEN x, GEN k);
GEN     vecsort0(GEN x, GEN k, long flag);

/* buch1.c */

GEN     buchimag(GEN D, GEN gcbach, GEN gcbach2, GEN gCO);
GEN     buchreal(GEN D, GEN gsens, GEN gcbach, GEN gcbach2, GEN gRELSUP, long prec);
GEN     quadclassunit0(GEN x, long flag,GEN data, long prec);
GEN     quadhilbert(GEN D, GEN flag, long prec);
GEN     quadray(GEN bnf, GEN f, GEN flag, long prec);


/* buch2.c */

GEN     bnfclassunit0(GEN P,long flag,GEN data,long prec);
GEN     bnfinit0(GEN P,long flag,GEN data,long prec);
GEN     buchall(GEN P, GEN gcbach, GEN gcbach2, GEN gRELSUP, GEN gborne, long nbrelpid, long minsfb, long flun, long prec);
GEN     buchfu(GEN bignf);
GEN     classgrouponly(GEN P,GEN data,long prec);
GEN     isprincipal(GEN bignf, GEN x);
GEN     isprincipalall(GEN bignf, GEN x,long flall);
GEN     isprincipalforce(GEN bignf,GEN x);
GEN     isprincipalgen(GEN bignf, GEN x);
GEN     isprincipalgenforce(GEN bignf,GEN x);
GEN     isunit(GEN bignf, GEN x);
GEN     bnfmake(GEN sbnf,long prec);
GEN     regulator(GEN P,GEN data,long prec);
GEN     signunits(GEN bignf);
GEN     smallbuchinit(GEN pol,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,long minsfb,long prec);

/* buch3.c */

GEN     bnrclass0(GEN bignf, GEN ideal, long flag, long prec);
GEN     bnrconductor(GEN arg0,GEN arg1,GEN arg2,long all,long prec);
GEN     bnrconductorofchar(GEN bnr,GEN chi,long prec);
GEN     bnrdisc0(GEN arg0, GEN arg1, GEN arg2, long flag,long prec);
GEN     bnrdisclist0(GEN bnf,GEN borne, GEN arch, long all);
GEN     bnrinit0(GEN bignf,GEN ideal,long flag, long prec);
long    bnrisconductor(GEN arg0,GEN arg1,GEN arg2,long prec);
GEN     buchnarrow(GEN bignf);
GEN     buchray(GEN bignf,GEN ideal,long prec);
GEN     buchrayinit(GEN bignf,GEN ideal,long prec);
GEN     buchrayinitgen(GEN bignf,GEN ideal,long prec);
long    certifybuchall(GEN bnf);
GEN     conductor(GEN bnr,GEN subgroup,long all,long prec);
GEN     decodemodule(GEN nf, GEN fa);
GEN     discrayabs(GEN bnr,GEN subgroup,long prec);
GEN     discrayabscond(GEN bnr,GEN subgroup,long prec);
GEN     discrayabslist(GEN bnf,GEN listes);
GEN     discrayabslistarch(GEN bnf, GEN arch, long bound);
GEN     discrayabslistlong(GEN bnf, long bound);
GEN     discrayrel(GEN bnr,GEN subgroup,long prec);
GEN     discrayrelcond(GEN bnr,GEN subgroup,long prec);
GEN     isprincipalray(GEN bignf, GEN x);
GEN     isprincipalrayall(GEN bignf, GEN x,long flall);
GEN     isprincipalraygen(GEN bignf, GEN x);
GEN     rayclassno(GEN bignf,GEN ideal);
GEN     rayclassnolist(GEN bnf,GEN listes);
GEN     rnfconductor(GEN bnf, GEN polrel, long prec);
GEN     rnfkummer(GEN bnr, GEN subgroup, long all, long prec);
GEN     rnfnormgroup(GEN bnr, GEN polrel);
GEN     subgrouplist0(GEN bnr, long indexbound, long all, long prec);

/* buch4.c */

GEN     bnfisnorm(GEN bnf,GEN x,long flag,long PREC);
GEN     rnfisnorm(GEN bnf,GEN ext,GEN x,long flag,long PREC);
GEN     bnfissunit(GEN bnf,GEN suni,GEN x);
GEN     bnfsunit(GEN bnf,GEN s,long PREC);
long    nfhilbert(GEN bnf,GEN a,GEN b);
long    nfhilbert0(GEN bnf,GEN a,GEN b,GEN p);
long    nfhilbertp(GEN bnf,GEN a,GEN b,GEN p);
long    qpsoluble(GEN pol,GEN p);
long    qpsolublenf(GEN bnf,GEN pol,GEN p);
long    zpsoluble(GEN pol,GEN p);
long    zpsolublenf(GEN bnf,GEN pol,GEN p);

/* elliptic.c */

GEN     addell(GEN e, GEN z1, GEN z2);
GEN     akell(GEN e, GEN n);
GEN     anell(GEN e, long n);
GEN     apell(GEN e, GEN p);
GEN     apell2(GEN e, GEN p);
GEN     bilhell(GEN e, GEN z1, GEN z2, long prec);
GEN     coordch(GEN e, GEN ch);
GEN     ellap0(GEN e, GEN p, long flag);
GEN     elleisnum(GEN om, long k, long flag, long prec);
GEN     elleta(GEN om, long prec);
GEN     ellheight0(GEN e, GEN a, long flag,long prec);
GEN     ellinit0(GEN x,long flag,long prec);
long    ellrootno(GEN e, GEN p);
GEN     ellsigma(GEN om, GEN z, long flag, long prec);
GEN     elltors0(GEN e, long flag);
GEN     ellwp0(GEN e, GEN z, long flag, long prec, long PREC);
GEN     ellzeta(GEN om, GEN z, long prec);
GEN     ghell(GEN e, GEN a, long prec);
GEN     ghell2(GEN e, GEN a, long prec);
GEN     globalreduction(GEN e1);
GEN     initell(GEN x, long prec);
GEN     localreduction(GEN e, GEN p1);
GEN     lseriesell(GEN e, GEN s, GEN A, long prec);
GEN     mathell(GEN e, GEN x, long prec);
int     oncurve(GEN e, GEN z);
GEN     ordell(GEN e, GEN x, long prec);
GEN     orderell(GEN e, GEN p);
GEN     pointch(GEN x, GEN ch);
GEN     pointell(GEN e, GEN z, long prec);
GEN     powell(GEN e, GEN z, GEN n);
GEN     smallinitell(GEN x);
GEN     subell(GEN e, GEN z1, GEN z2);
GEN     taniyama(GEN e);
GEN     torsell(GEN e);
GEN     weipell(GEN e, long precdl);
GEN     zell(GEN e, GEN z, long prec);

/* es.c */

char*   GENtostr(GEN x);
void    brute(GEN g, char format, long dec);
void    bruteall(GEN g, char format, long dec, long flbl);
void    bruterr(GEN x,char format,long dec);
void    ecrire(GEN x, char format, long dec, long chmp);
const char* eng_ord(long i);
void    etatpile(unsigned int n);
char*   expand_tilde(char *s);
char*   filtre(char *s,int status);
void    flusherr(void);
void    fprintferr(char* pat, ...);
void    killallfiles(int check);
int     killfile(pariFILE *f);
GEN     lisGEN(FILE *f);
void    matbrute(GEN g, char format, long dec);
pariFILE* newfile(FILE *f, char *name, int type);
void    outbeaut(GEN x);
void    outbeauterr(GEN x);
void    outbrute(GEN x);
void    outerr(GEN x);
void    outmat(GEN x);
void    output(GEN x);
void    outsor(GEN x);
void    pari_fclose(pariFILE *f);
pariFILE*   pari_fopen(char *s, char *mode);
char*   pari_strdup(char *s);
char*   pari_unique_filename(char *s);
char*   pari_unique_filename(char *s);
void    pari_unlink(char *s);
void    pariflush(void);
void    pariputc(char c);
void    pariputs(char *s);
void    pariputsf(char *format, ...);
int     popinfile(void);
void    sor(GEN g, char fo, long dd, long chmp);
void    switchin(char *name);
void    switchout(char *name);
void    texe(GEN g, char format, long dec);
pariFILE* try_pipe(char *cmd, int flag);
char*   type_name(long t);
void    voir(GEN x, long nb);
void    vpariputs(char* format, va_list args);

/* galconj.c */

GEN     galoisconj(GEN nf);
GEN     galoisconj0(GEN nf,long flag, GEN d, long prec);
GEN     galoisconj2(GEN x, long nbmax, long prec);
GEN     galoisconj4(GEN T, GEN den, long flag);
GEN     galoisfixedfield(GEN gal, GEN v, GEN p);
GEN     galoisinit(GEN nf, GEN den);
GEN     galoispermtopol(GEN gal,GEN perm);
long    numberofconjugates(GEN T, long pdepart);
GEN     vandermondeinverse(GEN L, GEN T, GEN den);
/* gen1.c */

GEN     gadd(GEN x, GEN y);
GEN     gdiv(GEN x, GEN y);
GEN     gmul(GEN x, GEN y);
GEN     gsub(GEN x, GEN y);

/* gen2.c */
void    gop1z(GEN (*f)(GEN), GEN x, GEN y);
void    gop2z(GEN (*f)(GEN, GEN), GEN x, GEN y, GEN z);
GEN     gopgs2(GEN (*f)(GEN, GEN), GEN y, long s);
void    gops2gsz(GEN (*f)(GEN, long), GEN x, long s, GEN z);
void    gops2sgz(GEN (*f)(long, GEN), long s, GEN y, GEN z);
void    gops2ssz(GEN (*f)(long, long), long s, long y, GEN z);
GEN     gopsg2(GEN (*f)(GEN, GEN), long s, GEN y);
void    gopsg2z(GEN (*f)(GEN, GEN), long s, GEN y, GEN z);
long    opgs2(int (*f)(GEN, GEN), GEN y, long s);

GEN     brutcopy(GEN x, GEN y);
GEN     cgetp(GEN x);
GEN     co8(GEN x, long l);
GEN     cvtop(GEN x, GEN p, long l);
GEN     dummyclone(GEN x);
GEN     dummycopy(GEN x);
int     egalii(GEN x, GEN y);
GEN     forcecopy(GEN x);
GEN     from_Kronecker(GEN z, GEN pol);
GEN     gabs(GEN x, long prec);
void    gaffect(GEN x, GEN y);
void    gaffsg(long s, GEN x);
GEN     gclone(GEN x);
int     gcmp(GEN x, GEN y);
int     gcmp0(GEN x);
int     gcmp1(GEN x);
int     gcmp_1(GEN x);
GEN     gcopy(GEN x);
GEN     gcopy_i(GEN x, long lx);
GEN     gcvtop(GEN x, GEN p, long r);
int     gegal(GEN x, GEN y);
long    gexpo(GEN x);
long    ggval(GEN x, GEN p);
long    glength(GEN x);
GEN     gmax(GEN x, GEN y);
GEN     gmin(GEN x, GEN y);
GEN     gneg(GEN x);
GEN     gneg_i(GEN x);
GEN     greffe(GEN x, long l, long use_stack);
int     gsigne(GEN x);
long    gsize(GEN x);
GEN     gsqr(GEN x);
GEN     gtolist(GEN x);
long    gtolong(GEN x);
int     lexcmp(GEN x, GEN y);
GEN     listconcat(GEN list1, GEN list2);
GEN     listcreate(long n);
GEN     listinsert(GEN list, GEN object, long index);
void    listkill(GEN list);
GEN     listput(GEN list, GEN object, long index);
GEN     listsort(GEN list, long flag);
GEN     matsize(GEN x);
GEN     normalize(GEN x);
GEN     normalizepol(GEN x);
GEN     normalizepol_i(GEN x, long lx);
long    pvaluation(GEN x, GEN p, GEN *py);
long    svaluation(ulong x, ulong p, long *py);
GEN     realun(long prec);
GEN     realzero(long prec);
long    taille(GEN x);
long    taille2(GEN x);
GEN     vecmax(GEN x);
GEN     vecmin(GEN x);

/* gen3.c */

GEN     Mod0(GEN x, GEN y,long flag);
GEN     centerlift(GEN x);
GEN     centerlift0(GEN x,long v);
GEN     compo(GEN x, long n);
long    degree(GEN x);
GEN     denom(GEN x);
GEN     deriv(GEN x, long v);
GEN     derivpol(GEN x);
GEN     derivser(GEN x);
GEN     gand(GEN x, GEN y);
GEN     gceil(GEN x);
GEN     gcvtoi(GEN x, long *e);
GEN     gdivent(GEN x, GEN y);
GEN     gdiventres(GEN x, GEN y);
GEN     gdivgs(GEN x, long s);
GEN     gdivmod(GEN x, GEN y, GEN *pr);
GEN     gdivround(GEN x, GEN y);
GEN     geq(GEN x, GEN y);
GEN     geval(GEN x);
GEN     gfloor(GEN x);
GEN     gfrac(GEN x);
GEN     gge(GEN x, GEN y);
GEN     ggprecision(GEN x);
GEN     ggt(GEN x, GEN y);
GEN     gimag(GEN x);
GEN     ginv(GEN x);
GEN     gle(GEN x, GEN y);
GEN     glt(GEN x, GEN y);
GEN     gmod(GEN x, GEN y);
GEN     gmodulcp(GEN x,GEN y);
GEN     gmodulo(GEN x,GEN y);
GEN     gmodulsg(long x, GEN y);
GEN     gmodulss(long x, long y);
GEN     gmul2n(GEN x, long n);
GEN     gmulsg(long s, GEN y);
GEN     gne(GEN x, GEN y);
GEN     gnot(GEN x);
GEN     gor(GEN x, GEN y);
GEN     gpolvar(GEN y);
long    gprecision(GEN x);
GEN     gram_matrix(GEN M);
GEN     greal(GEN x);
GEN     grndtoi(GEN x, long *e);
GEN     ground(GEN x);
GEN     gshift(GEN x, long n);
GEN     gsubst(GEN x, long v, GEN y);
GEN     gtopoly(GEN x, long v);
GEN     gtopolyrev(GEN x, long v);
GEN     gtoser(GEN x, long v);
GEN     gtovec(GEN x);
GEN     gtrunc(GEN x);
int     gvar(GEN x);
int     gvar2(GEN x);
GEN     hqfeval(GEN q, GEN x);
GEN     integ(GEN x, long v);
int     iscomplex(GEN x);
int     isexactzero(GEN g);
int     isinexactreal(GEN x);
int     ismonome(GEN x);
GEN     lift(GEN x);
GEN     lift0(GEN x,long v);
GEN     lift_intern0(GEN x,long v);
GEN     mulmat_real(GEN x, GEN y);
GEN     numer(GEN x);
long    padicprec(GEN x, GEN p);
GEN     polcoeff0(GEN x,long n,long v);
long    poldegree(GEN x,long v);
GEN     poleval(GEN x, GEN y);
GEN     pollead(GEN x,long v);
long    precision(GEN x);
GEN     precision0(GEN x,long n);
GEN     qf_base_change(GEN q, GEN M, int flag);
GEN     qfeval(GEN q, GEN x);
GEN     recip(GEN x);
GEN     round0(GEN x, GEN *pte);
GEN     scalarpol(GEN x, long v);
GEN     scalarser(GEN x, long v, long prec);
GEN     simplify(GEN x);
GEN     truecoeff(GEN x, long n);
GEN     trunc0(GEN x, GEN *pte);
GEN     zeropol(long v);
GEN     zeroser(long v, long prec);

/* ifactor.c */
GEN     nextprime(GEN n);
GEN     precprime(GEN n);

/* init.c */

long       allocatemoremem(ulong newsize);
GEN        changevar(GEN x, GEN y);
void       checkmemory(GEN x);
void       disable_dbg(long val);
void       freeall(void);
GEN        gerepile(long ltop, long lbot, GEN q);
void       gerepilemany(long av, GEN* g[], long n);
void       gerepilemanycoeffs(long av, GEN x, long n);
void       gerepilemanysp(long av, long tetpil, GEN* g[], long n);
void       gerepilemanyvec(long av, long tetpil, long *g, long n);
GEN        gerepileupto(long av, GEN q);
GEN        gerepileuptoint(long av, GEN q);
GEN        gerepileuptoleaf(long av, GEN q);
char*      gpmalloc(size_t bytes);
char*      gprealloc(void *pointer,size_t newsize,size_t oldsize);
void       gunclone(GEN x);
void       killbloc(GEN x);
void       msgtimer(char *format, ...);
GEN        newbloc(long n);
void       pari_init(long parisize, long maxprime);
GEN        reorder(GEN x);
void       stackdummy(GEN x, long l);
stackzone* switch_stack(stackzone *z, long n);
long       timer(void);
long       timer2(void);

BEGINEXTERN
VOLATILE void err(long numerr, ...);
ENDEXTERN

/* mp.c ou mp.s */

int     absi_cmp(GEN x, GEN y);
int     absi_equal(GEN x, GEN y);
int     absr_cmp(GEN x, GEN y);
GEN     addii(GEN x, GEN y);
GEN     addir(GEN x, GEN y);
GEN     addrr(GEN x, GEN y);
GEN     addsi(long x, GEN y);
GEN     addsr(long x, GEN y);
GEN     addss(long x, long y);
void    affir(GEN x, GEN y);
void    affrr(GEN x, GEN y);
void    cgiv(GEN x);
int     cmpii(GEN x, GEN y);
int     cmprr(GEN x, GEN y);
int     cmpsi(long x, GEN y);
GEN     dbltor(double x);
void    diviiz(GEN x, GEN y, GEN z);
GEN     divir(GEN x, GEN y);
GEN     divis(GEN y, long x);
GEN     divri(GEN x, GEN y);
GEN     divrr(GEN x, GEN y);
GEN     divrs(GEN x, long y);
GEN     divsi(long x, GEN y);
GEN     divsr(long x, GEN y);
GEN     dvmdii(GEN x, GEN y, GEN *z);
int     invmod(GEN a, GEN b, GEN *res);
GEN     modii(GEN x, GEN y);
void    modiiz(GEN x, GEN y, GEN z);
GEN     modiu(GEN y, ulong x);
GEN     modsi(long x, GEN y);
GEN     modss(long x, long y);
GEN     modui(ulong x, GEN y);
void    mpdivz(GEN x, GEN y, GEN z);
GEN     mpent(GEN x);
GEN     mptrunc(GEN x);
GEN     mulii(GEN x, GEN y);
GEN     mulir(GEN x, GEN y);
GEN     mulrr(GEN x, GEN y);
GEN     mulsi(long x, GEN y);
GEN     mulsr(long x, GEN y);
GEN     mulss(long x, long y);
GEN     resss(long x, long y);
double  rtodbl(GEN x);
GEN     shifti(GEN x, long n);
long    smodsi(long x, GEN y);
GEN     sqri(GEN x);
GEN     truedvmdii(GEN x, GEN y, GEN *z);
long    vals(ulong x);

/* nffactor.c */

GEN     nffactor(GEN nf,GEN x);
GEN     nffactormod(GEN nf,GEN pol,GEN pr);
GEN     nfroots(GEN nf,GEN pol);
GEN     rnfcharpoly(GEN nf,GEN T,GEN alpha,int n);
GEN     rnfdedekind(GEN nf,GEN T,GEN pr);
GEN     unifpol(GEN nf,GEN pol,long flag);

/* polarit1.c */

GEN     apprgen(GEN f, GEN a);
GEN     apprgen9(GEN f, GEN a);
GEN     factcantor(GEN x, GEN p);
GEN     factmod(GEN f, GEN p);
GEN     factmod9(GEN f, GEN p, GEN a);
GEN     factormod0(GEN f, GEN p,long flag);
GEN     factorpadic0(GEN f,GEN p,long r,long flag);
GEN     factorpadic2(GEN x, GEN p, long r);
GEN     factorpadic4(GEN x, GEN p, long r);
GEN     factpol2(GEN x, long klim);
int     gdivise(GEN x, GEN y);
GEN     gred(GEN x);
GEN     gred_rfrac(GEN x);
GEN     incloop(GEN a);
int     poldivis(GEN x, GEN y, GEN *z);
GEN     poldivres(GEN x, GEN y, GEN *pr);
GEN     rootmod(GEN f, GEN p);
GEN     rootmod0(GEN f, GEN p,long flag);
GEN     rootmod2(GEN f, GEN p);
GEN     rootpadic(GEN f, GEN p, long r);
GEN     rootpadicfast(GEN f, GEN p, long r, long flall);
GEN     roots2(GEN pol,long PREC);
GEN     rootsold(GEN x, long l);
GEN     setloop(GEN a);
GEN     simplefactmod(GEN f, GEN p);

/* polarit2.c */

GEN     bezoutpol(GEN a, GEN b, GEN *u, GEN *v);
GEN     centermod(GEN x, GEN p);
GEN     content(GEN x);
GEN     discsr(GEN x);
GEN     divide_conquer_prod(GEN x, GEN (*mul)(GEN,GEN));
GEN     factor(GEN x);
GEN     factor0(GEN x,long flag);
GEN     factorback(GEN fa,GEN nf);
GEN     factpol(GEN x, long klim, long hint);
GEN     gbezout(GEN x, GEN y, GEN *u, GEN *v);
GEN     gcd0(GEN x, GEN y,long flag);
GEN     gdivexact(GEN x, GEN y);
GEN     ggcd(GEN x, GEN y);
GEN     ginvmod(GEN x, GEN y);
GEN     gisirreducible(GEN x);
GEN     glcm(GEN x, GEN y);
GEN     newtonpoly(GEN x, GEN p);
GEN     nfisincl(GEN a, GEN b);
GEN     nfisisom(GEN a, GEN b);
GEN     poldisc0(GEN x, long v);
GEN     polfnf(GEN a, GEN t);
GEN     polresultant0(GEN x, GEN y,long v,long flag);
GEN     polsym(GEN x, long n);
GEN     quadgen(GEN x);
GEN     quadpoly(GEN x);
GEN     quadpoly0(GEN x, long v);
GEN     reduceddiscsmith(GEN pol);
GEN     resultant2(GEN x, GEN y);
GEN     resultantducos(GEN x, GEN y);
GEN     sort_factor(GEN y, int (*cmp)(GEN,GEN));
GEN     srgcd(GEN x, GEN y);
long    sturmpart(GEN x, GEN a, GEN b);
GEN     subresall(GEN u, GEN v, GEN *sol);
GEN     subresext(GEN x, GEN y, GEN *U, GEN *V);
GEN     sylvestermatrix(GEN x,GEN y);
GEN     vecbezout(GEN x, GEN y);
GEN     vecbezoutres(GEN x, GEN y);

/* polarit3.c */

GEN     Fp_pol(GEN z, GEN p);
GEN     Fp_pol_extgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv);
GEN     Fp_pol_gcd(GEN x, GEN y, GEN p);
GEN     Fp_pol_red(GEN z, GEN p);
GEN     Fp_pol_small(GEN z, GEN p, long l);
GEN     Fp_poldivres(GEN x, GEN y, GEN p, GEN *pr);
GEN     Fp_pow_mod_pol(GEN x, GEN n, GEN pol, GEN p);
GEN     Fp_vec(GEN z, GEN p);
GEN     Fp_vec_red(GEN z, GEN p);
GEN     modulargcd(GEN a,GEN b);
GEN     normalize_mod_p(GEN z, GEN p);
GEN     quickmul(GEN a, GEN b, long na, long nb);
GEN     quicksqr(GEN a, long na);
GEN     small_to_pol(GEN z, long l, long p);
GEN     stopoly(long m, long p, long v);
GEN     stopoly_gen(GEN m, GEN p, long v);

/* rootpol.c */

int     isrealappr(GEN x, long l);
GEN     roots(GEN x,long l);
GEN     roots0(GEN x,long flag,long l);

/* subfields.c */

GEN     ffinit(GEN p,long n, long v);
GEN     subfields(GEN nf,GEN d);
GEN     subfields0(GEN nf,GEN d);
GEN     conjugates(GEN pol);

/* subgroup.c */

void    forsubgroup(entree *oep, GEN cyc, long bound, char *och);
GEN     subgrouplist(GEN cyc, long bound);

/* stark.c */

GEN     bnrL1(GEN bnr, long flag, long prec);
GEN     bnrrootnumber(GEN bnr, GEN chi, long flag, long prec);
GEN     bnrstark(GEN bnr, GEN subgroup, long flag, long prec);

/* sumiter.c */

GEN     direuler(entree *ep, GEN a, GEN b, char *ch);
GEN     divsum(GEN num,entree *ep, char *ch);
void    fordiv(GEN a, entree *ep, char *ch);
void    forpari(entree *ep, GEN a, GEN b, char *ch);
void    forprime(entree *ep, GEN a, GEN b, char *ch);
void    forstep(entree *ep, GEN a, GEN b, GEN s, char *ch);
void    forvec(entree *ep, GEN x, char *ch, long flag);
GEN     intnum0(entree *ep, GEN a, GEN b, char *ch,long flag,long prec);
GEN     matrice(GEN nlig, GEN ncol,entree *ep1, entree *ep2, char *ch);
GEN     polzag(long n, long m);
GEN     polzagreel(long n, long m, long prec);
GEN     prodeuler(entree *ep, GEN a, GEN b, char *ch, long prec);
GEN     prodinf(entree *ep, GEN a, char *ch, long prec);
GEN     prodinf0(entree *ep, GEN a, char *ch, long flag, long prec);
GEN     prodinf1(entree *ep, GEN a, char *ch, long prec);
GEN     produit(entree *ep, GEN a, GEN b, char *ch, GEN x);
GEN     qromb(entree *ep, GEN a, GEN b, char *ch, long prec);
GEN     qromi(entree *ep, GEN a, GEN b, char *ch, long prec);
GEN     qromo(entree *ep, GEN a, GEN b, char *ch, long prec);
GEN     rombint(entree *ep, GEN a, GEN b, char *ch, long prec);
GEN     somme(entree *ep, GEN a, GEN b, char *ch, GEN x);
GEN     sumalt(entree *ep, GEN a, char *ch, long prec);
GEN     sumalt0(entree *ep, GEN a, char *ch,long flag, long prec);
GEN     sumalt2(entree *ep, GEN a, char *ch, long prec);
GEN     sumpos(entree *ep, GEN a, char *ch, long prec);
GEN     sumpos0(entree *ep, GEN a, char *ch, long flag,long prec);
GEN     sumpos2(entree *ep, GEN a, char *ch, long prec);
GEN     suminf(entree *ep, GEN a, char *ch, long prec);
GEN     vecteur(GEN nmax, entree *ep, char *ch);
GEN     vvecteur(GEN nmax, entree *ep, char *ch);
GEN     zbrent(entree *ep, GEN a, GEN b, char *ch, long prec);

/* thue.c */

GEN     bnfisintnorm(GEN x, GEN y);
GEN     thue(GEN thueres, GEN rhs, GEN ne);
GEN     thueinit(GEN poly, long flag, long prec);

/* trans1.c */

void    consteuler(long prec);
void    constpi(long prec);
GEN     gcos(GEN x, long prec);
void    gcosz(GEN x, GEN y);
GEN     gcotan(GEN x, long prec);
GEN     gexp(GEN x, long prec);
void    gexpz(GEN x, GEN y);
GEN     glog(GEN x, long prec);
void    glogz(GEN x, GEN y);
GEN     gpow(GEN x, GEN n, long prec);
GEN     gpowgs(GEN x, long n);
GEN     gsin(GEN x, long prec);
void    gsincos(GEN x, GEN *s, GEN *c, long prec);
void    gsinz(GEN x, GEN y);
GEN     gsqrt(GEN x, long prec);
void    gsqrtz(GEN x, GEN y);
GEN     gtan(GEN x, long prec);
void    gtanz(GEN x, GEN y);
GEN     log0(GEN x,long flag, long prec);
GEN     mpeuler(long prec);
GEN     mpexp(GEN x);
GEN     mpexp1(GEN x);
GEN     mplog(GEN x);
GEN     mppi(long prec);
GEN     mpsqrt(GEN x);
GEN     palog(GEN x);
GEN     powgi(GEN x, GEN n);
GEN     teich(GEN x);
GEN     transc(GEN (*f) (GEN, long), GEN x, long prec);

/* trans2.c */

GEN     bernfrac(long n);
GEN     bernreal(long n, long prec);
GEN     bernvec(long nomb);
GEN     gach(GEN x, long prec);
void    gachz(GEN x, GEN y);
GEN     gacos(GEN x, long prec);
void    gacosz(GEN x, GEN y);
GEN     garg(GEN x, long prec);
GEN     gash(GEN x, long prec);
void    gashz(GEN x, GEN y);
GEN     gasin(GEN x, long prec);
void    gasinz(GEN x, GEN y);
GEN     gatan(GEN x, long prec);
void    gatanz(GEN x, GEN y);
GEN     gath(GEN x, long prec);
void    gathz(GEN x, GEN y);
GEN     gch(GEN x, long prec);
void    gchz(GEN x, GEN y);
GEN     ggamd(GEN x, long prec);
void    ggamdz(GEN x, GEN y);
GEN     ggamma(GEN x, long prec);
void    ggammaz(GEN x, GEN y);
GEN     glngamma(GEN x, long prec);
void    glngammaz(GEN x, GEN y);
GEN     gpsi(GEN x, long prec);
void    gpsiz(GEN x, GEN y);
GEN     gsh(GEN x, long prec);
void    gshz(GEN x, GEN y);
GEN     gth(GEN x, long prec);
void    gthz(GEN x, GEN y);
void    mpbern(long nomb, long prec);
void    mpgamdz(long s, GEN y);

/* trans3.c */

GEN     agm(GEN x, GEN y, long prec);
GEN     dilog(GEN x, long prec);
GEN     eint1(GEN x, long prec);
GEN     eta(GEN x, long prec);
GEN     eta0(GEN x, long flag,long prec);
GEN     gerfc(GEN x, long prec);
GEN     glogagm(GEN x, long prec);
GEN     gpolylog(long m, GEN x, long prec);
void    gpolylogz(long m, GEN x, GEN y);
GEN     gzeta(GEN x, long prec);
void    gzetaz(GEN x, GEN y);
GEN     hyperu(GEN a, GEN b, GEN gx, long prec);
GEN     incgam(GEN a, GEN x, long prec);
GEN     incgam0(GEN a, GEN x, GEN z,long prec);
GEN     incgam1(GEN a, GEN x, long prec);
GEN     incgam2(GEN a, GEN x, long prec);
GEN     incgam3(GEN a, GEN x, long prec);
GEN     incgam4(GEN a, GEN x, GEN z, long prec);
GEN     jbesselh(GEN n, GEN z, long prec);
GEN     jell(GEN x, long prec);
GEN     kbessel(GEN nu, GEN gx, long prec);
GEN     kbessel0(GEN nu, GEN gx, long flag,long prec);
GEN     kbessel2(GEN nu, GEN x, long prec);
GEN     logagm(GEN q);
GEN     polylog(long m, GEN x, long prec);
GEN     polylog0(long m, GEN x, long flag, long prec);
GEN     polylogd(long m, GEN x, long prec);
GEN     polylogdold(long m, GEN x, long prec);
GEN     polylogp(long m, GEN x, long prec);
GEN     theta(GEN q, GEN z, long prec);
GEN     thetanullk(GEN q, long k, long prec);
GEN     trueeta(GEN x, long prec);
GEN     veceint1(GEN nmax, GEN C, long prec);
GEN     weber0(GEN x, long flag,long prec);
GEN     wf(GEN x, long prec);
GEN     wf2(GEN x, long prec);
