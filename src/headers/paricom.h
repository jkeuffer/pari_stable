/******************************************************************/
/******************************************************************/
/*                                                                */
/*                       Fichier Include PARI                     */
/*                   commun a toutes les versions                 */
/*                                                                */
/******************************************************************/
/******************************************************************/
/* $Id$ */

#define bit_accuracy(x) (((x)-2) << TWOPOTBITS_IN_LONG)

#define GSTR(x) ((char*) (((GEN) (x)) + 1 ))

/* For compatibility with 1.x.x */
#define err pari_err /* move to e.g paritr.h ? */
#define init pari_init
#define gen2str GENtostr
#define gpui gpow
#define gpuigs gpowgs
#define classno3 hclassno
#define strtoGEN flisexpr

#define rcopy mpcopy
#define absr  mpabs
#define absi  mpabs
#define negi  mpneg
#define negr  mpneg
#define mpnegz(x,y)      {long av=avma;mpaff(mpneg(x),y);avma=av;}
#define mpabsz(x,y)      {long av=avma;mpaff(mpabs(x),y);avma=av;}
#define absrz(x,z)       mpabsz((x),(z))
#define negrz(x,z)       mpnegz((x),(z))

/* Common global variables: */

extern PariOUT *pariOut, *pariErr;
extern FILE    *pari_outfile, *logfile, *infile, *errfile;

extern long  DEBUGFILES, DEBUGLEVEL, DEBUGMEM, precdl;
extern long  *ordvar;
extern GEN   bernzone,gpi,geuler;
extern GEN   polvar,*polun,*polx,primetab;
extern GEN   gun,gdeux,ghalf,gi,gzero;

extern const long lontyp[];

#define NUMPRTBELT     100 /* taille table de premiers prives */
#define MAXITERPOL     10  /* nombre maximum de doublement de precision
			      dans les operations de type polredabs */

                                                /* let SL = sizeof(long) */
#define pariK  (9.632959862*(BYTES_IN_LONG/4))  /* SL*log(2)/log(10)     */
#define pariK1 (0.103810253/(BYTES_IN_LONG/4))  /* log(10)/(SL*log(2))   */
#define pariK2 (1.1239968)                      /* 1/(1-(log(2)/(2*pi))) */
#define pariK4 (17.079468445347/BITS_IN_LONG)   /* 2*e*pi/SL             */
#define LOG2   (0.69314718055994531)            /* log(2)                */
#define L2SL10 (0.301029995663981)              /* log(2)/log(10)        */
#define pariC1 (0.9189385332)                   /* log(2*pi)/2           */
#define pariC2 (22.18070978*(BYTES_IN_LONG/4))  /* SL*log(2)             */
#define pariC3 (0.0216950598/(BYTES_IN_LONG/4)) /* log((1+sqrt(5))/2)/C2 */

#ifndef  PI
#  define PI (3.141592653589)
#endif

#ifdef LONG_IS_64BIT
#  define VERYBIGINT (9223372036854775807L) /* 2^63-1 */
#  define EXP220 (1099511627776L)          /* 2^40   */
#  define BIGINT (2147483647)              /* 2^31-1 */
#else
#  define VERYBIGINT (2147483647L) /* 2^31-1 */
#  define EXP220 (1048576L)       /* 2^20   */
#  define BIGINT (32767)          /* 2^15-1 */
#endif

#ifdef NOEXP2
#  ifdef __cplusplus
     inline double exp2(double x) {return exp(x*LOG2);}
     inline double log2(double x) {return log(x)/LOG2;}
#  else
#    define exp2(x) (exp((double)(x)*LOG2))
#    ifndef __CYGWIN32__
#      define log2(x) (log((double)(x))/LOG2)
#    endif
#  endif
#else
  BEGINEXTERN
    double exp2(double);
    double log2(double);
  ENDEXTERN
#endif

#ifndef LONG_IS_64BIT
#  undef labs
#  define labs(x) abs(x)
#endif

#ifdef min
#  undef min
#endif
#ifdef max
#  undef max
#endif
#define min(a,b) ((a)>(b)?(b):(a))
#define max(a,b) ((a)>(b)?(a):(b))

#define gval(x,v) (ggval((x),polx[v]))
#define gvar9(x) ((typ(x)==t_POLMOD)? gvar2(x): gvar(x))

#define ggrando(x,n) (grando0((x),(n),1))
#define ggrandocp(x,n) (grando0((x),(n),0))

#define addis(x,s)  (addsi((s),(x)))
#define addrs(x,s)  (addsr((s),(x)))
#define mulis(x,s)  (mulsi((s),(x)))
#define muliu(x,s)  (mului((s),(x)))
#define mulri(x,s)  (mulir((s),(x)))
#define mulrs(x,s)  (mulsr((s),(x)))
#define gmulgs(y,s) (gmulsg((s),(y)))
#define lmulgs(y,s) ((long)gmulsg((s),(y)))

#define mpmodz(x,y,z) (modiiz((x),(y),(z)))
#define mpresz(x,y,z) (resiiz((x),(y),(z)))
#define mpmod(x,y)    (modii((x),(y)))
#define mpres(x,y)    (resii((x),(y)))

#define laddgs(y,s)    (lopsg2(gadd,(s),(y)))
#define laddsg(s,y)    (lopsg2(gadd,(s),(y)))
#define ldiventgs(y,s) (lopgs2(gdivent,(y),(s)))
#define ldiventsg(s,y) (lopsg2(gdivent,(s),(y)))
#define ldivsg(s,y)    (lopsg2(gdiv,(s),(y)))
#define lmaxgs(y,s)    (lopgs2(gmax,(y),(s)))
#define lmaxsg(s,y)    (lopsg2(gmax,(s),(y)))
#define lmings(y,s)    (lopgs2(gmin,(y),(s)))
#define lminsg(s,y)    (lopsg2(gmin,(s),(y)))
#define lmodgs(y,s)    (lopgs2(gmod,(y),(s)))
#define lmodsg(s,y)    (lopsg2(gmod,(s),(y)))
#define lsubgs(y,s)    (lopgs2(gsub,(y),(s)))
#define lsubsg(s,y)    (lopsg2(gsub,(s),(y)))

#define mppiz(x)       (gop0z(mppi,(x)))
#define mpeulerz(x)    (gop0z(mpeuler,(x)))

#define autz(x,y)      (gop1z(mpaut,(x),(y)))
#define mpsqrtz(x,y)   (gop1z(mpsqrt,(x),(y)))
#define mpexpz(x,y)    (gop1z(mpexp,(x),(y)))
#define mpexp1z(x,y)   (gop1z(mpexp1,(x),(y)))
#define mplogz(x,y)    (gop1z(mplog,(x),(y)))
#define mpcosz(x,y)    (gop1z(mpcos,(x),(y)))
#define mpsinz(x,y)    (gop1z(mpsin,(x),(y)))
#define mptanz(x,y)    (gop1z(mptan,(x),(y)))
#define mpatanz(x,y)   (gop1z(mpatan,(x),(y)))
#define mpasinz(x,y)   (gop1z(mpasin,(x),(y)))
#define mpacosz(x,y)   (gop1z(mpacos,(x),(y)))
#define mpchz(x,y)     (gop1z(mpch,(x),(y)))
#define mpshz(x,y)     (gop1z(mpsh,(x),(y)))
#define mpthz(x,y)     (gop1z(mpth,(x),(y)))
#define mpathz(x,y)    (gop1z(mpath,(x),(y)))
#define mpashz(x,y)    (gop1z(mpash,(x),(y)))
#define mpachz(x,y)    (gop1z(mpach,(x),(y)))
#define mpgammaz(x,y)  (gop1z(mpgamma,(x),(y)))
#define gredz(x,y)     (gop1z(gred,(x),(y)))
#define gnegz(x,y)     (gop1z(gneg,(x),(y)))

#define mpargz(x,y,z)   (gop2z(mparg,(x),(y),(z)))
#define gabsz(x,prec,y) (gop2z(gabs,(x),(prec),(y)))
#define gmaxz(x,y,z)    (gop2z(gmax,(x),(y),(z)))
#define gminz(x,y,z)    (gop2z(gmin,(x),(y),(z)))
#define gaddz(x,y,z)    (gop2z(gadd,(x),(y),(z)))
#define gsubz(x,y,z)    (gop2z(gsub,(x),(y),(z)))
#define gmulz(x,y,z)    (gop2z(gmul,(x),(y),(z)))
#define gdivz(x,y,z)    (gop2z(gdiv,(x),(y),(z)))
#define gdiventz(x,y,z) (gop2z(gdivent,(x),(y),(z)))
#define gmodz(x,y,z)    (gop2z(gmod,(x),(y),(z)))

#define gaddgs(y,s)     (gopsg2(gadd,(s),(y)))
#define gaddsg(s,y)     (gopsg2(gadd,(s),(y)))
#define gaddsmat(s,y)   (gopsg2(gaddmat,(s),(y)))
#define gdiventsg(s,y)  (gopsg2(gdivent,(s),(y)))
#define gdivsg(s,y)     (gopsg2(gdiv,(s),(y)))
#define gmaxsg(s,y)     (gopsg2(gmax,(s),(y)))
#define gminsg(s,y)     (gopsg2(gmin,(s),(y)))
#define gmodsg(s,y)     (gopsg2(gmod,(s),(y)))
#define gsubsg(s,y)     (gopsg2(gsub,(s),(y)))

#define gdiventgs(y,s)  (gopgs2(gdivent,(y),(s)))
#define gmaxgs(y,s)     (gopgs2(gmax,(y),(s)))
#define gmings(y,s)     (gopgs2(gmin,(y),(s)))
#define gmodgs(y,s)     (gopgs2(gmod,(y),(s)))
#define gsubgs(y,s)     (gopgs2(gsub,(y),(s)))

#define gcmpsg(s,y)     (-opgs2(gcmp,(y),(s)))
#define gcmpgs(y,s)     (opgs2(gcmp,(y),(s)))
#define gegalsg(s,y)    (opgs2(gegal,(y),(s)))
#define gegalgs(y,s)    (opgs2(gegal,(y),(s)))

#define gaddgsz(y,s,z)    (gopsg2z(gadd,(s),(y),(z)))
#define gaddsgz(s,y,z)    (gopsg2z(gadd,(s),(y),(z)))
#define gdiventsgz(s,y,z) (gopsg2z(gdivent,(s),y),(z)))
#define gdivsgz(s,y,z)    (gopsg2z(gdiv,(s),(y),(z)))
#define gmaxsgz(s,y,z)    (gopsg2z(gmax,(s),(y),(z)))
#define gminsgz(s,y,z)    (gopsg2z(gmin,(s),(y),(z)))
#define gmodsgz(s,y,z)    (gopsg2z(gmod,(s),(y),(z)))
#define gsubsgz(s,y,z)    (gopsg2z(gsub,(s),(y),(z)))

#define gdiventgsz(y,s,z) (gopgs2z(gdivent,(y),(s),(z)))
#define gmaxgsz(y,s,z)    (gopgs2z(gmax,(y),(s),(z)))
#define gmingsz(y,s,z)    (gopgs2z(gmin,(y),(s),(z)))
#define gmodgsz(y,s,z)    (gopgs2z(gmod,(y),(s),(z)))
#define gsubgsz(y,s,z)    (gopgs2z(gsub,(y),(s),(z)))

#define gdivgsz(y,s,z)  (gops2gsz(gdivgs,(y),(s),(z)))
#define gmul2nz(x,s,z)  (gops2gsz(gmul2n,(x),(s),(z)))
#define gmulgsz(y,s,z)  (gops2sgz(gmulsg,(s),(y),(z)))
#define gmulsgz(s,y,z)  (gops2sgz(gmulsg,(s),(y),(z)))
#define gshiftz(x,s,z)  (gops2gsz(gshift,(x),(s),(z)))

#define bern(i)       (bernzone + 3 + (i)*bernzone[2])

/* works only for POSITIVE integers */
#define mod64(x)  (((x)[lgefint(x)-1]) & 63)
#define mod32(x)  (((x)[lgefint(x)-1]) & 31)
#define mod16(x)  (((x)[lgefint(x)-1]) & 15)
#define mod8(x)   (((x)[lgefint(x)-1]) & 7)
#define mod4(x)   (((x)[lgefint(x)-1]) & 3)
#define mod2(x)   (((x)[lgefint(x)-1]) & 1)
#define is_pm1(n)    ((lgefint(n)==3) && (((GEN)(n))[2]==1))
#define is_bigint(n) ((lgefint(n)>3) || \
		      ((lgefint(n)==3) && ((((GEN)(n))[2]) < 0)))

#define leading_term(x) ((GEN)(((GEN)(x))[lgef(x)-1]))

#ifdef __cplusplus
   inline int odd(long x) {return x&1;}
#else
#  define odd(x) ((x) & 1)
#endif

#define mpodd(x) (signe(x) && mod2(x))

#define ONLY_REM ((GEN*)0x1)
#define ONLY_DIVIDES ((GEN*)0x2)
#define ONLY_DIVIDES_EXACT ((GEN*)0x3)
#define gdeuc(x,y) (poldivres((x),(y),NULL))
#define gres(x,y) (poldivres((x),(y),ONLY_REM))
#define Fp_deuc(x,y,p) (Fp_poldivres((x),(y),(p), NULL))
#define Fp_res(x,y,p) (Fp_poldivres((x),(y),(p), ONLY_REM))
#define matpascal(n) matqpascal((n),NULL)
#define sturm(x) (sturmpart((x),NULL,NULL))
#define carreparfait(x) (carrecomplet((x),NULL))
#define subres(x,y) (subresall((x),(y),NULL))
/* #define subres(x,y) (resultantducos((x),(y))) */

#define leadingcoeff(x) (pollead((x),-1))
#define lift_intern(x) (lift_intern0((x),-1))

#define idealmullll(nf,x,y) (idealoplll(idealmul,(nf),(x),(y)))
#define idealdivlll(nf,x,y) (idealoplll(idealdiv,(nf),(x),(y)))

#define invmat(a) (gauss((a),NULL))

#define element_divmodideal(nf,x,y,ideal) (\
  nfreducemodideal((nf),\
    element_mul((nf),(x),element_invmodideal((nf),(y),(ideal)))\
    ,(ideal)\
  )\
)
#define element_mulmodideal(nf,x,y,ideal) (\
  nfreducemodideal((nf),element_mul((nf),(x),(y)),(ideal))\
)
#define element_mulmodidele(nf,x,y,idele,structarch) (\
  nfreducemodidele((nf),element_mul((nf),(x),(y)),(idele),(structarch))\
)
#define element_mulmodpr(nf,x,y,prhall) (\
  nfreducemodpr((nf),element_mul((nf),(x),(y)),(prhall))\
)
#define element_sqrmodideal(nf,x,ideal) (\
  nfreducemodideal((nf),element_sqr((nf),(x)),(ideal))\
)
#define element_sqrmodidele(nf,x,idele,structarch) (\
  nfreducemodidele((nf),element_sqr((nf),(x)),(idele),(structarch))\
)
#define element_sqrmodpr(nf,x,prhall) (\
  nfreducemodpr((nf),element_sqr((nf),(x)),(prhall))\
)
#define idealmulmodideal(nf,x,y,ideal,prec) (\
  ideallllredmodideal((nf),idealmullll((nf),(x),(y)),(ideal),(prec))\
)
#define idealsqrmodideal(nf,x,ideal,prec) (\
  ideallllredmodideal((nf),idealsqrlll((nf),(x)),(ideal),(prec))\
)

#define buchgen(P,gcbach,gcbach2,prec) (\
  buchall((P),(gcbach),(gcbach2),stoi(5),gzero,4,3,0,(prec))\
)
#define buchgenfu(P,gcbach,gcbach2,prec) (\
  buchall((P),(gcbach),(gcbach2),stoi(5),gzero,4,3,2,(prec))\
)
#define buchinit(P,gcbach,gcbach2,prec) (\
  buchall((P),(gcbach),(gcbach2),stoi(5),gzero,4,3,-1,(prec))\
)
#define buchinitfu(P,gcbach,gcbach2,prec) (\
  buchall((P),(gcbach),(gcbach2),stoi(5),gzero,4,3,-2,(prec))\
)

/* output of get_nf and get_bnf */
#define typ_NULL 0
#define typ_POL  1
#define typ_Q    2
#define typ_NF   3
#define typ_BNF  4
#define typ_BNR  5
#define typ_CLA  6 /* bnfclassunit   */
#define typ_ELL  7 /* elliptic curve */
#define typ_QUA  8 /* quadclassunit  */

/* for gen_sort */
#define cmp_IND 1
#define cmp_LEX 2
#define cmp_C   4
