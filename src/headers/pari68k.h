/*******************************************************************/
/*******************************************************************/
/*                                                                 */
/*                        Fichier Include PARI                     */
/*                   declarations specifiques 680x0                */
/*                                                                 */
/*******************************************************************/
/*******************************************************************/
/* $Id$ */

BEGINEXTERN
  void  addiiz(GEN x, GEN y, GEN z);
  void  addirz(GEN x, GEN y, GEN z);
  void  addriz(GEN x, GEN y, GEN z);
  void  addrrz(GEN x, GEN y, GEN z);
  void  addsii(long x, GEN y, GEN z);
  void  addsiz(long x, GEN y, GEN z);
  void  addsrz(long x, GEN y, GEN z);
  void  addssz(long x, long y, GEN z);
  void  affii(GEN x, GEN y);
  void  affri(GEN x, GEN y);
  void  affrs(GEN x, long y);
  void  affsi(long s, GEN x);
  void  affsr(long s, GEN x);
  void  affsz(long x, GEN y);
  GEN   cgetg(long x, long y);
  GEN   cgeti(long x);
  GEN   cgetr(long x);
  int   cmpir(GEN x, GEN y);
  int   cmpis(GEN x, long y);
  int   cmpri(GEN x, GEN y);
  int   cmprs(GEN x, long y);
  int   cmpsr(long x, GEN y);
  GEN   divii(GEN x, GEN y);
  void  divirz(GEN x, GEN y, GEN z);
  int   divise(GEN x, GEN y);
  long  divisii(GEN x, long y, GEN z);
  void  divisz(GEN x, long y, GEN z);
  void  divriz(GEN x, GEN y, GEN z);
  void  divrrz(GEN x, GEN y, GEN z);
  void  divrsz(GEN x, long y, GEN z);
  void  divsiz(long x, GEN y, GEN z);
  void  divsrz(long x, GEN y, GEN z);
  void  divssz(long x, long y, GEN z);
  void  dvmdiiz(GEN x, GEN y, GEN z, GEN t);
  GEN   dvmdis(GEN x, long y, GEN *z);
  void  dvmdisz(GEN x, long y, GEN z, GEN t);
  GEN   dvmdsi(long x, GEN y, GEN *z);
  void  dvmdsiz(long x, GEN y, GEN z, GEN t);
  void  dvmdssz(long x, long y, GEN z, GEN t);
  long  itos(GEN x);
  GEN   modis(GEN x, long y);
  void  modisz(GEN x, long y, GEN z);
  void  modssz(long x, long y, GEN z);
  GEN   mpadd(GEN x, GEN y);
  void  mpaddz(GEN x, GEN y, GEN z);
  void  mpaff(GEN x, GEN y);
  int   mpcmp(GEN x, GEN y);
  GEN   mpdiv(GEN x, GEN y);
  int   mpdivis(GEN x, GEN y, GEN z);
  void  mpdvmdz(GEN x, GEN y, GEN z, GEN *r);
  void  mpentz(GEN x, GEN y);
  void  mpinvir(GEN x, GEN y);
  void  mpinvrr(GEN x, GEN y);
  void  mpinvsr(long x, GEN y);
  void  mpinvz(GEN x, GEN z);
  GEN   mpmul(GEN x, GEN y);
  void  mpmulz(GEN x, GEN y, GEN z);
  GEN   mpshift(GEN x, long y);
  void  mpshiftz(GEN x, long y, GEN z);
  GEN   mpsub(GEN x, GEN y);
  void  mpsubz(GEN x, GEN y, GEN z);
  void  mptruncz(GEN x, GEN y);
  GEN   mulii(GEN x, GEN y);
  void  muliiz(GEN x, GEN y, GEN z);
  void  mulirz(GEN x, GEN y, GEN z);
  void  mulriz(GEN x, GEN y, GEN z);
  void  mulrrz(GEN x, GEN y, GEN z);
  void  mulsii(long x, GEN y, GEN z);
  void  mulsiz(long x, GEN y, GEN z);
  void  mulsrz(long x, GEN y, GEN z);
  void  mulssz(long x, long y, GEN z);
  GEN   resii(GEN x, GEN y);
  void  resiiz(GEN x, GEN y, GEN z);
  GEN   resis(GEN x, long y);
  void  resisz(GEN x, long y, GEN z);
  GEN   ressi(long x, GEN y);
  void  ressiz(long x, GEN y, GEN z);
  void  resssz(long x, long y, GEN z);
  GEN   shiftr(GEN x, long n);
  GEN   shifts(long x, long y);
  GEN   stoi(long x);
  GEN   subii(GEN x, GEN y);
  void  subiiz(GEN x, GEN y, GEN z);
  GEN   subir(GEN x, GEN y);
  void  subirz(GEN x, GEN y, GEN z);
  GEN   subis(GEN x, long y);
  void  subisz(GEN x, long y, GEN z);
  GEN   subri(GEN x, GEN y);
  void  subriz(GEN x, GEN y, GEN z);
  GEN   subrr(GEN x, GEN y);
  void  subrrz(GEN x, GEN y, GEN z);
  GEN   subrs(GEN x, long y);
  void  subrsz(GEN x, long y, GEN z);
  GEN   subsi(long x, GEN y);
  void  subsiz(long x, GEN y, GEN z);
  GEN   subsr(long x, GEN y);
  void  subsrz(long x, GEN y, GEN z);
  void  subssz(long x, long y, GEN z);
  long  vali(GEN x);
ENDEXTERN
