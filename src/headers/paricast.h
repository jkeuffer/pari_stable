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

#ifdef lround /* in some Mac header */
#  undef lround
#endif

#define mael(ma,x1,x2) ( ((GEN) ((GEN)(ma))[x1]) [x2])
#define mael2 mael
#define mael3(ma,x1,x2,x3) ( ((GEN) mael2((ma),(x1),(x2))) [x3])
#define mael4(ma,x1,x2,x3,x4) ( ((GEN) mael3((ma),(x1),(x2),(x3))) [x4])
#define mael5(ma,x1,x2,x3,x4,x5) (\
  ((GEN) mael4((ma),(x1),(x2),(x3),(x4))) [x5] \
)
#define gmael (GEN) mael
#define gmael2 (GEN) mael
#define gmael3 (GEN) mael3
#define gmael4 (GEN) mael4
#define gmael5 (GEN) mael5

#define coeff(a,i,j)  ( ( (GEN) ( (GEN) (a))[j]) [i])
#define gcoeff(a,i,j) ((GEN)coeff((a),(i),(j)))

#define labsi   (long)absi
#define labsr   (long)absr
#define lach    (long)gach
#define lacos   (long)gacos
#define ladd    (long)gadd
#define laddii  (long)addii
#define laddir  (long)addir
#define laddis  (long)addis
#define laddmat (long)gaddmat
#define laddrr  (long)addrr
#define laddrs  (long)addrs
#define laddsi  (long)addsi
#define laddsmat (long)gaddsmat
#define laddsr  (long)addsr
#define ladj    (long)adj
#define larg    (long)garg
#define lash    (long)gash
#define lasin   (long)gasin
#define lassmat (long)assmat
#define latan   (long)gatan
#define lath    (long)gath
#define lbezout (long)bezout
#define lbinome (long)binome
#define lcaract (long)caract
#define lcaradj (long)caradj
#define lceil   (long)gceil
#define lch     (long)gch
#define lchangevar (long)changevar
#define lclone  (long)gclone
#define lco8    (long)co8
#define lconcat (long)concat
#define lconj   (long)gconj
#define lcontent (long)content
#define lcopy   (long)gcopy
#define lcos    (long)gcos
#define lcvtoi  (long)gcvtoi
#define lderiv  (long)deriv
#define ldet    (long)det
#define ldet2   (long)det2
#define ldeuc   (long)gdeuc
#define ldiscsr (long)discsr
/* ldiv is a predefined macro on some AIX versions --GN1997Jan27 */
#ifdef ldiv
#undef ldiv
#endif
#define ldiv    (long)gdiv

#define ldivgs  (long)gdivgs
#define ldivii  (long)divii
#define ldivir  (long)divir
#define ldivis  (long)divis
#define ldivmod (long)gdivmod
#define ldivres (long)poldivres
#define ldivri  (long)divri
#define ldivrr  (long)divrr
#define ldivrs  (long)divrs
#define ldivsi  (long)divsi
#define ldivsr  (long)divsr
#define ldvmdii (long)dvmdii
#define ldvmdis (long)dvmdis
#define ldvmdsi (long)dvmdsi
#define lexp    (long)gexp
#define lfibo   (long)fibo
#define lfloor  (long)gfloor
#define lfrac   (long)gfrac
#define lgamd   (long)ggamd
#define lgamma  (long)ggamma
#define lgauss  (long)gauss
#define lgcd    (long)ggcd
#define lgetg   (long)cgetg
#define lgeti   (long)cgeti
#define lgetp   (long)cgetp
#define lgetr   (long)cgetr
#define lgreffe (long)greffe
#define lhilb   (long)hilb
#define licopy  (long)icopy
#define limag   (long)gimag
#define linteg  (long)integ
#define linv    (long)ginv
#define linvmat (long)invmat
#define linvmod (long)ginvmod
#define linvmulmat (long)invmulmat
#define llegendre (long)legendre
#define llift   (long)lift
#define llngamma  (long)glngamma
#define llog    (long)glog
#define lmax    (long)gmax
#define lmin    (long)gmin
#define lmod    (long)gmod
#define lmodii  (long)modii
#define lmodsi  (long)modsi
#define lmodulcp  (long)gmodulcp
#define lmodulo  (long)gmodulo
#define lmpabs  (long)mpabs
#define lmpach  (long)mpach
#define lmpacos (long)mpacos
#define lmpadd  (long)mpadd
#define lmpash  (long)mpash
#define lmpasin (long)mpasin
#define lmpatan (long)mpatan
#define lmpath  (long)mpath
#define lmpaut  (long)mpaut
#define lmpch   (long)mpch
#define lmpcos  (long)mpcos
#define lmpdiv  (long)mpdiv
#define lmpent  (long)mpent
#define lmpeuler (long)mpeuler
#define lmpexp  (long)mpexp
#define lmpexp1 (long)mpexp1
#define lmpfact (long)mpfact
#define lmpgamd (long)mpgamd
#define lmpgamma (long)mpgamma
#define lmpinvmod (long)mpinvmod
#define lmplngamma (long)mplngamma
#define lmplog  (long)mplog
#define lmpmul  (long)mpmul
#define lmpneg  (long)mpneg
#define lmppgcd (long)mppgcd
#define lmppi   (long)mppi
#define lmppsi  (long)mppsi
#define lmpsc1  (long)mpsc1
#define lmpsh   (long)mpsh
#define lmpshift (long)mpshift
#define lmpsin  (long)mpsin
#define lmpsqrt (long)mpsqrt
#define lmpsub  (long)mpsub
#define lmptan  (long)mptan
#define lmpth   (long)mpth
#define lmptrunc (long)mptrunc
#define lmul    (long)gmul
#define lmul2n  (long)gmul2n
#define lmulii  (long)mulii
#define lmulir  (long)mulir
#define lmulis  (long)mulis
#define lmulri  (long)mulri
#define lmulrr  (long)mulrr
#define lmulrs  (long)mulrs
#define lmulsg  (long)gmulsg
#define lmulsi  (long)mulsi
#define lmulsr  (long)mulsr
#define lmulss  (long)mulss
#define lneg    (long)gneg
#define lnegi   (long)negi
#define lnegr   (long)negr
#define lnorm   (long)gnorm
#define lnorml2 (long)gnorml2
#define lopgs2  (long)gopgs2
#define lopsg2  (long)gopsg2
#define lpasc   (long)pasc
#define lpile   (long)gerepile
#define lpilecopy (long)gerepilecopy
#define lpileupto (long)gerepileupto
#define lpileuptoint (long)gerepileuptoint
#define lpoleval (long)poleval
#define lpolgcd (long)polgcd
#define lpowgs  (long)gpowgs
#define lprec   (long)gprec
#define lprimpart (long)primpart
#define lpsi    (long)gpsi
#define lpui    (long)gpui
#define lpuigs  (long)gpuigs
#define lpuissmodulo (long)puissmodulo
#define lquadgen (long)quadgen
#define lquadpoly (long)quadpoly
#define lracine (long)racine
#define lrcopy  (long)rcopy
#define lreal   (long)greal
#define lrecip  (long)recip
#define lred    (long)gred
#define lres    (long)gres
#define lresii  (long)resii
#define lrndtoi (long)grndtoi
#define lroots  (long)roots
#define lround  (long)ground
#define lscalmat (long)gscalmat
#define lscalsmat (long)gscalsmat
#define lsh     (long)gsh
#define lshift  (long)gshift
#define lshifti (long)shifti
#define lshiftr (long)shiftr
#define lsin    (long)gsin
#define lsqr    (long)gsqr
#define lsqri   (long)sqri
#define lsqrt   (long)gsqrt
#define lstoi   (long)stoi
#define lsub    (long)gsub
#define lsubii  (long)subii
#define lsubir  (long)subir
#define lsubis  (long)subis
#define lsubres (long)subres
#define lsubri  (long)subri
#define lsubrr  (long)subrr
#define lsubrs  (long)subrs
#define lsubsi  (long)subsi
#define lsubsr  (long)subsr
#define lsubst  (long)gsubst
#define ltan    (long)gtan
#define ltchebi (long)tchebi
#define lth     (long)gth
#define ltrace  (long)gtrace
#define ltrans  (long)gtrans
#define ltrunc  (long)gtrunc

#define zero    (long)gzero
#define un      (long)gun
#define deux    (long)gdeux
#define lhalf   (long)ghalf
#define lpolx   (long)polx
#define lpolun  (long)polun

