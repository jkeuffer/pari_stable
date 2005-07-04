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
#define gmael1(m,x1)             (((GEN*)    (m))[x1])
#define gmael2(m,x1,x2)          (((GEN**)   (m))[x1][x2])
#define gmael3(m,x1,x2,x3)       (((GEN***)  (m))[x1][x2][x3])
#define gmael4(m,x1,x2,x3,x4)    (((GEN****) (m))[x1][x2][x3][x4])
#define gmael5(m,x1,x2,x3,x4,x5) (((GEN*****)(m))[x1][x2][x3][x4][x5])
#define gmael gmael2
#define gel   gmael1

#define coeff(a,i,j)  ( ( (GEN) ( (GEN) (a))[j]) [i])
#define gcoeff(a,i,j) (((GEN**)(a))[j][i])

#define laddii  (long)addii
#define laddir  (long)addir
#define laddis  (long)addis
#define ladd    (long)gadd
#define laddrr  (long)addrr
#define laddsi  (long)addsi
#define lclone  (long)gclone
#define lcopy   (long)gcopy
#define ldeuc   (long)gdeuc
#define ldiscsr (long)discsr
#define ldiventgs (long)gdiventgs
#define ldiventsg (long)gdiventsg
#define ldivgs  (long)gdivgs
#define ldivii  (long)divii
#define ldivir  (long)divir
#define ldivis  (long)divis
#define ldivmod (long)gdivmod
#define ldivri  (long)divri
#define ldivrr  (long)divrr
#define ldivrs  (long)divrs
#define ldivsg    (long)gdivsg
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
#define licopy  (long)icopy
#define limag   (long)gimag
#define linteg  (long)integ
#define linv    (long)ginv
#define linvmat (long)invmat
#define linvmod (long)ginvmod
#define llegendre (long)legendre
#define llift   (long)lift
#define llngamma  (long)glngamma
#define llog    (long)glog
#define lmaxgs    (long)gmaxgs
#define lmax    (long)gmax
#define lmaxsg    (long)gmaxsg
#define lmings    (long)gmings
#define lmin    (long)gmin
#define lminsg    (long)gminsg
#define lmodgs    (long)gmodgs
#define lmodii  (long)modii
#define lmod    (long)gmod
#define lmodsg    (long)gmodsg
#define lmodsi  (long)modsi
#define lmodulcp  (long)gmodulcp
#define lmodulo  (long)gmodulo
#define lmpabs  (long)mpabs
#define lmpadd  (long)mpadd
#define lmpcos  (long)mpcos
#define lmpdiv  (long)mpdiv
#define lmpent  (long)mpent
#define lmpeuler (long)mpeuler
#define lmpexp1 (long)mpexp1
#define lmpexp  (long)mpexp
#define lmpfact (long)mpfact
#define lmplog  (long)mplog
#define lmpmul  (long)mpmul
#define lmpneg  (long)mpneg
#define lmppgcd (long)mppgcd
#define lmppi   (long)mppi
#define lmpshift (long)mpshift
#define lmpsin  (long)mpsin
#define lmpsqrt (long)mpsqrt
#define lmpsub  (long)mpsub
#define lmptrunc (long)mptrunc
#define lmul2n  (long)gmul2n
#define lmulgs  (long)gmulgs
#define lmulii  (long)mulii
#define lmulir  (long)mulir
#define lmulis  (long)mulis
#define lmul    (long)gmul
#define lmulri  (long)mulri
#define lmulrr  (long)mulrr
#define lmulrs  (long)mulrs
#define lmulsg  (long)gmulsg
#define lmulsi  (long)mulsi
#define lmulsr  (long)mulsr
#define lmulss  (long)mulss
#define lnegi   (long)negi
#define lneg    (long)gneg
#define lnegr   (long)negr
#define lnorml2 (long)gnorml2
#define lnorm   (long)gnorm
#define lpilecopy (long)gerepilecopy
#define lpile   (long)gerepile
#define lpileuptoint (long)gerepileuptoint
#define lpileuptoleaf (long)gerepileuptoleaf
#define lpileupto (long)gerepileupto
#define lpoleval (long)poleval
#define lpowgs  (long)gpowgs
#define lprec   (long)gprec
#define lpsi    (long)gpsi
#define lpuigs  (long)gpuigs
#define lpui    (long)gpui
#define lquadgen (long)quadgen
#define lquadpoly (long)quadpoly
#define lracine (long)racine
#define lrcopy  (long)rcopy
#define lreal   (long)greal
#define lrecip  (long)recip
#define lred    (long)gred
#define lremii  (long)remii
#define lrem    (long)grem
#define lrndtoi (long)grndtoi
#define lroots  (long)roots
#define lround  (long)ground
#define lscalmat (long)gscalmat
#define lscalsmat (long)gscalsmat
#define lshifti (long)shifti
#define lshift  (long)gshift
#define lshiftr (long)shiftr
#define lsqri   (long)sqri
#define lsqr    (long)gsqr
#define lsqrt   (long)gsqrt
#define lstoi   (long)stoi
#define lsubgs  (long)gsubgs
#define lsubii  (long)subii
#define lsubir  (long)subir
#define lsubis  (long)subis
#define lsub    (long)gsub
#define lsubres (long)subres
#define lsubri  (long)subri
#define lsubrr  (long)subrr
#define lsubrs  (long)subrs
#define lsubst  (long)gsubst
#define lutoi   (long)utoi

/* ldiv is a predefined macro on some AIX versions --GN1997Jan27 */
#ifdef ldiv
#undef ldiv
#endif
#define ldiv    (long)gdiv
