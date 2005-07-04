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

#define ladd    (long)gadd
#define lcopy   (long)gcopy
#define llift   (long)lift
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
