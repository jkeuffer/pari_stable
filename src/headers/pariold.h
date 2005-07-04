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

/* For compatibility with 1.x.x */
/*casts*/
#define labsi   (long)absi
#define labsr   (long)absr
#define lach    (long)gach
#define lacos   (long)gacos
#define laddgs  (long)gaddgs
#define laddii  (long)addii
#define laddir  (long)addir
#define laddis  (long)addis
#define laddrr  (long)addrr
#define laddsg  (long)gaddsg
#define laddsi  (long)addsi
#define laddmat (long)gaddmat
#define laddrs  (long)addrs
#define laddsr  (long)addsr
#define ladj    (long)adj
#define larg    (long)garg
#define lash    (long)gash
#define lasin   (long)gasin
#define lassmat (long)assmat
#define latan   (long)gatan
#define lath    (long)gath
#define lbezout (long)bezout
#define lbinome (long)binomial
#define lcaract (long)caract
#define lcaradj (long)caradj
#define lceil   (long)gceil
#define lch     (long)gch
#define lchangevar (long)changevar
#define lclone  (long)gclone
#define lconcat (long)concat
#define lconj   (long)gconj
#define lcontent (long)content
#define lcos    (long)gcos
#define lcvtoi  (long)gcvtoi
#define lderiv  (long)deriv
#define ldet2   (long)det2
#define ldet    (long)det
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
#define lsin    (long)gsin
#define lsh     (long)gsh
#define lsubsg  (long)gsubsg
#define lsubsi  (long)subsi
#define lsubsr  (long)subsr
#define ltan    (long)gtan
#define ltchebi (long)tchebi
#define lth     (long)gth
#define ltrace  (long)gtrace
#define ltrans  (long)gtrans
#define ltrunc  (long)gtrunc

#define lhalf   (long)ghalf
#define lpolx   (long)polx
#define lpolun  (long)polun

/*functions renamed*/
#define globalreduction ellglobalred
#define taniyama(e) elltaniyama((e),precdl)
#define chinois chinese
#define binome binomial
#define egalii equalii
#define gegal gequal
#define gegalgs gequalgs
#define gegalsg gequalsg
#define zero  (long)gen_0
#define un    (long)gen_1
#define deux  (long)gen_2
#define gzero gen_0
#define gun   gen_1
#define gdeux gen_2
#define realzero real_0
#define realzero_bit real_0_bit
#define realun real_1
#define realmun real_m1
#define err pari_err /* move to e.g paritr.h ? */
#define init pari_init
#define gen2str GENtostr
#define gpui gpow
#define gpuigs gpowgs
#define classno3 hclassno
#define strtoGEN freadexpr
#define flisexpr freadexpr
#define flisseq freadseq
#define lisseq readseq
#define lisGEN readGEN
#define lisexpr readexpr
#define permute numtoperm
#define permuteInv permtonum
#define evallgef(x) 0
#define lgef lg
#define setlgef setlg
#define leadingcoeff(x) (pollead((x),-1))
#define poldivres poldivrem
#define nfdivres nfdivrem
#define gred gcopy
#define pvaluation Z_pvalrem
#define svaluation u_lvalrem
#define isprincipalrayall bnrisprincipal
#define rayclassno bnrclassno
#define rayclassnolist bnrclassnolist
#define idealhermite2 idealhnf0

#define apprgen padicappr
#define apprgen9 padicappr
#define factmod9 factorff
#define ggrandocp ggrando
#define glogagm glog
#define logagm  mplog
#define mpsqrtz  gopgz(absr,(x),(y))
#define adduumod Fl_add
#define subuumod Fl_sub
#define muluumod Fl_mul
#define divuumod Fl_div
#define powuumod Fl_pow
#define invumod Fl_inv
#define invsmod Fl_inv_signed
#define mpinvmod Fp_inv
#define powmodulo Fp_pow
#define mpsqrtmod Fp_sqrt
#define mpsqrtnmod Fp_sqrtn
#define mpsqrt  sqrtr
#define mpsqrtn  sqrtnr
#define resii  remii
#define resis  remis
#define ressi  remsi
#define resss  remss
#define resiiz  remiiz
#define resisz  remisz
#define ressiz  remsiz
#define resssz  remssz
#define gres    grem
#define lres    lrem
#define rcopy mpcopy
#define gdivise gdvd
#define divise dvdii
#define mpdivis dvdiiz
#define mpdivisis dvdisz
#define absr  mpabs
#define absi  mpabs
#define negi  mpneg
#define negr  mpneg
#define mpent mpfloor
#define mpentz mpfloorz
#define mpnegz(x,y) \
  STMT_START {pari_sp _av=avma;mpaff(mpneg(x),y);avma=_av;} STMT_END
#define mpabsz(x,y) \
  STMT_START {pari_sp _av=avma;mpaff(mpabs(x),y);avma=_av;} STMT_END
#define absrz(x,z)  mpabsz((x),(z))
#define negrz(x,z)  mpnegz((x),(z))
