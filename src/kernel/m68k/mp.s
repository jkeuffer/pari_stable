#*******************************************************************#
#===================================================================#
#*                                                                 *#
#=     oooooooooo          ooooo       oooooooooo      ooooo       =#
#*      ooooooooooo      ooooooooo      ooooooooooo     ooo        *#
#*      ooo     ooo     ooo     ooo     ooo     ooo     ooo        *#
#=      ooo     ooo     ooo     ooo     ooo     ooo     ooo        =#
#*      ooooooooooo     ooooooooooo     oooooooooo      ooo        *#
#=      oooooooooo      ooooooooooo     ooooooooooo     ooo        =#
#*      ooo             ooo     ooo     ooo     ooo     ooo        *#
#=      ooo             ooo     ooo     ooo     ooo     ooo        =#
#*     ooooo           ooooo   ooooo   ooooo   ooooo   ooooo       *#
#*                                                                 *#
#=                                                                 =#
#*                      version numero 2                           *#
#*                                                                 *#
#=                          commentee                              =#
#*                                                                 *#
#=                 fichier cree le 22 sept. 1987                   =#
#*                                                                 *#
#=                              par                                =#
#*                                                                 *#
#=        christian batut , henri cohen , michel olivier           =#
#*                                                                 *#
#=        """"""""""""""""""""""""""""""""""""""""""""""           =#
#*                                                                 *#
#===================================================================#
#*******************************************************************#
#*     $Id$     *#

#-------------------------------------------------------------------#
#  Notations :                                                      #
#               T = type ( S , I , ou R ).                          #
#               R = type reel.                                      #
#               S = type entier court ( long du C).                 #
#               P = p-adique.                                       #
#                                                                   #
#               L = longueur de la mantisse pour un reel ;          #
#                   longueur de la mantisse effective pour un entier#
#               l = longueur totale du nombre avec codage.          #
#               le= longueur effective totale de l'entier avec code #
#                   on doit avoir : l <= 2^15-1.                    #
#                                                                   #
#               exp = exposant non biaise d'un reel.                #
#               fexp= exposant biaise ( fexp = exp + 2^23 ).        #
#                     on doit avoir : -2^23 <= exp < 2^23           #
#               fvalp=valuation p-adique biaisee d'un p-adique.     #
#                     ( fvalp = valuation + 2^15 )                  #
#-------------------------------------------------------------------#
#-------------------------------------------------------------------#
#   Conventions :                                                   #
#               Tous les sous programmes creent la place necessaire #
#               pour stocker le resultat , a l'exception des        #
#               programmes d'affectation et d'echange , ainsi que   #
#               des programmes dont le nom se termine par la lettre #
#               "z" . On entre dans ces derniers avec une zone creee#
#               dans la pile PARI ou le resultat est range.         #
#                                                                   #
#               Le nombre reel 0 s'ecrit avec mantisse non          #
#               significative;le deuxieme lgmot code contient       #
#               -32*L + (2^23) ou L est la longueur de la mantisse  #
#                                                                   #
#               Les registres a0,a1,d0,d1 sont en general utilises  #
#               par les programmes et ne sont pas restaures a leurs #
#               valeurs d'entree.Tous les autres sont sauvegardes.  #
#                                                                   #
#               Les objets utilises par PARI sont crees dans une    #
#               pile dite dans la suite "pile PARI",pointee par     #
#               _avma.                                              #
#-------------------------------------------------------------------#

affer1  = 23
affer2  = 24
affer3  = 25
affer4  = 26
affer5  = 27
shier1  = 28
shier2  = 29
truer1  = 30
truer2  = 31
adder1  = 32
adder2  = 33
adder3  = 34
adder4  = 35
adder5  = 36
muler1  = 37
muler2  = 38
muler3  = 39
muler4  = 40
muler5  = 41
muler6  = 42
diver1  = 43
diver2  = 44
diver3  = 45
diver4  = 46
diver5  = 47
diver6  = 48
diver7  = 49
diver8  = 50
diver9  = 51
diver10 = 52
diver11 = 53
diver12 = 54
divzer1 = 55
dvmer1  = 56
moder1  = 57
reser1  = 58
arier1  = 59
arier2  = 60
errpile = 61

        .text

        .globl  _cget,_cgetg,_cgeti,_cgetr
        .globl  _mpaff,_affsz,_affsi,_affsr,_affii,_affir
        .globl  _affrs,_affri,_affrr
        .globl  _stoi,_itos
        .globl  _mptrunc,_mptruncz,_mpent,_mpentz
        .globl  _vals,_vali
        .globl  _mpshift,_mpshiftz,_shifts,_shifti,_shiftr
        .globl  _mpcmp,_cmpsi,_cmpsr,_cmpis,_cmpii,_cmpir
        .globl  _cmprs,_cmpri,_cmprr
        .globl  _mpadd,_addss,_addsi,_addsr,_addii,_addir,_addrr
        .globl  _mpaddz,_addssz,_addsiz,_addsrz,_addiiz,_addirz,_addrrz
        .globl  _mpsub,_subss,_subsi,_subsr,_subis,_subii,_subir
        .globl  _subrs,_subri,_subrr
        .globl  _mpsubz,_subssz,_subsiz,_subsrz,_subisz,_subiiz,_subirz
        .globl  _subrsz,_subriz,_subrrz
        .globl  _mpmul,_mulss,_mulsi,_mulsr,_asmmulii,_mulir,_mulrr
        .globl  _mpmulz,_mulssz,_mulsiz,_mulsrz,_muliiz,_mulirz,_mulrrz
        .globl  _dvmdss,_dvmdsi,_dvmdis,_asmdvmdii
        .globl  _mpdvmdz,_dvmdssz,_dvmdsiz,_dvmdisz,_dvmdiiz
        .globl  _mpdiv,_divss,_divsi,_divsr,_divis,_divii,_divir
        .globl  _divrs,_divri,_divrr
        .globl  _mpdivis,_divise
        .globl  _mpdivz,_divssz,_divsiz,_divsrz,_divisz,_diviiz,_divirz
        .globl  _divrsz,_divriz,_divrrz
        .globl  _mpinvz,_mpinvsr,_mpinvir,_mpinvrr
        .globl  _modss,_modsi,_modis,_modii
        .globl  _mpmodz,_modssz,_modsiz,_modisz,_modiiz
        .globl  _resss,_ressi,_resis,_resii
        .globl  _mpresz,_resssz,_ressiz,_resisz,_resiiz
        .globl  _addsii,_mulsii,_divisii

#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**             PROGRAMMES DE GESTION DE LA MEMOIRE PARI          **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#



#===================================================================#
#                                                                   #
#           Allocation memoire dans pile PARI en C                  #
#                                                                   #
#       entree : a7@(4) contient la longueur totale a attribuer     #
#       sortie : d0 pointe sur un type I ou R                       #
#                d1 et a1 sont inutilises                           #
#                                                                   #
#===================================================================#

_cget:  movl    sp@(4),d0
        bsr     get
        movl    a0,d0
        rts

_cgetg: movl    sp@(8),d0       | a7@(8) contient le type
        rorl    #8,d0
        movw    sp@(6),d0
        bsr     get
        movl    a0,d0
        rts

_cgeti: movl    sp@(4),d0
        bsr     geti
        movl    a0,d0
        rts

_cgetr: movl    sp@(4),d0
        bsr     getr
        movl    a0,d0
        rts

#===================================================================#
#                                                                   #
#               Allocation memoire dans pile PARI                   #
#                                                                   #
#       entree : d0.w contient le nombre total de longs mots        #
#                demandes si type I ou R                            #
#       sortie : a0 pointe sur la zone allouee ; _avma est mis      #
#                a jour ; message d'erreur si memoire insuffisante ;#
#                d0 est inchange;d1 et a1 sont sauvegardes.         #
#       remarque : il est interdit de creer des type S dans la pile #
#                                                                   #
#===================================================================#

                                | allocation memoire type qcque

get:    movl    d1,sp@-         | d0.l contient code et longueur
        moveq   #0,d1
        movw    d0,d1
        lsll    #2,d1
        movl    _avma,a0
        subl    d1,a0
        cmpl    _bot,a0
        bmi     mnet
        movl    a0,_avma
#        swap    d0
#        movb    #1,d0
#        swap    d0
        movl    d0,a0@
        movl    sp@+,d1
        rts

                                | allocation memoire de type I

geti:   movl    d1,sp@-
        moveq   #0,d1
        movw    d0,d1
        lsll    #2,d1
        movl    _avma,a0
        subl    d1,a0
        cmpl    _bot,a0
        bmi     mnet
        movl    a0,_avma
        movw    #0x100,a0@
        movw    d0,a0@(2)
        movl    sp@+,d1
        rts

                                | allocation memoire type R

getr:   movl    d1,sp@-
        moveq   #0,d1
        movw    d0,d1
        lsll    #2,d1
        movl    _avma,a0
        subl    d1,a0
        cmpl    _bot,a0
        bmi     mnet
        movl    a0,_avma
        movw    #0x200,a0@
        movw    d0,a0@(2)
        movl    sp@+,d1
        rts

                                | nettoyage pile PARI
                                | a ecrire .....!!!!!!!!!
mnet:   movl    #errpile,sp@-
        jsr     _pari_err

#===================================================================#
#                                                                   #
#               Desallocation memoire PARI                          #
#                                                                   #
#       entree : a0@ contient le premier long mot code d'une        #
#                zone memoire a desallouer : uniquement de type     #
#                I ou R                                             #
#       sortie : _avma est mis a jour si necessaire                 #
#                a0 pointe sur avma a jour                          #
#                tous les autres registres sont inchanges           #
#                                                                   #
#===================================================================#

giv:    movl    d0,sp@-
        cmpl    _avma,a0
        bne     givf
                                | ici la zone en tete de pile: on desalloue
        movw    a0@(2),d0
        lea     a0@(0,d0:w:4),a0| a0 pointe sur zone suivante
        movl    a0,_avma

givf:   movl    sp@+,d0
        rts

#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**             PROGRAMMES D'AFFECTATION OU D'ECHANGE             **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#       Affectation generale    n2 --> n1                           #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : la zone pointee par a7@(8) contient n2             #
#       interdit : n2 ou n1 de type S                               #
#       remarques: erreur dans le cas R --> I                       #
#                  d0,d1,a0,a1 sont inchanges                       #
#                                                                   #
#===================================================================#

_mpaff: cmpb    #1,sp@(8)@
        bne     1$
                                | ici T1 = I
        cmpb    #1,sp@(4)@
        beq     _affii          | ici T1 = T2 = I
        bra     _affri          | ici T1 = I et T2 = R
                                | ici T1 = R
1$:     cmpb    #1,sp@(4)@
        beq     _affir          | ici T1 = R et T2 = I
        bra     _affrr          | ici T1 = T2 = R

#-------------------------------------------------------------------#

                                | affectation s2 --> i1 ou r1
_affsz: cmpb    #2,sp@(4)@
        beq     _affsr
                                | affectation s2 --> i1

_affsi: link    a6,#0
        moveml  d0/a0,sp@-
        movl    a6@(8),d0       | d0.l contient s2
        movl    a6@(12),a0      | a0 pointe sur i1
        cmpw    #2,a0@(2)
        bne     1$
                                | ici l1 = 2 (i1 = 0)
        tstl    d0
        beq     4$
                                | ici s2 <> 0 (erreur)
        movl    #affer1,sp@-
        jsr     _pari_err
                                | ici s2 = 0 ou l1 >= 3
1$:     tstl    d0
4$:     bmi     2$
                                | ici s2 >= 0
        bne     3$
                                | ici s2 = 0
        movl    #2,a0@(4)
        bra     affsif
                                | ici s2 > 0 et l1 >= 3
3$:     movl    #0x1000003,a0@(4)
        movl    d0,a0@(8)
        bra     affsif
                                | ici s2 < 0 et l1 >= 3
2$:     movl    #0xff000003,a0@(4)
        negl    d0
        movl    d0,a0@(8)
affsif: moveml  sp@+,d0/a0
        unlk    a6
        rts

#-------------------------------------------------------------------#

                                | affectation i2 --> i1

_affii: link    a6,#0
        moveml  d0/a0-a1,sp@-
        movl    a6@(8),a1       | a1 pointe sur i2
        movl    a6@(12),a0      | a0 pointe sur i1
        cmpl    a0,a1
        beq     affiif
                                | ici a0 <> a1
        movw    a0@(2),d0       | d0.w contient l1
        cmpw    a1@(6),d0
        bcc     1$
                                | ici le2 > l1 (erreur)
        movl    #affer3,sp@-
        jsr     _pari_err
                                | ici le2 <= l1
1$:     movw    a1@(6),d0       | d0.w contient le2
        subqw   #2,d0           | d0.w contient L2
        addql   #4,a0
        addql   #4,a1
                                | copie de i2 dans i1
2$:     movl    a1@+,a0@+
        dbra    d0,2$
affiif: moveml  sp@+,d0/a0-a1
        unlk    a6
        rts

#-------------------------------------------------------------------#

                                | conversion i --> long du C dans d0

_itos:  movl    a1,sp@-
        movl    sp@(8),a1       | a1 pointe sur i2
        cmpw    #3,a1@(6)
        bls     1$
                                | ici l2 >= 4 (erreur)
        movl    #affer2,sp@-
        jsr     _pari_err
                                | ici l2 <= 3
1$:     beq     2$
                                | ici l2 = 2 (i2 = 0)
        moveq   #0,d0
        bra     itosf
                                | ici l2 = 3
2$:     movl    a1@(8),d0       | d0.l contient |i2|
        cmpl    #0x80000000,d0
        bcs     3$
        beq     4$
                                | ici |i2| > 2^31 (erreur)
5$:     movl    #affer2,sp@-
        jsr     _pari_err
                                | ici |i2| = 2^31
4$:     tstb    a1@(4)
        bpl     5$              | si i2 = 2^31 erreur
        bra     itosf           | ici i2 = -2^31
                                | ici |i2| <= 2^31-1
3$:     tstw    a1@(4)
        bpl     itosf
        negl    d0
itosf:  movl    sp@+,a1
        rts

#-------------------------------------------------------------------#

                                | conversion long du C --> i cree

_stoi:  movl    sp@(4),d1
        bne     1$
	movl	_gzero,d0
	rts
1$:     movl    #3,d0
        bsr     geti
        tstl    d1
        bmi     2$
        movl    #0x1000003,a0@(4)
        bra     3$
2$:     movl    #0xff000003,a0@(4)
        negl    d1
3$:     movl    d1,a0@(8)
	movl    a0,d0
        rts

#-----------------------------------------------------------------------#

                                | affectation s2 --> r1

_affsr: link    a6,#0
        moveml  d0-d1/a0,sp@-
        movl    a6@(12),a0      | a0 pointe sur r1
        movl    a6@(8),d0       | d0.l contient s2
        bne     1$
                                | ici s2 = 0
        moveq   #0,d0
        movw    a0@(2),d0
        subqw   #2,d0
        lsll    #5,d0
        negl    d0
        addl    #0x800000,d0    | d0.l contient fexp(0)
        movl    d0,a0@(4)
        clrl    a0@(8)
        bra     affsrf
                                | ici s2 <> 0
1$:     bpl     2$
        negl    d0
        movb    #0xff,a0@(4)    | mise signe si s2 < 0
        bra     3$
2$:     movb    #1,a0@(4)       | mise signe si s2 > 0
                                | ici s2 <> 0
3$:     bfffo   d0{#0:#0},d1    | d1.l recoit nb. de shifts (=k)
        lsll    d1,d0           | d0.l est norme
        negw    d1
        addw    #31,d1
        movw    d1,a0@(6)
        movb    #0x80,a0@(5)    | mise exposant
        movl    d0,a0@(8)       | mise 1er long mot mantisse
        moveq   #0,d0
        movw    a0@(2),d1
        subql   #3,d1           | d1.w recoit L1-1
        addl    #12,a0          | a0 pointe sur 2eme long mot mantisse
        bra     4$
5$:     movl    d0,a0@+
4$:     dbra    d1,5$
affsrf: moveml  sp@+,d0-d1/a0
        unlk    a6
        rts

#-------------------------------------------------------------------#

                                | affectation i2 --> r1

_affir: link a6,#0
        moveml  d0-d6/a0-a1,sp@-
        movl    a6@(8),a1       | a1 pointe sur i2
        movl    a6@(12),a0      | a0 pointe sur r1
        tstb    a1@(4)
        bne     1$
                                | ici i2 = 0
        moveq   #0,d0
        movw    a0@(2),d0
        subqw   #2,d0
        lsll    #5,d0
        negl    d0
        addl    #0x800000,d0
        movl    d0,a0@(4)
        clrl    a0@(8)
        bra     affirf
                                | ici i2 <> 0
1$:     movl    a1@(8),d0       | d0.l contient 1er lg mot mantisse
        bfffo   d0{#0:#0},d1    | d1.l recoit nb de shifts (=k)
        lsll    d1,d0           | d0.l normalise
        moveq   #0,d2
        movw    a1@(6),d2
        lsll    #5,d2
        subl    d1,d2
        addl    #0x7fffbf,d2    | d2.l = fexp2 = 2^23 + L1*32 -1 -k
        movl    d2,a0@(4)       | mise exposant
        movb    a1@(4),a0@(4)   | mise signe
        movw    a1@(6),d4
        subqw   #3,d4           | d4.w recoit L2-1 (compteur)
        movw    a0@(2),d2
        subqw   #3,d2           | d2.w recoit L1-1
        addl    #12,a1          | a1 pointe sur 2eme lg mot mantisse i2
        addql   #8,a0           | a0 ponte sur 1er lg mot mantisse r1
        moveq   #1,d6           | masque
        lsll    d1,d6
        subql   #1,d6
        subw    d4,d2           | d2.w  recoit L1-L2
        bpl     2$
                                | ici L1 < L2
        addw    d2,d4           | d4.w  recoit L1-1
        bra     2$
                                | copie mantisse shiftee dans r1
3$:     movl    a1@+,d3
        roll    d1,d3
        movl    d3,d5
        andl    d6,d3
        addl    d3,d0
        movl    d0,a0@+
        subl    d3,d5
        movl    d5,d0
2$:     dbra    d4,3$
        tstw    d2
        bmi     4$
                                | ici L1 > L2 completer par des 0
        moveq   #0,d3
        movl    d0,a0@+
        bra     5$
6$:     movl    d3,a0@+
5$:     dbra    d2,6$
        bra     affirf
                                | ici L1 <= L2
4$:     movl    a1@+,d3
        roll    d1,d3
        andl    d6,d3
        addl    d3,d0
        movl    d0,a0@+         | mise a jour dernier lg mot
affirf: moveml  sp@+,d0-d6/a0-a1
        unlk    a6
        rts

#-------------------------------------------------------------------#

                                | affectation r2 --> r1

_affrr: link    a6,#0
        moveml  d0-d1/a0-a1,sp@-
        movl    a6@(8),a1       | a1 pointe sur r2
        movl    a6@(12),a0      | a0 pointe sur r1
        cmpl    a0,a1
        beq     affrrf
                                | ici a0 <> a1
        tstb    a1@(4)
        bne     6$
                                | ici r2 = 0
        movl    a1@(4),a0@(4)
        clrl    a0@(8)
        bra     affrrf
                                | ici r2 <> 0
6$:     addql   #4,a0
        addql   #4,a1
        movw    a0@(-2),d0
        movw    a1@(-2),d1      | d0.w , d1.w contient l1,l2
        cmpw    d0,d1
        bhi     1$
                                | ici l1 >= l2
        subw    d1,d0           | d0.w contient l1-l2
        subqw   #2,d1           | d1.w  contient L2
3$:     movl    a1@+,a0@+       | copie de r2 dans r1
        dbra    d1,3$
        moveq   #0,d1
        bra     2$
                                | ici completer par des 0
4$:     movl    d1,a0@+
2$:     dbra    d0,4$
        bra     affrrf
                                | ici l2 > l1
1$:     subqw   #2,d0           | d0.w recoit L1 (compteur)
5$:     movl    a1@+,a0@+
        dbra    d0,5$
affrrf: moveml  sp@+,d0-d1/a0-a1
        unlk    a6
        rts

#-------------------------------------------------------------------#

                                | affectation r2 --> s1

_affrs: movl    #affer4,sp@-
        jsr     _pari_err

#-------------------------------------------------------------------#

                                | affectation r2 --> i1

_affri: movl    #affer5,sp@-
        jsr     _pari_err


#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     VALUATION                                 **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#       Valuation 2-adique d'un entier court ou d'un entier         #
#                                                                   #
#       entree : a7@(4) contient s1 de type S ou pointe sur i1 de   #
#                type I                                             #
#       sortie : d0.l contient k tel que : k>=0 , n1=2^k*n2 ,       #
#                avec n2 et 2 premiers entre eux ; si n1=0 , alors  #
#                d0.l contient -1.                                  #
#       remarque : type R interdit                                  #
#                                                                   #
#===================================================================#

                                | valuation de s1 de type S

_vals:  link    a6,#0
        movl    d2,sp@-
        moveq   #-1,d0
        movl    a6@(8),d1       | d1.l contient s1
        beq     valsf
        moveq   #0,d0
        tstw    d1
        bne     1$
        addl    #16,d0
        swap    d1
1$:     tstb    d1
        bne     2$
        addql   #8,d0
        lsrl    #8,d1
2$:     movl    d1,d2
        andl    #15,d2
        bne     3$
        addql   #4,d0
        lsrl    #4,d1
3$:     movl    d1,d2
        andl    #3,d2
        bne     4$
        addql   #2,d0
        lsrl    #2,d1
4$:     btst    #0,d1
        bne     valsf
        addql   #1,d0
valsf:  movl    sp@,d2
        unlk    a6
        rts

                                | valuation de i1 de type I

_vali:  link    a6,#0
        movl    d2,sp@-
        movl    a6@(8),a1       | a1 pointe sur i1
        moveq   #-1,d0
        tstb    a1@(4)
        beq     valif
                                | ici i1 <> 0
        movw    a1@(6),d1       | d1.w contient L1+2
        lea     a1@(0,d1:w:4),a1| a1 pointe fin mantisse de i1
        movl    #0xffff,d0
5$:     tstl    a1@-
        dbne    d0,5$
        notw    d0
        lsll    #5,d0           | d0.l contient 32*nb.de lgmots nuls
        movl    a1@,d1          | a droite de i1 et a1 pointe 1er lgmot
        tstw    d1              | non nul (qui existe car i1 <> 0)
        bne     1$
        addl    #16,d0
        swap    d1
1$:     tstb    d1
        bne     2$
        addql   #8,d0
        lsrl    #8,d1
2$:     movl    d1,d2
        andl    #15,d2
        bne     3$
        addql   #4,d0
        lsrl    #4,d1
3$:     movl    d1,d2
        andl    #3,d2
        bne     4$
        addql   #2,d0
        lsrl    #2,d1
4$:     btst    #0,d1
        bne     valif
        addql   #1,d0
valif:  movl    sp@,d2
        unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES DE SHIFT                       **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Shift general                               #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) contient k = nombre de shifts               #
#       sortie : d0 pointe sur n1 de type I ou R                    #
#                contenant n1 = 2^k * n2 (zone creee)               #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpshift:cmpb   #1,sp@(4)@
        beq     _shifti
        bra     _shiftr

#===================================================================#
#                                                                   #
#                       Shift (par valeur)                          #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) contient le nombre de shifts (=k)           #
#                a7@(12) pointe sur n1 de type I ou R               #
#       sortie : la zone pointee par a7@(12) contient 2^k * n2      #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpshiftz:movl  sp@(4),a0
        cmpl    sp@(12),a0
        bne     1$
        cmpb    #2,a0@
        bne     1$
        movl    a0@(4),d0
        andl    #0xffffff,d0
        addl    sp@(8),d0
        bvs     shier
        cmpl    #0x1000000,d0
        bcc     shier
        tstl    d0
        bmi     shier
        movw    d0,a0@(6)
        swap    d0
        movb    d0,a0@(5)
        rts
1$:     movl    sp@(8),sp@-
        movl    sp@(8),sp@-
        bsr     _mpshift
        movl    d0,sp@
        movl    sp@(20),sp@(4)
        bsr     _mpaff
        movl    sp@,a0
        addql   #8,sp
        bra     giv

#===================================================================#
#                                                                   #
#               Shift d'un entier court = entier                    #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient k = nombre de shifts               #
#       sortie : d0 pointe sur i1 de type I                         #
#                avec i1 = 2^k * s2 (zone creee)                    #
#                                                                   #
#===================================================================#

_shifts:link    a6,#-12
        movl    a6@(12),sp@-    | empilage k
        movl    a6@(8),d0       | d0.l contient s2
        bne     1$
                                | ici s2 = 0
        movl    #0x1000002,a6@(-12)
        movl    #2,a6@(-8)      | creation de 0 en var. locale
        bra     3$
                                | ici s2 <> 0
1$:     movl    #0x1000003,a6@(-12)
        movl    #0x1000003,a6@(-8)
        tstl    d0
        bpl     2$
        negl    d0
        movb    #0xff,a6@(-8)
2$:     movl    d0,a6@(-4)      | creation de s2 en var. locale
3$:     pea     a6@(-12)        | empilage adresse var. locale
        bsr     _shifti
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#                       Shift entier = entier                       #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient k = nombre de shifts               #
#       sortie : d0 pointe sur i1 de type I                         #
#                avec i1 = 2^k * i2 (zone creee)                    #
#                                                                   #
#===================================================================#

_shifti:link    a6,#0
        moveml  d2-d7/a2-a3,sp@-
        movl    a6@(8),a2       | a2 pointe sur i2
        movl    a6@(12),d7      | d7.l contient k
        bne     1$
                                | ici k = 0
        movw    a2@(2),d0
        bsr     geti
        movl    a0,a3   | sauvegarde adresse resultat
        subqw   #2,d0
        addql   #4,a0
        addql   #4,a2
24$:    movl    a2@+,a0@+
        dbra    d0,24$
        bra     shiftif
                                | ici k <> 0
1$:     tstb    a2@(4)
        bne     2$
                                | ici i1 = 0
6$:     movl    _gzero,d0       | sauvegarde adresse resultat
        bra     shiftig
                                | ici k <> 0 et i2 <> 0
2$:     moveq   #0,d0
        movw    a2@(6),d0       | d0.w contient L2+2
        cmpl    #1,d7
        bne     3$
                                | ici k = 1 et i2 <> 0
        movl    a2@(8),d5
        btst    #31,d5
        beq     4$
                                | ici d5 >= 2^31
        addqw   #1,d0           | demander 1 lgmot supplementaire
        cmpw    #0x8000,d0
        bcs     4$
                                | ici debordement
18$:    movl    #shier1,sp@-
        jsr     _pari_err
                                | ici k = 1 et i2 <> 0
4$:     bsr     geti
        movl    a0,a3           | sauvegarde adresse resultat
        movw    a0@(2),a0@(6)   | mise longueur effective
        movb    a2@(4),a0@(4)   | mise signe
        lea     a0@(0,d0:w:4),a1| a1 pointe fin resultat
        lea     a2@(0,d0:w:4),a2
        btst    #31,d5
        beq     5$
        subqw   #4,a2           | ici a2 pointe fin i2
        movl    #1,a0@(8)
        subqw   #1,d0
5$:     subqw   #3,d0           | d0.w compteur
7$:     movl    a2@-,d1
        roxll   #1,d1
        movl    d1,a1@-
        dbra    d0,7$
        bra     shiftif
                                | ici k <> 1 et i2 <> 0
3$:     cmpl    #-1,d7
        bne     8$
                                | ici k = -1 et i2 <> 0
        cmpl    #1,a2@(8)
        bhi     9$
        subqw   #1,d0
        cmpw    #2,d0
        beq     6$              | si i1 = 0
9$:     bsr     geti
        movl    a0,a3
        movb    a2@(4),a0@(4)   | mise signe
        movw    a0@(2),a0@(6)   | mise longueur effective
        addql   #8,a0
        addql   #8,a2
        movw    a2@(-2),d0
        subqw   #3,d0           | d0.w compteur
        movl    a2@+,d1
        lsrl    #1,d1
        beq     10$
        movl    d1,a0@+
        bra     10$
11$:    movl    a2@+,d1
        roxrl   #1,d1
        movl    d1,a0@+
10$:    dbra    d0,11$
        bra     shiftif
                                | ici k<>0,k<>1,k<>-1 et i2<>0
8$:     tstl    d7
        bpl     12$
                                | ici shift a droite : k < -1 et i2 <> 0
        negl    d7              | d7.l contient /k/
        movl    d7,d4
        lsrl    #5,d4           | d4.l contient q
        andl    #31,d7          | k=32*q+r; d7.l contient r

        subw    #2,d0           | d0.w contient L2
        cmpw    d4,d0
        bls     6$              | si r1 <= 0
        addw    #2,d0           |
        subw    d4,d0           | d0.w contient L2+2-q

        movl    a2@(8),d4
        lsrl    d7,d4
        bne     13$
                                | ici on perd un lgmot de resultat
        subqw   #1,d0
        cmpw    #2,d0
        beq     6$              | si r1 = 0
13$:    bsr     geti            | allocation memoire pour resultat
        movl    a0,a3
        movb    a2@(4),a0@(4)   | mise signe
        movw    a0@(2),a0@(6)   | mise longueur effective
        lea     a2@(0,d0:w:4),a2| a2 pointe ou il faut !
        lea     a0@(0,d0:w:4),a1| a1 pointe fin resultat
        tstl    d4
        beq     14$
        movl    d4,a0@(8)
        subqw   #3,d0           | d0.w compteur
        bra     15$
14$:    addql   #4,a2
        subqw   #2,d0
15$:    moveq   #-1,d6
        lsrl    d7,d6           | masque de shift
        movl    a2@-,d4
        lsrl    d7,d4
        bra     16$
17$:    movl    a2@-,d2         | boucle de shift
        rorl    d7,d2
        movl    d2,d3
        andl    d6,d3
        subl    d3,d2
        addl    d2,d4
        movl    d4,a1@-
        movl    d3,d4
16$:    dbra    d0,17$
        bra     shiftif
                                | ici shift a gauche : k > 1 et i2 <> 0
12$:    movl    d7,d4
        andl    #31,d7          | d7.l contient r
        lsrl    #5,d4           | d4.l contient q (k=32*q+r)
        addl    d4,d0           | d0.l contient L2+2+q
        cmpw    #0x7fff,d0
        bcc     18$
        moveq   #-1,d6
        lsll    d7,d6
        notl    d6              | masque de shift
        movl    a2@(8),d2
        roll    d7,d2
        movl    d2,d3
        andl    d6,d3
        beq     19$
        addqw   #1,d0           | un long mot supplementaire
19$:    bsr     geti
        movl    a0,a3
        movl    a0@(2),a0@(6)   | mise longueur effective
        movb    a2@(4),a0@(4)   | mise signe
        addql   #8,a0
        tstl    d3
        beq     20$
        movl    d3,a0@+
20$:    subl    d3,d2
        movl    d2,d5
        movw    a2@(6),d0
        addl    #12,a2
        subqw   #3,d0           | d0.w contient compteur
        bra     21$
22$:    movl    a2@+,d2
        roll    d7,d2
        movl    d2,d3
        andl    d6,d3
        subl    d3,d2
        addl    d3,d5
        movl    d5,a0@+
        movl    d2,d5
21$:    dbra    d0,22$
        movl    d5,a0@+
        moveq   #0,d0
        bra     23$
25$:    movl    d0,a0@+
23$:    dbra    d4,25$
shiftif:movl    a3,d0           | d0 pointe sur resultat
shiftig:moveml  sp@+,d2-d7/a2-a3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#                       Shift reel = reel                           #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) contient k = nombre de shifts               #
#       sortie : d0 pointe sur r1 de type R                         #
#                avec r1 = 2^k * r2 zone creee)                     #
#                                                                   #
#===================================================================#

_shiftr:link    a6,#0
        moveml  d2/a2-a3,sp@-
        movl    a6@(8),a2       | a2 pointe sur r2
        movl    a6@(12),d2      | d2.l contient k
        bne     1$
                                | ici k = 0
        movw    a2@(2),d0
        bsr     getr
        movl    a0,a3
        subqw   #2,d0
        addql   #4,a0
        addql   #4,a2
4$:     movl    a2@+,a0@+
        dbra    d0,4$           | boucle de recopie de r2 dans r1
        bra     shiftrf
                                | ici k <> 0
1$:     movl    a2@(4),d1
        andl    #0xffffff,d1
        addl    d2,d1           | d1.l contient fexp2 + k
        bvc     sh
                                | ici debordement
shier:  movl    #shier2,sp@-
        jsr     _pari_err
                                | ici k + fexp2 <= 2^31 -1
sh:     cmpl    #0x1000000,d1
        bcc     shier           | si k + fexp2 >= 2^24
        tstl    d1
        bmi     shier           | si k + fexp2 < 0
        movw    a2@(2),d0
        bsr     getr            | allocation memoire pour resultat
        movl    a0,a3
        movl    d1,a0@(4)       | mise exposant
        movb    a2@(4),a0@(4)   | mise signe
        addql   #8,a0
        addql   #8,a2
        subqw   #3,d0
5$:     movl    a2@+,a0@+
        dbra    d0,5$
shiftrf:movl    a3,d0           | d0 pointe sur resultat
        moveml  sp@+,d2/a2-a3
        unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES DE PARTIE ENTIERE              **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#               Fausse partie entiere (trunc)                       #
#                                                                   #
#       entree : a7@(4) pointe sur n1 de type I ou de type R        #
#       sortie : d0 pointe sur i1 de type I (zone creee)            #
#       calcul : si r1 >= 0 , i1 est la partie entiere              #
#                si r1 < 0 , i1 = - Ent (-r1)                       #
#       remarque : type S interdit                                  #
#                                                                   #
#===================================================================#

_mptrunc:link   a6,#0
        moveml  d2-d6/a2-a4,sp@-
        movl    a6@(8),a1       | a1 pointe sur n1
        cmpb    #1,a1@
        bne     5$
                                | ici n1 est de type I
        movw    a1@(6),d0
        bsr     geti
        movl    a0,a4
        subqw   #2,d0
        addql   #4,a0
        addql   #4,a1
7$:     movl    a1@+,a0@+
        dbra    d0,7$
        bra     truncf
                                | ici n1 est de type R
5$:     movl    a1@(4),d3       | d3.l contient second long mot code r1
        movl    d3,d0
        andl    #0xffffff,d0    | d0.l contient fexp1
        subl    #0x800000,d0    | d0.l contient exp1
        bpl     1$
                                | ici exp1 < 0 (trunc r1 = 0)
	movl	_gzero,d0
        bra     truncg
                                | ici exp1 >= 0
1$:     movl    d0,d2           | d2.l  contient exp1
        lsrl    #5,d0           | d0.l contient exp1 div 32 = q
        addql   #3,d0           | d0.l  contient le(i1)
        cmpl    #0x7fff,d0
        bls     2$
                                | ici le(i1)> 2^15 : erreur
        movl    #truer1,sp@-
        jsr     _pari_err
                                | ici le(i1)<=2^15
2$:     bsr     geti            | allocation q+3 longs mots pour i1
        movl    a0,a4
        movw    d0,a0@(6)       | mise longueur effective de i1
        movb    a1@(4),a0@(4)   | mise signe de i1
        movl    a0,a3           | sauvegarde adresse i1
        addql   #8,a0
        addql   #8,a1           | a0,a1 pointent sur mantisses i1,r1
        movw    a1@(-6),d1      | d1.w contient l(r1)
        subw    d0,d1           | d1.w contient l(r1)-le(i1)
        bpl     3$
                                | ici l(r1)<le(i1) : erreur
        movl    #truer2,sp@-
        jsr     _pari_err
                                | ici l(r1)>=le(i1)
3$:     subqw   #3,d0           | d0.w contient l(i1)-1 (compteur)
        addqb   #1,d2           | d2.b contient exp1+1 (derniers bits)
        andb    #31,d2          | d2.b contient exp1+1 mod 32
        bne     4$
                                | ici pas de shift a faire
8$:     movl    a1@+,a0@+
        dbra    d0,8$           | recopie des mantisses
        bra     truncf
                                | ici d2.b shifts a faire
4$:     moveq   #1,d6
        lsll    d2,d6
        subql   #1,d6           | masque de shift
        moveq   #0,d5
6$:     movl    a1@+,d3         | boucle de shift
        roll    d2,d3
        movl    d3,d4
        andl    d6,d4
        subl    d4,d3
        addl    d5,d4
        movl    d4,a0@+
        movl    d3,d5
        dbra    d0,6$
truncf: movl    a4,d0           | d0 pointe sur resultat
truncg: moveml  sp@+,d2-d6/a2-a4
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Fausse partie entiere (par valeur)                  #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : la zone pointee par a7@(8) contient trunc(n2)      #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mptruncz:movl  sp@(4),sp@-
        bsr     _mptrunc
        movl    sp@(12),sp@
        movl    d0,sp@-
        bsr     _mpaff
        movl    d0,a0
        addql   #8,sp
        bra     giv

#===================================================================#
#                                                                   #
#               Partie entiere ( max { n <= x} )                    #
#                                                                   #
#       entree : a7@(4) pointe sur n1 de type I ou R                #
#       sortie : d0 pointe sur i1 de type I (zone creee)            #
#       remarque : type S interdit                                  #
#                                                                   #
#===================================================================#

_mpent: link    a6,#0
        moveml  d2-d6/a2-a4,sp@-
        movl    a6@(8),a1       | a1 pointe sur n1
        cmpb    #1,a1@
        bne     1$
                                | ici n1 est de type I
        movw    a1@(6),d0       | d0.w recoit le1
        bsr     geti
        movl    a0,a4           | sauvegarde adresse resultat
        subqw   #2,d0
        addql   #4,a0
        addql   #4,a1
6$:     movl    a1@+,a0@+
        dbra    d0,6$
        bra     entf
                                | ici n1 est de type R
1$:     tstb    a1@(4)
        blt     2$
                                | ici n1 >= 0 (ent(n1)=trunc(n1))
        movl    a6@(8),sp@-     | empilage adresse n1
        bsr     _mptrunc
        movl    d0,a4           | sauvegarde adresse resultat
        addql   #4,sp
        bra     entf
                                | ici n1 < 0
2$:     movl    a1@(4),d3
        andl    #0xffffff,d3
        subl    #0x800000,d3    | d3.l contient exp1
        bpl     3$
                                | ici exp1 < 0 (ent(n1)=-1)
        moveq   #3,d0
        bsr     geti
        movl    a0,a4           | sauvegarde adresse resultat
        movl    #0xff000003,a0@(4)
        movl    #1,a0@(8)
        bra     entf
                                | ici exp1 >= 0
3$:     movl    _avma,a3        | ancien _avma dans var. locale
        movl    a6@(8),sp@-     | empilage adresse n1
        bsr     _mptrunc
        movl    d0,a4           | sauvegarde adresse res. provisoire
        addql   #4,sp           | depilage des parametres
        movl    d3,d1           | d1.l contient exp1
        lsrl    #5,d3           | d3.l contient exp1 div 32 = q
        andl    #31,d1          | d1.l contient exp1 mod 32 = r
        movl    a6@(8),a1
        lea     a1@(8,d3:l:4),a2| a2 pointe q+1eme lgmot mantisse
        movl    #0x80000000,d6  | d6.l contient 2^31
        lsrl    d1,d6           | d6.l  contient 2^(31-r)
        subql   #1,d6           | masque:0...01...1 avec r+1 zeros
        moveq   #0,d2
        movw    a1@(2),d2
        subql   #3,d2           | d2.l contient L1-1
        subl    d3,d2           | d2.l contient L1-1-q
        movl    a2@+,d5         | d5.l contient le q+1 eme lgmot
        andl    d6,d5
        beq     4$
        bra     5$
7$:     tstl    a2@+
4$:     dbne    d2,7$
        bne     5$
                                | ici tous les lgmots sont nuls
        bra     entf
                                | ici un au moins non nul
5$:     movl    a4,sp@-         | empilage trunc(n1)
        movl    #0xffffffff,sp@-| empilage -1
        bsr     _addsi          | calcul de trunc(n1)-1
        addql   #8,sp           | depilage
        movl    a4,a1           | a1 pointe sur trunc(n1)
        movl    a3,a4           | a4 contient _avma ancien
        movl    d0,a0           | a0 pointe sur resultat (res)
        movw    a0@(2),d0       | d0.w contient l(res)
        subqw   #1,d0           | d0.w contient l-1
8$:     movl    a1@-,a4@-
        dbra    d0,8$           | transfert du resultat ds pile PARI
        movl    a4,_avma        | mise a jour pile PARI
entf:   movl    a4,d0           | d0 pointe sur resultat
        moveml  sp@+,d2-d6/a2-a4
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#                       Partie entiere (par valeur)                 #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : la zone pointee par a7@(8) contient ent(n2)        #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpentz:movl    sp@(4),sp@-
        bsr     _mpent
        movl    sp@(12),sp@
        movl    d0,sp@-
        bsr     _mpaff
        movl    d0,a0
        addql   #8,sp
        bra     giv





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**             PROGRAMMES DE COMPARAISON                         **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Comparaison generale                        #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : d0.l contient -1 si n2<n1,0 si n2=n1,1 sinon.      #
#                d1,a0,a1 sont sauvegardes                          #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpcmp: link    a6,#0
        moveml  d1-d2/a1-a2,sp@-
        movl    a6@(8),a2
        movl    a6@(12),a1      | a1 et a2 pointent sur n1 et n2
        moveq   #0,d1
        movb    a2@,d2          | d2.b contient T2
        cmpb    a1@,d2
        ble     1$
                                | ici T2 > T1
        exg     a1,a2
        moveq   #1,d1
                                | ici T2 <= T1
1$:     movl    a1,sp@-
        movl    a2,sp@-
        cmpb    #1,a1@
        bne     2$
                                | ici T1 = T2 = I
        bsr     _cmpii
        bra     cmpf
                                | ici T1 = R
2$:     cmpb    #1,a2@
        bne     3$
                                | ici T1 = R et T2 = I
        bsr     _cmpir
        bra     cmpf
                                | ici T1 = T2 = R
3$:     bsr     _cmprr
cmpf:   addql   #8,sp
        tstb    d1
        beq     1$
        negl    d0
1$:     moveml  sp@+,d1-d2/a1-a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Comparaison : entier court et entier                #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0.l contient 1 si s2>i1,0 si s2=i1,-1 sinon       #
#                d1,a0,a1 sont sauvegardes                          #
#                                                                   #
#===================================================================#

_cmpsi: link    a6,#0
        moveml  d1-d4/a1,sp@-
        movl    a6@(12),a1      | a1 pointe sur i1
        movb    a1@(4),d1       | d1.b contient signe de i1 (si1)
        movb    d1,d4           | d4.b contient si1
        movb    #1,d3
        movl    a6@(8),d2       | d2.l contient s2
        bgt     1$              | si s2 > 0
                                | ici s2 <= 0
        bne     2$              | si s2 < 0
                                | ici s2 = 0
        movb    #0,d3
        bra     1$
                                | ici s2 < 0
2$:     movb    #-1,d3          | d3.b contient signe de s2 (ss2)
1$:     eorb    d3,d4           | d4.b contient :
                                | 0 si les deux nuls ou >0 ou <0
                                | >0 si un nul l'autre >0
                                | <0 si un nul autre<0,un<0 autre>0
        bpl     3$
                                | ici d4.b < 0
        moveq   #1,d0
        tstb    d3
        bpl     4$
                                | ici s2<0 et i1>0
        moveq   #-1,d0
4$:     bra     cmpsif
                                | ici d4.b >=0
3$:     cmpw    #3,a1@(6)
        ble     5$
                                | ici L1 >= 2
8$:     moveq   #-1,d0
        tstb    d1
        bpl     6$
        negl    d0
6$:     bra     cmpsif
                                | ici L1 <= 1
5$:     cmpw    #2,a1@(6)
        beq     7$
                                | ici L1 = 1
        tstl    d2
        bpl     9$
        negl    d2
9$:     moveq   #1,d0
        cmpl    a1@(8),d2
        bhi     10$
        bne     11$
        moveq   #0,d0
        bra     cmpsif
11$:    moveq   #-1,d0
10$:    tstb    d1
        bpl     cmpsif
        negl    d0
        bra     cmpsif
7$:     moveq   #1,d0
        tstb    d3
        bne     cmpsif
        moveq   #0,d0
cmpsif: moveml  sp@+,d1-d4/a1
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Comparaison : entier court et reel                  #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0.l contient 1 si s2>r1, 0 si s2=r1, -1 sinon     #
#                d1,a0,a1 sont sauvegardes                          #
#                                                                   #
#===================================================================#

_cmpsr: link    a6,#0
        moveml  d1-d4/a0-a2,sp@-
        movl    a6@(12),a1      | a1 pointe sur r1
        movb    a1@(4),d1       | d1.b contient sr1 (signe de r1)
        movb    d1,d4           | d4.b aussi
        movb    #1,d3
        movl    a6@(8),d2       | d2.l contient s2
        bgt     1$
        bne     2$
        movb    #0,d3
        bra     1$
2$:     movb    #-1,d3          | d3.b contient ss2 (signe de s2)
1$:     eorb    d3,d4           | d4.b contient 'signe'
        bpl     3$
                                | ici d4.b < 0
        moveq   #1,d0
        tstb    d3
        bpl     4$
        moveq   #-1,d0
4$:     bra     cmpsrf
                                | ici d4.b >= 0
3$:     tstb    d1
        bne     5$
                                | ici r1 = 0
        moveq   #1,d0
        tstb    d3
        bne     6$
                                | ici s2 = r1 = 0
        moveq   #0,d0
6$:     bra     cmpsrf
                                | ici r1 <> 0
5$:     movw    a1@(2),d0
        bsr     getr            | pour copie reelle de s2
        movl    a0,a2   | sauvegarde adresse copie
        movl    a0,sp@-         | empilage adresse copie
        movl    d2,sp@-         | empilage s2
        bsr     _affsr
        addql   #8,sp           | depilage
        movl    a1,sp@-         | empilage adresse r1
        movl    a0,sp@-         | empilage adresse copie
        bsr     _cmprr
        addql   #8,sp
        movl    a2,a0
        bsr     giv
cmpsrf: moveml  sp@+,d1-d4/a0-a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Comparaison : entier et entier court                #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient s1                                 #
#       sortie : d0.l contient le signe de i2 - s1                  #
#                aucun autre registre n'est affecte                 #
#                                                                   #
#===================================================================#

_cmpis: movl    sp@(4),sp@-
        movl    sp@(12),sp@-
        bsr     _cmpsi
        addql   #8,sp
        negl    d0
        rts

#===================================================================#
#                                                                   #
#               Comparaison : entier et entier                      #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0.l contient :1 si i2>i1,0 si i2=i1,-1 sinon      #
#                d1,a0,a1 sont sauvegardes                          #
#                                                                   #
#===================================================================#

_cmpii: link    a6,#0
        moveml  d1-d4/a1-a2,sp@-
        movl    a6@(8),a2
        movl    a6@(12),a1      | a1, a2 pointent sur i1, i2
        movb    a1@(4),d1       | d1.b contient si1
        movb    d1,d4
        movb    a2@(4),d2       | d2.b contient si2
        eorb    d2,d4
        bpl     1$
                                | ici d4.b < 0
        moveq   #1,d0
        tstb    d2
        bpl     cmpiif
        moveq   #-1,d0
        bra     cmpiif
                                | ici d4.b >= 0
1$:     movw    a1@(6),d1
        movw    a2@(6),d2       | d1.w et d2.w contiennent le1 et le2
        cmpw    d1,d2
        blt     3$
        beq     4$
                                | ici le2 > le1
6$:     moveq   #1,d0
        tstb    a1@(4)
        bpl     cmpiif
        moveq   #-1,d0
        bra     cmpiif
                                | ici le2 < le1
3$:     moveq   #-1,d0
        tstb    a2@(4)
        bpl     cmpiif
        moveq   #1,d0
        bra     cmpiif
                                | ici le2 = le1
4$:     cmpw    #2,d1
        bne     7$
        moveq   #0,d0
        bra     cmpiif
                                | ici i1 et i2 <> 0
7$:     movb    a1@(4),d3
        addql   #8,a1
        addql   #8,a2
        subqw   #3,d1
11$:    cmpml   a1@+,a2@+
        dbne    d1,11$
        bhi     8$
        beq     9$
        moveq   #-1,d0
        bra     10$
9$:     moveq   #0,d0
        bra     cmpiif
8$:     moveq   #1,d0
10$:    tstb    d3
        bpl     cmpiif
        negl    d0
cmpiif: moveml  sp@+,d1-d4/a1-a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Comparaison : entier et reel                        #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type R                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0.l contient :1 si i2>r1,0 si i2=r1,-1 sinon      #
#                d1,a0,a1 sont sauvegardes                          #
#                                                                   #
#===================================================================#

_cmpir: link    a6,#0
        moveml  d1-d4/a0-a3,sp@-
        movl    a6@(8),a2
        movl    a6@(12),a1      | a1 et a2 pointent sur r1 et i2
        movb    a1@(4),d1
        movb    d1,d4
        movb    a2@(4),d2
        eorb    d2,d4
        bpl     1$
        moveq   #1,d0
        tstb    d2
        bpl     2$
        moveq   #-1,d0
2$:     bra     cmpirf
                                | ici d4.b >= 0
1$:     tstb    d1
        bne     3$
        moveq   #1,d0
        tstb    d2
        bne     4$
        moveq   #0,d0
4$:     bra     cmpirf
                                | ici faire copie de i2 en type R
3$:     movw    a1@(2),d0       | allouer memoire pour copie de i2
        bsr     getr
        movl    a0,a3
        movl    a0,sp@-         | empiler adresse copie
        movl    a2,sp@-         | empiler adresse i2
        bsr     _affir
        addql   #8,sp           | depiler
        movl    a1,sp@-         | empiler adresse r1
        movl    a0,sp@-         | empiler adresse copie
        bsr     _cmprr
        addql   #8,sp           | depiler
        movl    a3,a0
        bsr     giv             | rendre copie
cmpirf: moveml  sp@+,d1-d4/a0-a3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Comparaison : reel et entier court                  #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) contient s1                                 #
#       sortie : d0.l contient le signe de r2 - s1                  #
#                aucun autre registre n'est affecte                 #
#                                                                   #
#===================================================================#

_cmprs: movl    sp@(4),sp@-
        movl    sp@(12),sp@-
        bsr     _cmpsr
        addql   #8,sp
        negl    d0
        rts

#===================================================================#
#                                                                   #
#               Comparaison : reel et entier                        #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) contient i1                                 #
#       sortie : d0.l contient le signe de r2 - i1                  #
#                aucun autre registre n'est affecte                 #
#                                                                   #
#===================================================================#

_cmpri: movl    sp@(4),sp@-
        movl    sp@(12),sp@-
        bsr     _cmpir
        addql   #8,sp
        negl    d0
        rts

#===================================================================#
#                                                                   #
#               Comparaison : reel et reel                          #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0.l contient :1 si r2>r1,0 si r2=r1,-1 sinon      #
#                d1,a0,a1 sont sauvegardes                          #
#                                                                   #
#===================================================================#

_cmprr: link    a6,#0
        moveml  d1-d5/a1-a2,sp@-
        movl    a6@(8),a2
        movl    a6@(12),a1      | a1 et a2 pointent sur r1 et r2
        movb    a1@(4),d1
        movb    d1,d4
        movb    a2@(4),d2
        eorb    d2,d4
        bpl     1$
                                | ici d4.b < 0
        moveq   #1,d0
        tstb    d2
        bpl     2$
        moveq   #-1,d0
2$:     bra     cmprrf
                                | ici d4.b >= 0
1$:     tstb    d1
        bne     3$
        moveq   #1,d0
        tstb    d2
        bne     4$
        moveq   #0,d0
4$:     bra     cmprrf
3$:     tstb    a2@(4)
        bne     5$
        moveq   #-1,d0
        bra     cmprrf
                                | ici r2 <> 0
5$:     moveq   #1,d0
        movw    a1@(2),d1
        movw    a2@(2),d2
        cmpw    d1,d2
        bpl     6$
        exg     d1,d2
        exg     a1,a2
        moveq   #-1,d0
6$:     tstb    a2@(4)
        bpl     7$
        negl    d0
7$:     movl    a1@(4),d5
        andl    #0xffffff,d5
        movl    a2@(4),d3
        andl    #0xffffff,d3
        cmpl    d5,d3
        bpl     8$
10$:    negl    d0
        bra     cmprrf
8$:     bne     cmprrf
        subw    d1,d2
        subqw   #3,d1
        addql   #8,a1
        addql   #8,a2
9$:     cmpml   a1@+,a2@+
        dbne    d1,9$
        bcs     10$
        beq     11$
        bra     cmprrf
12$:    tstl    a2@+
11$:    dbne    d2,12$
        bne     cmprrf
        moveq   #0,d0
cmprrf: moveml  sp@+,d1-d5/a1-a2
        unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES D'ADDITION                     **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Addition generale                           #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : d0 pointe sur n2 + n1 de type I ou R (zone creee)  #
#       interdit : type S                                           #
#       precision : voir les formules des routines specalisees      #
#                                                                   #
#===================================================================#

_mpadd: movl    sp@(4),a0
        movl    sp@(8),a1       | a1 et a0 pointent sur n1 et n2
        movb    a0@,d0
        movb    a1@,d1          | d1.b et d0.b contiennent T1 et T2
        cmpb    d1,d0
        ble     1$
                                | ici T2 > T1
        exg     a1,a0
        exg     d1,d0
        movl    a0,sp@(4)
        movl    a1,sp@(8)
                                | ici T2 <= T1
1$:     cmpb    #1,d1
        beq     _addii          | ici T1 = T2 = I
2$:     cmpb    #2,d0
        beq     _addrr          | ici T1 = T2 = R
        bra     _addir

#===================================================================#
#                                                                   #
#                       Addition (par valeur)                       #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#                a7@(12) pointe sur n3 de type I ou R               #
#       sortie : la zone pointee par a7@(12) contient n2+n1         #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpaddz:lea     _mpadd,a0
        bra     mpopz

                                | addition S+S=I ou R

_addssz:lea     _addss,a0
        bra     mpopz

                                | addition S+I=I ou R

_addsiz:lea     _addsi,a0
        bra     mpopz

                                | addition S+R=R sinon erreur

_addsrz:lea     _addsr,a0
        bra     mpopz

                                | addition I+I=I ou R

_addiiz:lea     _addii,a0
        bra     mpopz

                                | addition I+R=R sinon erreur

_addirz:lea     _addir,a0
        bra     mpopz

                                | addition R+R=R sinon erreur

_addrrz:lea     _addrr,a0
        bra     mpopz

#===================================================================#
#                                                                   #
#    Addition : entier court + entier court = entier                #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur s1+s2 de type I(zone cree)           #
#       remarque : s1 + s2 = s0 est interdit                        #
#                                                                   #
#===================================================================#

_addss: link    a6,#-2
        movl    d2,sp@-
        movl    a6@(8),d1
        movl    a6@(12),d2
        addl    d2,d1           | d1.l contient s2 + s1
        bne     1$
                                | ici d1.l=0
        bvs     2$
                                | ici s1+s2=0
	movl	_gzero,d0
        bra     addssg
                                | ici s1+s2=-2^32 (s1=s2=-2^31)
2$:     movw    #4,d0
        bsr     geti
        movl    #0xff000004,a0@(4)
        movl    #1,a0@(8)
        clrl    a0@(12)
        bra     addssf
                                | ici d1.l<>0
1$:     movw    #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        addl    a6@(8),d2       | repositionne les indicateurs
        bvs     3$
                                | ici pas d'overflow
        bmi     4$              | d1 donne bien le signe du resultat
        bra     5$
                                | ici overflow
3$:     bcc     5$              | le carry donne le signe du resultat
4$:     negl    d1
        movb    #0xff,a0@(4)
5$:     movl    d1,a0@(8)
addssf: movl    a0,d0           | d0 pointe sur resultat
addssg: movl    sp@,d2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Addition : entier court + entier = entier           #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur s2 + i1 de type I (zone creee)       #
#                                                                   #
#===================================================================#

_addsi: link    a6,#0
        moveml  d2-d4/a2,sp@-
        movl    a6@(12),a1      | a1 pointe sur i1
        movl    a6@(8),d2       | d2.l contient s2
        bne     1$              | si s2 <> 0
                                | ici s2 = 0 (i1 + s2 = i1)
        movw    a1@(6),d0
        bsr     geti            | allocation memoire pour resultat
        movl    a0,d4
        subqw   #2,d0           | compteur de boucle pour recopie de i1
        addql   #4,a0
        addql   #4,a1
2$:     movl    a1@+,a0@+       | recopie de i1
        dbra    d0,2$
        bra     addsif
                                | ici s2 <> 0
1$:     tstb    a1@(4)
        bne     3$              | si i1 <> 0
                                | ici i1 = 0 (i1 + s2 = s2)
        moveq   #3,d0
        bsr     geti            | allocation memoire pour resultat
        movl    a0,d4
        movl    #0x1000003,a0@(4)
        movl    d2,a0@(8)

        bpl     addsif
                                | ici s2 < 0
        movb    #0xff,a0@(4)
        negl    a0@(8)
        bra     addsif
                                | ici s2 et i1 <> 0
3$:     movw    a1@(6),d0       | d0.w contient le1
        bsr     geti
        movl    a0,d4
        movw    a1@(4),d1
        extl    d1              | d1.l contient signe de i1
        lea     a0@(0,d0:w:4),a0
        lea     a1@(0,d0:w:4),a2| a0 pointe fin du resultat;a2 fin de i1
        moveq   #0,d3
        subqw   #3,d0           | d0.w compteur boucle addition
        eorl    d2,d1           | comparaison signes i1 et s2
        bmi     susi            | si i1 * s2 < 0
                                | ici i1 * s2 > 0
        tstl    d2
        bpl     51$             | valeur absolue de s2
        negl    d2
51$:    addl    a2@-,d2
        bra     4$              | boucle d'addition
5$:     movl    d2,a0@-
        movl    a2@-,d2
        addxl   d3,d2
4$:     dbra    d0,5$
        bcc     6$              | ici retenue finale
        movl    d2,a0@-         | mise a jour dernier long mot
        moveq   #1,d0
        bsr     geti            | allocation un long mot supplementaire
        movl    a0,d4
        movl    a0@(4),a0@
        addqw   #1,a0@(2)       | mise a jour premier long mot code
        cmpw    #0x7fff,a0@(2)
        bls     7$
                                | ici debordement
        movl    #adder1,sp@-
        jsr     _pari_err
7$:     movw    a0@(2),a0@(6)   | mise longueur effective
	movw    a1@(4),a0@(4)   | signe du resultat
        movl    #1,a0@(8)       | mise a jour retenue finale
        bra     8$
                                | ici pas de retenue finale
6$:     movl    d2,a0@-         | mise a jour dernier long mot
        subqw   #8,a0
        movw    a0@(2),a0@(6)   | longueur effective
	movw    a1@(4),a0@(4)   | signe du resultat
8$:     movl    a0,d4
addsif: movl    d4,d0           | d0 pointe sur resultat
        moveml  sp@+,d2-d4/a2
        unlk    a6
        rts
                                | ici i1 * s2 < 0 : soustraction
susi:   movl    d2,d1           | d1.l recoit s2
        bpl     6$
        negl    d1              | d1.l recoit |s2|
6$:     movl    a2@-,d2
        subl    d1,d2           | amorcage de la soustraction
        bra     1$
                                | boucle de soustraction
2$:     movl    d2,a0@-
        movl    a2@-,d2
        subxl   d3,d2
1$:     dbra    d0,2$
        bcc     3$
                                | ici retenue finale:longueur resultat=3
        negl    d2
        movl    d2,a0@-
        subql   #8,a0           | a0 pointe sur resultat
        movw    #3,a0@(6)       | mise a jour longueur effective
        movb    a1@(4),d2
        negb    d2
        movb    d2,a0@(4)       | mise a jour signe (-|i1|)
        bra     addsif
                                | ici pas de retenue finale
3$:     tstl    d2
        beq     4$
                                | ici d2 <> 0
        movl    d2,a0@-
        movl    a1@(4),a0@-     | mise a jour second long mot code
        bra     addsif
                                | ici d2 = 0
4$:     movl    a1@(4),a0@-
        subqw   #1,a0@(2)
        cmpw    #2,a0@(2)
        bne     5$
                                | ici L1 = 1 ; le resultat est 0
        clrb    a0@
5$:     movl    a0@(-8),a0@-
        subqw   #1,a0@(2)
        movl    a0,d4
        addql   #4,_avma                | mise a jour pile PARI
        bra     addsif

#===================================================================#
#                                                                   #
#               Addition : entier + entier = entier                 #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur i2 + i1 de type I (zone creee)       #
#                                                                   #
#===================================================================#

_addii: link    a6,#0
        moveml  d2-d7/a2-a4,sp@-
        movl    a6@(8),a2       | a2 pointe sur i2
        movl    a6@(12),a1      | a1 pointe sur i1
        moveq   #0,d2
        moveq   #0,d1
        movw    a2@(6),d2
        movw    a1@(6),d1       | d1.w recoit le1 et d2.w recoit le2
        cmpw    d1,d2
        bcc     1$
        exg     a1,a2
        exg     d1,d2           | si L2 < L1 ,echanger a1,a2 et d1,d2
                                | ici L2 >= L1
1$:     tstb    a1@(4)
        bne     2$              | ici i1 = 0 : i1 + i2 = i2
        movw    a2@(6),d0
        bsr     geti            | allocation memoire pour recopie de i2
        subqw   #2,d0           | compteur de recopie
        movl    a0,a1
        addql   #4,a1
        addql   #4,a2
                                | boucle de recopie
3$:     movl    a2@+,a1@+
        dbra    d0,3$
        bra     addiif
                                | ici i1 <> 0 ( donc i2 <> 0)
2$:     movb    a1@(4),d3
        movb    a2@(4),d4
        eorb    d4,d3           | d3 contient signe de i2 * i1
        bmi     suii
                                | ici i2 * i1 > 0
        movw    d2,d0
        bsr     geti            | allocation memoire le2 longs mots
        lea     a0@(0,d0:w:4),a0| a0 pointe fin du resultat
        lea     a2@(0,d0:w:4),a2| a2 pointe fin de i2
        lea     a1@(0,d1:w:4),a1| a1 pointe fin de i1
        subw    d1,d2           | d2.w contient L2-L1
        subqw   #3,d1           | d1.w contient L1-1 (compteur)
        moveq   #0,d4
                                | ici premiere boucle d'addition
4$:     movl    a1@-,d0
        movl    a2@-,d5
        addxl   d5,d0
        movl    d0,a0@-
        dbra    d1,4$
        roxrw   d4,d0           | mise a jour dernier long mot
        bra     5$
                                | ici deuxieme boucle:propagation carry
6$:     movl    a2@-,d0
        addxl   d4,d0
        movl    d0,a0@-
        roxrw   d4,d0
5$:     dbcc    d2,6$
        bcs     7$              | si carry jusqu'a la fin
                                | ici pas de carry
        bra     8$
                                | ici troisieme boucle:recopie mantisse
9$:     movl    a2@-,a0@-
8$:     dbra    d2,9$
                                | ici pas de carry finale
        movl    a2@-,a0@-
        subql   #4,a0
        bra     addiif
                                | ici carry finale
7$:     movw    a2@(-2),d2
        addqw   #1,d2
        cmpw    #0x8000,d2
        bcs     10$
                                | ici debordement
        movl    #adder2,sp@-
        jsr     _pari_err
                                | ici demander 1 long mot en plus
10$:    moveq   #1,d0
        bsr     geti
        movl    #1,a0@(8)       | mise retenue
        movl    a0@(4),a0@
        movw    d2,a0@(2)       | mise a jour premier long mot code
        movl    a2@-,a0@(4)
        movw    d2,a0@(6)       | idem deuxieme long mot code
addiif: movl    a0,d0           | d0 pointe sur resultat
addiig: moveml  sp@+,d2-d7/a2-a4
        unlk    a6
        rts
                                | ici i2 * i1 < 0 : soustraction
suii:   movl    a1,a3
        movl    a2,a4           | a3,a4 pointent sur i1,i2
        subw    d1,d2           | d2.w contient L2-L1
        bne     1$
                                | ici L2=L1
        subqw   #3,d1           | d1.w  contient L1-1
        addql   #8,a3
        addql   #8,a4           | a3,a4 pointent debut mantisses i1,i2
2$:     cmpml   a3@+,a4@+
        dbne    d1,2$           | on compare |i1| et |i2|
        bhi     1$              | si |i2| > |i1|
                                | ici |i2| < |i1|
        bne     3$
                                | ici |i2| = |i1| : i2 + i1 = 0
	movl	_gzero,d0
        bra     addiig
                                | ici |i2| < |i1| : echanger i2 et i1
3$:     exg     a1,a2
                                | ici |i2| > |i1| (signe i2=signe resultat)
1$:     movw    a2@(6),d0
        bsr     geti            | allocation memoire le2 longs mots
        movw    a1@(6),d1       | d1.w  contient L1+2
        movl    a0,sp@-         | empilage adresse resultat
        movb    a2@(4),d7       | d7.b  contient signe resultat
        lea     a1@(0,d1:w:4),a1
        lea     a2@(0,d0:w:4),a2
        lea     a0@(0,d0:w:4),a0| a0,a1,a2 pointent fin resultat,i1,i2
        subl    d3,d3           | initialisation bit X
        subqw   #3,d1           | d1.w contient L1-1 (compteur)
                                | premiere boucle de soustraction
4$:     movl    a2@-,d0
        movl    a1@-,d5
        subxl   d5,d0
        movl    d0,a0@-
        dbra    d1,4$
        roxrw   d3,d0           | restauration du bit C
        bra     5$
                                | deuxieme boucle:propagation carry
6$:     movl    a2@-,d5
        subxl   d3,d5
        movl    d5,a0@-
        roxrw   d3,d0
5$:     dbcc    d2,6$
        bra     7$
                                | troisieme boucle:recopie fin i2
8$:     movl    a2@-,a0@-
7$:     dbra    d2,8$
        movl    sp@+,a0         | depilage adresse resultat
        movw    a0@(2),d1       | d1.w contient lon eff du resultat
        moveq   #0,d2
        movw    d1,d2           | d2.w idem
        addql   #8,a0           | a0 pointe mantisse resultat
9$:     tstl    a0@+
        dbne    d1,9$           | chasse aux '0' partie gauche resultat
        subql   #4,a0           | a0 pointe 1er long mot non nul
        movl    d1,a0@-         | mise a jour longueur effective
        movb    d7,a0@          | mise a jour signe
        movw    d1,a0@-         | mise a jour longueur totale
        movw    #0x100,a0@-     | mise a jour type
        subw    d1,d2
        lsll    #2,d2
        addl    d2,_avma                | mise a jour pile PARI
        bra     addiif

#===================================================================#
#                                                                   #
#               Addition : entier court + reel = reel               #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur s2 + r1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_addsr: link    a6,#-12         | 3 lgmots pour transformer s2 en type I
        movl    a6@(8),d1       | d1.l contient s2
        bne     1$
                                | ici s2 = 0
        movl    #0x1000002,a6@(-12)
        movl    #2,a6@(-8)
        bra     3$
                                | ici s2 <> 0
1$:     bmi     2$
        movl    #0x1000003,a6@(-12)
        movl    #0x1000003,a6@(-8)
        movl    d1,a6@(-4)
        bra     3$
                                | ici s2 < 0
2$:     movl    #0x1000003,a6@(-12)
        movl    #0xff000003,a6@(-8)
        negl    d1
        movl    d1,a6@(-4)
3$:     movl    a6@(12),sp@-
        pea     a6@(-12)
        bsr     _addir
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Addition : entier + reel = reel                     #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur i2 + r1 de type R (zone creee)       #
#       precision : si exp2>=exp1 , L = L1 + int((exp2-exp1)/32) + 1#
#                   si exp2<exp1  , L = L1                          #
#                   i2 est transforme en un reel                    #
#                                                                   #
#===================================================================#

_addir: link    a6,#-4          | var. locale pour copie i2 en r2
        moveml  d2-d3/a2,sp@-
        movl    a6@(8),a2
        movl    a6@(12),a1      | a1,a2 pointent sur r1,i2
        tstb    a2@(4)
        bne     1$
                                | ici i2 = 0 ( i2 + r1 = r1)
6$:     movw    a1@(2),d0
        bsr     getr
        movl    a0,a6@(-4)      | sauve adresse resultat
        addql   #4,a1
        addql   #4,a0
        subqw   #2,d0
                                | boucle de copie d'un reel
4$:     movl    a1@+,a0@+
        dbra    d0,4$
        bra     addirf
                                | ici i2 <> 0
1$:     tstb    a1@(4)
        bne     3$
                                | ici r1 = 0 (i2 + r1 = i2)
        movl    a1@(4),d1
        subl    #0x800000,d1
        asrl    #5,d1
        moveq   #0,d0
        movw    a2@(6),d0
        subl    d1,d0           | d0.l contient L2-[exp1/32]
        cmpl    #3,d0
        bcs     2$
        cmpl    #0x8000,d0
        bcc     2$
        bsr     getr
        movl    a0,a6@(-4)
        movl    a0,sp@-
        movl    a2,sp@-
        bsr     _affir          | le resultat est i2 en type R
        addql   #8,sp           | de longueur L2-[exp1/32]
        bra     addirf
                                | ici i2 et r1 <> 0
3$:     movl    a2@(8),d0
        bfffo   d0{#0:#0},d1    | d1.l recoit nb de shifts (=s)
        moveq   #0,d0
        movw    a2@(6),d0
        subqw   #2,d0
        lsll    #5,d0
        subl    d1,d0
        subql   #1,d0           | d0.l recoit 32*L2-s-1 = exp2
        moveq   #0,d3
        movw    a1@(2),d3       | d3.w recoit l1
        movl    a1@(4),d2
        andl    #0xffffff,d2
        subl    #0x800000,d2    | d2.l recoit exp1
        subl    d0,d2           | d2.l recoit exp1-exp2
        ble     5$
                                | ici exp1 > exp2
        lsrl    #5,d2           | d2.l recoit L3=[(exp1-exp2)/32]
        subl    d2,d3           | d3.l recoit L1-L3+2
        cmpl    #2,d3
        ble     6$              | si L1 <= L3 alors:r1+i2=r1
                                | ici L1 > L3
7$:     movl    _avma,sp@-      | empilage pile PARI
        movw    d3,d0
        bsr     getr            | allocation memoire L1-L3+2 lg mots
                                | pour ecrire i2 en type R
        movl    a0,sp@-         | empilage r2 (copie de i2)
        movl    a2,sp@-         | empilage i2
        bsr     _affir
        movl    a1,sp@          | empilage r1
        bsr     _addrr
        movl    d0,a0           | a0 pointe sur r2 + r1
        movw    a0@(2),d0       | d0.w contient lr (longueur resultat)
        subqw   #1,d0           | d0.w contient lr-1 (compteur pile)
        movl    sp@(4),a1       | a1 pointe sur r2
        addql   #8,sp           | depilage r1 et r2
        moveq   #0,d1
        movw    a1@(2),d1
        lsll    #2,d1           | d1.l contient 4*l2 (nb d'octets a
                                | desallouer dans pile PARI)

        movl    sp@+,a0         | a0 pointe sur ancien _avma
                                | boucle de transfert du resultat
8$:     movl    a1@-,a0@-
        dbra    d0,8$
        addl    d1,_avma        | mise a jour pile PARI
        movl    a0,a6@(-4)
        bra     addirf
                                | ici exp1 <= exp2
5$:     negl    d2
        lsrl    #5,d2           | d2.l recoit L3=[(exp2-exp1)/32]
        addw    d2,d3
        addqw   #1,d3           | d3.w recoit L1+L3+1
        cmpw    #0x8000,d3
        bcs     7$
                                | ici debordement
2$:     movl    #adder3,sp@-
        jsr     _pari_err
addirf: movl    a6@(-4),d0      | d0 pointe sur resultat
        moveml  sp@+,d2-d3/a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Addition : reel + reel = reel                       #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur r2 + r1 de type R (zone creee)       #
#       precision : L = inf ( L2 , L1 + [(exp2-exp1)/32])           #
#                       si exp2 >= exp1 (sinon echanger r1 et r2)   #
#                                                                   #
#===================================================================#

_addrr: link    a6,#-16
        moveml  d2-d7/a2-a4,sp@-
        movl    a6@(8),a2       | a2 pointe sur r2
        movl    a6@(12),a1      | a1 pointe sur r1
        tstb    a2@(4)
        bne     1$
                                | ici r2 = 0 (r2 + r1 = r1)
4$:     tstb    a1@(4)
        bne     22$
                                | ici r2=r1=0
        movl    a1@(4),d1
        cmpl    a2@(4),d1
        bgt     23$
        movl    a2@(4),d1       | d1.l contient sup(fexp1,fexp2)
23$:    moveq   #3,d0
        bsr     getr
        movl    a0,a6@(-8)
        movl    d1,a0@(4)
        clrl    a0@(8)
        bra     addrrf
                                | ici r2 = 0 et r1 <> 0
22$:    moveq   #0,d0
        movl    a2@(4),d2       | d2.l contient fexp2
        movl    a1@(4),d1
        andl    #0xffffff,d1    | d1.l contient fexp1
        subl    d2,d1           | d1.l recoit exp1-exp2
        bcc     24$
                                | ici exp2 > exp1
        moveq   #3,d0
        bsr     getr
        movl    a0,a6@(-8)      | le resultat est 0 avec exposant fexp2
        movl    a2@(4),a0@(4)
        clrl    a0@(8)
        bra     addrrf
                                | ici exp2 <= exp1
24$:    lsrl    #5,d1           | d1.l contient [(exp1-exp2)/32]
        movw    a1@(2),d0
        subqw   #2,d0           | d0.l contient L1
        cmpl    d1,d0
        ble     25$
        movl    d1,d0           | d0.l=inf(L1,[(e1-e2)/32])=L
        addql   #1,d0           | le resultat est r1 en longueur:
25$:    addql   #2,d0           | L1 si L1<=[(e1-e2)/32] ou
        bsr     getr
        movl    a0,a6@(-8)
        addql   #4,a1
        addql   #4,a0
        subqw   #2,d0
27$:    movl    a1@+,a0@+
        dbra    d0,27$
        bra     addrrf
                                | ici r2 <> 0
1$:     tstb    a1@(4)
        bne     3$
                                | ici r1 = 0 (r2 + r1 = r2)
        exg     a2,a1
        bra     22$
                                | ici r1 * r2 <> 0
3$:     movb    a1@(4),d3
        movb    a2@(4),d5
        eorb    d5,d3           | d3.b contient : 0 si r1 * r2 > 0
                                | et est negatif sinon
        movb    d3,a6@(-2)      | sauvegarde du 'signe'
        movl    a2@(4),d3
        andl    #0xffffff,d3    | d3.l contient fexp2=e2
        movl    a1@(4),d1
        andl    #0xffffff,d1    | d1.l contient fexp1=e1
        subl    d1,d3           | d3.l  contient exp2-exp1
        beq     5$              | si e2 = e1
        bcc     6$              | si e2 > e1
                                | ici e2 < e1
        exg     a1,a2
        negl    d3              | d3.l recoit e1-e2 > 0
                                | ici e2-e1 > 0
6$:     movw    d3,d4
        andw    #31,d4
        lsrl    #5,d3           | e2-e1=32*L3+r ; d4.w,d3.l recoit r,L3
        moveq   #0,d2
        movw    a2@(2),d2
        subqw   #2,d2           | d2.l recoit L2
        cmpl    d2,d3
        bcs     7$
                                | ici L3 >= L2 (r1 + r2 = r2)
        movw    a2@(2),d0
        bsr     getr
        movl    a0,a6@(-8)
        addql   #4,a2
        addql   #4,a0
        subqw   #2,d0
28$:    movl    a2@+,a0@+
        dbra    d0,28$
        bra     addrrf
                                | ici L3 < L2
7$:     moveq   #0,d1
        movw    a1@(2),d1
        subqw   #2,d1           | d1.l recoit L1
        movl    d3,d5
        addl    d1,d5           | d5.l recoit L1 + L3
        cmpl    d2,d5
        bcs     8$              | si L1 + L3 < L2
                                | ici L3 < L2 <= L1 + L3
        movb    #1,a6@(-4)      | a6@(-4) flag contenant :
                                | 0 si L1+L3 < L2 faire alors copie r1
                                | 1 si L3 < L2 <= L1+L3 et idem
                                | 2 si e1 = e2 et alors pas de copie
        movw    d2,d0
        addqw   #2,d0           | d0.w recoit l2
        bsr     getr            | allocation L2+2 lgmots pour resultat
        movl    a0,a6@(-8)      | adresse resultat dans var. locale
        movw    d2,d5
        subw    d3,d5           | d5.w contient L2 - L3
        movw    d5,d0
        addqw   #1,d0           | d0.w contient L2 - L3 + 1
        bsr     getr            | allocation L2-L3+1 pour copie r1 avec
                                | un unique longmot code
        subqw   #2,d0           | d0.w contient L2 - L3 - 1
        movw    a2@(2),d1
        lea     a2@(0,d1:w:4),a2| a2 pointe fin de r2
        bra     9$
                                | ici L1 + L3 < L2
8$:     clrb    a6@(-4)         | a6@(-4) mis a 0
        movw    d5,d0
        addqw   #3,d0           | d0.w contient L1 + L3 + 3
        bsr     getr            | allocation pour resultat
        movl    a0,a6@(-8)      | adresse resultat dans var. locale
        lea     a2@(0,d0:w:4),a2| a2 pointe ou necessaire !!
        movw    a1@(2),d5       | d5.w contient L1 + 2
        movw    d5,d0           | d0.w contient L1 + 2
        subqw   #2,d5           | d5.w contient L1
        bsr     getr            | allocation L1+2 pour copie r1 avec
                                | un  seul lgmot code
        subqw   #3,d0           | d0.w contient L1 - 1
9$:     movl    a0,a6@(-12)     | adresse copie r1 dans var. locale
        addql   #4,a0
        movl    a0,a3           | a0 et a3 pointent sur debut copie
        addql   #8,a1           | a1 pointe debut mantisse r1
29$:    movl    a1@+,a0@+
        dbra    d0,29$          | boucle copie r1
        tstw    d4              | test de r = nb de shifts
        bne     10$
                                | ici r = 0 ; pas de shift a faire
                                | a0 pointe fin copie r1
                                | a3 pointe debut mantisse copie r1
        moveq   #0,d7
        movw    a3@(-2),d7
        subqw   #1,d7           | d7.w contient longueur mantisse copie
        movw    d7,d2
        subqw   #1,d2           | d2.w = compteur boucle addition
        lea     a3@(0,d7:w:4),a3| a3 pointe fin copie r1
        movl    a3,a1           | a1 aussi
        bra     11$
                                | ici r <> 0 ; shift a faire
10$:    subqw   #1,d5
        movew   d5,d2           | d5.w et d2.w = compteur boucle shift
        movl    #-1,d6
        lsrl    d4,d6           | masque de shift:0...01...1; avec r '0'
        moveq   #0,d0
                                | boucle de shift de copie de r1
12$:    movl    a3@,d7
        rorl    d4,d7
        movl    d7,d1
        andl    d6,d1
        subl    d1,d7
        addl    d1,d0
        movl    d0,a3@+
        movl    d7,d0
        dbra    d5,12$
        movl    a3,a1
        tstb    a6@(-4)
        bne     11$             | si a6@(-4) <> 0
                                | ici a6@(-4) = 0
        movl    d0,a1@+
        addqw   #1,d2           | d2.w = compteur boucle addition
11$:    movl    a6@(-8),a0      | a0 pointe sur resultat
        moveq   #0,d1
        movw    a0@(2),d1
        lea     a0@(0,d1:w:4),a0| a0 pointe fin du resultat
        bra     14$
                                | ici e1 = e2
5$:     movb    #2,a6@(-4)      | a6@(-4) recoit 2
        movl    d1,a6@(-16)     | a6@(-16) recoit e1=e2 biaise
        movw    a1@(2),d0
        cmpw    a2@(2),d0
        bcs     15$
        movw    a2@(2),d0
15$:    bsr     getr            | allocation inf (l1,l2) pour resultat
        movl    a0,a6@(-8)      | adresse du resultat dans var. locale
        moveq   #0,d2
        movw    d0,d2
        movl    d2,d0
        subqw   #3,d2
        moveq   #0,d3
        movl    a2,a4
        movl    a1,a3
        lea     a0@(0,d0:w:4),a0| a0 pointe fin resultat
        lea     a1@(0,d0:w:4),a1| a1 pointe fin de r1 ou copie
        lea     a2@(0,d0:w:4),a2| a2 pointe fin de r2

                                | zone des boucles d'addition

                                | conditions initiales :
                                | a0 pointe fin resultat
                                | a1 pointe fin r1 ou copie
                                | a2 pointe fin r2
                                | d2.w contient L4-1
                                | d3.w contient L3 avec L3+L4=long.res.
14$:    subl    d4,d4           | initialisation bit X
        tstb    a6@(-2)         | test du signe de r1*r2
        bne     surr
                                | ici r1 * r2 > 0
                                | 1ere boucle d'addition
16$:    movl    a1@-,d1
        movl    a2@-,d5
        addxl   d5,d1
        movl    d1,a0@-
        dbra    d2,16$
        roxrw   d4,d0           | remise a jour du bit C
        bcc     17$             | si pas de carry
        bra     18$             | si carry
                                | 2eme boucle:propagation carry
19$:    movl    a2@-,d5
        addxl   d4,d5
        movl    d5,a0@-
        roxrw   d4,d0           | mise a jour bit C
18$:    dbcc    d3,19$
        bcs     20$             | si carry finale
        bra     17$
                                | 3eme boucle:recopie reste mantisse r2
30$:    movl    a2@-,a0@-
17$:    dbra    d3,30$
        movl    a2@-,a0@-       | mise signe et exposant:celui de r2
        cmpb    #2,a6@(-4)
        beq     addrrf          | si a6@(-4) = 2
                                | ici rendre copie de r1
        movl    a6@(-12),a0
        bsr     giv
        bra     addrrf
                                | ici carry finale
20$:    movl    a2@-,d1
        andl    #0xffffff,d1
        addql   #1,d1           | d1.l recoit fexp resultat
        cmpl    #0x1000000,d1
        blt     2$
                                | ici fexp>=2^24 : erreur
        movl    #adder4,sp@-
        jsr     _pari_err
                                | ici non debordement
2$:     cmpb    #2,a6@(-4)
        beq     13$
                                | ici rendre copie de r1
        movl    a0,a3
        movl    a6@(-12),a0
        bsr     giv
        movl    a3,a0
13$:    movl    d1,a0@(-4)
        movb    a2@,a0@(-4)     | mise a jour exp et sign resultat
        movw    a0@(-6),d2
        subqw   #3,d2           | compteur de shift
        movw    #-1,d0
        movw    d0,cc           | mise a 1 des bit x et c
31$:    roxrw   a0@+
        roxrw   a0@+            | boucle de mise de retenue finale et
        dbra    d2,31$          | shift de 1 vers la droite mantisse
addrrf: movl    a6@(-8),d0      | d0 pointe sur resultat
        moveml  sp@+,d2-d7/a2-a4
        unlk    a6
        rts
                                | ici faire une soustraction
                                | pour conditions initiales cf.plus haut
surr:   moveq   #0,d6
        movw    d2,d6
        movw    d2,d7
        addw    d3,d7
        addqw   #3,d7
        cmpb    #2,a6@(-4)
        bne     1$
                                | ici e2 = e1:comparer les mantisses
        addql   #8,a3
        addql   #8,a4
12$:    cmpml   a3@+,a4@+
        dbne    d2,12$
        bhi     1$              | si |r2| > |r1|
        bne     2$              | si |r2| < |r1|
                                | ici |r2| = |r1| et donc r2 + r1 = 0
        movl    a6@(-8),a0      | le resultat est 0 avec comme exposant
        moveq   #0,d2           | -32*inf(l1,l2)+e1
        movw    a0@(2),d2
        subqw   #2,d2
        lsll    #5,d2
        negl    d2
        addl    a6@(-16),d2     | ajouter e1 biaise
        bpl     15$
        movl    #adder5,sp@-    | underflow dans R+R
        jsr     _pari_err
15$:    cmpl    #0x1000000,d2
        blt     16$
                                | ici fexp>=2^24 : erreur overflow dans R+R
        movl    #adder4,sp@-
        jsr     _pari_err
16$:    bsr     giv
        moveq   #3,d0
        bsr     getr
        movl    a0,a6@(-8)
        movl    d2,a0@(4)
        clrl    a0@(8)
        bra     addrrf
                                | ici |r2| < |r1| : echanger r2 et r1
2$:     exg     a1,a2
                                | ici |r2| > |r1|
1$:     subw    d2,d6
        subl    d4,d4           | initialisation bit X
                                | 1ere boucle de soustraction
3$:     movl    a2@-,d0
        movl    a1@-,d5
        subxl   d5,d0
        movl    d0,a0@-
        dbra    d2,3$
        roxrw   d4,d0           | remise ajour bit C
        bra     4$
                                | 2eme boucle:propagation carry
5$:     movl    a2@-,d5
        subxl   d4,d5
        movl    d5,a0@-
        roxrw   d4,d0
4$:     dbcc    d3,5$
        bra     6$
                                | 3eme boucle:copie reste mantisse r2
13$:    movl    a2@-,a0@-
6$:     dbra    d3,13$
        moveq   #0,d3
        moveq   #-1,d2
        movw    d2,d3
14$:    tstl    a0@+
        dbne    d2,14$          | chasse aux '0' du resultat provisoire
                                | a0 pointe sur 1er lgmot non nul
        subw    d2,d3           | d3.w  contient de lgmots nuls
        addw    d6,d3
        subl    #12,a0          | a0 pointe sur resultat
        movl    a0,a6@(-8)
        movl    a0,a1           | a1 aussi
        cmpb    #2,a6@(-4)
        beq     7$              | si pas de copie faite
                                | ici rendre copie
        movl    a6@(-12),a0
        bsr     giv
7$:     moveq   #0,d0
        movw    d3,d0
        lsll    #2,d0           | d0.l = nb d'octets a 0 du result.
        addl    d0,_avma        | mise a jour pile PARI(rendre d3 lgmot)
        movl    a1,a0           | a0 pointe sur resultat final
        movw    #0x200,a0@
        subw    d3,d7
        movw    d7,a0@(2)       | mise a jour 1er lgmot code resultat
        lsll    #5,d3
        movl    a0@(8),d0
        bfffo   d0{#0:#0},d1    | d1.l contient nb de shifts=r
        lsll    d1,d0           | normalisation 1er lgmot mantisse
        addl    d1,d3
        lsll    #2,d6
        subl    d6,a2
        movl    a2@(-4),d2
        andl    #0xffffff,d2
        subl    d3,d2
        movl    d2,a0@(4)       | calcul et mise exposant resultat
        movb    a2@(-4),a0@(4)  | mise signe resultat
        tstb    d1
        bne     8$              | si r <> 0
        bra     9$              | si r = 0
8$:     moveq   #1,d6
        lsll    d1,d6
        subql   #1,d6           | masque de shift
        addql   #8,a1
        subqw   #3,d7           | d7.w  contient L-1
        bra     10$
                                | boucle de shift vers la gauche
11$:    movl  a1@(4),d2
        roll    d1,d2
        movl    d2,d3
        andl    d6,d3
        subl    d3,d2
        addl    d3,d0
        movl    d0,a1@+
        movl    d2,d0
10$:    dbra    d7,11$
        movl    d0,a1@
9$:     bra     addrrf





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES DE SOUSTRACTION                **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Soustraction generale                       #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : d0 pointe sur n2 - n1 de type I ou R (zone creee)  #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpsub: cmpb    #1,sp@(8)@
        bne     1$
        cmpb    #1,sp@(4)@
        beq     _subii
        bra     _subri
1$:     cmpb    #1,sp@(4)@
        beq     _subir
        bra     _subrr

#===================================================================#
#                                                                   #
#                       Soustraction (par valeur)                   #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#                a7@(12) pointe sur n3 de type I ou R               #
#       sortie : la zone pointee par a7@(12) contient n2 - n1       #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpsubz:lea     _mpsub,a0
        bra     mpopz

                                | soustraction S-S=I ou R

_subssz:lea     _subss,a0
        bra     mpopz

                                | soustraction S-I=I ou R

_subsiz:lea     _subsi,a0
        bra     mpopz

                                | soustraction S-R=R sinon erreur

_subsrz:lea     _subsr,a0
        bra     mpopz

                                | soustraction I-S=I ou R

_subisz:lea     _subis,a0
        bra     mpopz

                                | soustraction I-I=I ou R

_subiiz:lea     _subii,a0
        bra     mpopz

                                | soustraction I-R=R sinon erreur

_subirz:lea     _subir,a0
        bra     mpopz

                                | soustraction R-S=R sinon erreur

_subrsz:lea     _subrs,a0
        bra     mpopz

                                | soustraction R-I=R sinon erreur

_subriz:lea     _subri,a0
        bra     mpopz

                                | soustraction R-R=R sinon erreur

_subrrz:lea     _subrr,a0
        bra     mpopz

#===================================================================#
#                                                                   #
#       Soustraction : entier court - entier court = entier         #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a@7(8) contient s1 de type S                       #
#       sortie : d0 pointe sur s2 - s1 de type I (zone creee)       #
#       remarque : s2 - s1 = s0 est interdit                        #
#                                                                   #
#===================================================================#

_subss: link    a6,#-12
        movl    a6@(12),d1      | d1.l recoit s1
        negl    d1              | d1.l recoit -s1
        bvs     1$
                                | ici |s1| <= 2^31-1
        movl    d1,sp@-         | empilage -s1
        movl    a6@(8),sp@-     | empilage s2
        bsr     _addss          | calcul se s2+(-s1)
        bra     subssf
                                | ici s1 = -2^31
1$:     movl    #0x1000003,a6@(-12)
        movl    #0x1000003,a6@(-8)
        movl    #0x80000000,a6@(-4)| creation de 2^31 type entier
        pea     a6@(-12)        | empilage adresse de 2^31
        movl    a6@(8),sp@-     | empilage s2
        bsr     _addsi
subssf: unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Soustraction : entier - entier = entier             #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur i2 - i1 de type I (zone creee)       #
#                                                                   #
#===================================================================#

_subii: link    a6,#-4
        movl    a6@(12),sp@-    | empilage adresse i1
        movl    a6@(8),sp@-     | empilage adresse i2
        movl    a6@(12),a0      | a0 pointe sur i1
        negb    a0@(4)          | changer signe de i1
        movl    a0,a6@(-4)
        bsr     _addii
        movl    a6@(-4),a0
        negb    a0@(4)          | remettre signe de i1
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Soustraction : reel - reel = reel                   #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur r2 - r1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_subrr: link    a6,#-4          | voir commentaires de _subii
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        movl    a6@(12),a0
        negb    a0@(4)
        movl    a0,a6@(-4)
        bsr     _addrr
        movl    a6@(-4),a0
        negb    a0@(4)
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#       Soustraction : entier court - entier = entier               #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur s2 - i1 de type I                    #
#                                                                   #
#===================================================================#

_subsi: link    a6,#-4          | voir commentaires de _subii
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        movl    a6@(12),a0
        negb    a0@(4)
        movl    a0,a6@(-4)
        bsr     _addsi
        movl    a6@(-4),a0
        negb    a0@(4)
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Soustraction : entier court - reel = reel           #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur s2 - r1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_subsr: link    a6,#-4          | voir commentaires de _subii
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        movl    a6@(12),a0
        negb    a0@(4)
        movl    a0,a6@(-4)
        bsr     _addsr
        movl    a6@(-4),a0
        negb    a0@(4)
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#       Soustraction : entier - entier court = entier               #
#                                                                   #
#       entree : a7@(4) pointe sur i1 de type I                     #
#                a7@(8) contient s2 de type S                       #
#       sortie : d0 pointe sur i1 - s2 de type I (zone creee)       #
#                                                                   #
#===================================================================#

_subis: link    a6,#-12         | voir commentaires de _subss
        movl    a6@(8),sp@-
        movl    a6@(12),d1
        negl    d1
        bvs     1$
        movl    d1,sp@-
        bsr     _addsi
        bra     subisf
1$:     movl    #0x1000003,a6@(-12)
        movl    #0x1000003,a6@(-8)
        movl    #0x80000000,a6@(-4)
        pea     a6@(-12)
        bsr     _addii
subisf: unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Soustraction : entier - reel = reel                 #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur i2 - r1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_subir: link    a6,#-4          | voir commentaires de _subii
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        movl    a6@(12),a0
        negb    a0@(4)
        movl    a0,a6@(-4)
        bsr     _addir
        movl    a6@(-4),a0
        negb    a0@(4)
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Soustraction : reel - entier = reel                 #
#                                                                   #
#       entree : a7@(4) pointe sur r1 de type R                     #
#                a7@(8) pointe sur i2 de type I                     #
#       sortie : d0 pointe sur r2 - i1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_subri: link    a6,#-4          | voir commentaires de _subii
        movl    a6@(8),sp@-
        movl    a6@(12),sp@-
        movl    a6@(12),a0
        negb    a0@(4)
        movl    a0,a6@(-4)
        bsr     _addir
        movl    a6@(-4),a0
        negb    a0@(4)
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#       Soustraction : reel - entier court = reel                   #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur r2 - s1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_subrs: link    a6,#-12         | voir commentaires de _subss
        movl    a6@(8),sp@-
        movl    a6@(12),d1
        negl    d1
        bvs     1$
        movl    d1,sp@-
        bsr     _addsr
        bra     subsrf
1$:     movl    #0x1000003,a6@(-12)
        movl    #0x1000003,a6@(-8)
        movl    #0x80000000,a6@(-4)
        pea     a6@(-12)
        bsr     _addir
subsrf: unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES DE MULTIPLICATION              **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Multiplication generale                     #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : d0 pointe sur n2 * n1 de type I ou R (zone cree)   #
#       interdit : type S                                           #
#       precision : voir routines specialisees                      #
#                                                                   #
#===================================================================#

_mpmul: movl    sp@(4),a0
        movl    sp@(8),a1       | a1 et a0 pointent sur n1 et n2
        movb    a0@,d0
        movb    a1@,d1          | d1.b et d0.b contiennent T1 et T2
        cmpb    d1,d0
        ble     1$
                                | ici T2 > T1
        exg     a1,a0
        exg     d1,d0
        movl    a0,sp@(4)
        movl    a1,sp@(8)
                                | ici T2 <= T1
1$:     cmpb    #1,d1
        beq     _asmmulii          | ici T1 = T2 = I
2$:     cmpb    #2,d0
        beq     _mulrr          | ici T1 = T2 = R
        bra     _mulir

#===================================================================#
#                                                                   #
#               Multiplication (par valeur)                         #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#                a7@(12) pointe sur n3 de type I ou R               #
#       sortie : la zone pointee par a7@(12) contient n2*n1         #
#       interdit : type S                                           #
#                                                                   #
#===================================================================#

_mpmulz:lea     _mpmul,a0
        bra     mpopz

                                | multiplication S*S=I ou R

_mulssz:lea     _mulss,a0
        bra     mpopz

                                | multiplication S*I=I ou R

_mulsiz:lea     _mulsi,a0
        bra     mpopz

                                | multiplication S*R=R sinon erreur

_mulsrz:lea     _mulsr,a0
        bra     mpopz

                                | multiplication I*I=I ou R

_muliiz:lea     _asmmulii,a0
        bra     mpopz

                                | multiplication I*R=R sinon erreur

_mulirz:lea     _mulir,a0
        bra     mpopz

                                | multiplication R*R=R sinon erreur

_mulrrz:lea     _mulrr,a0
        bra     mpopz

#===================================================================#
#                                                                   #
#       Multiplication : entier court * entier court = entier       #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur s2 * s1 de type I (zone creee)       #
#                                                                   #
#===================================================================#

_mulss: link    a6,#-2
        moveml  d2-d4,sp@-
        movl    a6@(8),d2       | d2.l contient s2
        bne     1$
2$:     movl	_gzero,d0       | ici s2 ou s1 = 0
        bra     mulssg
                                | ici s2 <> 0
1$:     movl    d2,d4
        bpl     3$
        negl    d2              | d2.l contient |s2|
3$:     movl    a6@(12),d1      | d1.l contient s1
        beq     2$              | si s1=0
        eorl    d1,d4
        tstl    d1
        bpl     4$
        negl    d1              | d1.l contient |s1|
4$:     mulul   d1,d3:d2
        movw    #4,d0
        tstl    d3
        bne     5$
        movw    #3,d0           | d0 recoit 3 ou 4 pour allocation
5$:     bsr     geti
        movw    a0@(2),a0@(6)   | met long effect.
        movb    #1,a0@(4)       | met signe
        tstl    d4
        bpl     6$
        negb    a0@(4)
6$:     tstl    d3
        bne     7$
        movl    d2,a0@(8)
        bra     mulssf
7$:     movl    d3,a0@(8)
        movl    d2,a0@(12)
mulssf: movl    a0,d0
mulssg: moveml  sp@+,d2-d4
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#       Multiplication : entier court * entier = entier             #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur s2 * i1  de type I (zone creee)      #
#                                                                   #
#===================================================================#

_mulsi: link    a6,#0
        moveml  d2-d6/a2,sp@-
        movl    a6@(8),d2       | d2.l contient s2
        bne     1$
                                | ici s2 = 0 ou i1 = 0
2$:     movl	_gzero,d0
        bra     mulsig
                                | ici s2 <> 0
1$:     bpl     6$
        negl    d2              | d2 contient |s2|
6$:     movl    a6@(12),a1      | a1 pointe sur i1
        tstb    a1@(4)
        beq     2$              | si i1 = 0
                                | ici i1 <> 0 et s2 <> 0
        movw    a1@(6),d0       | d0.w contient le1
        bsr     geti
        lea     a0@(0,d0:w:4),a2| a2 pointe apres resultat (i0)
        lea     a1@(0,d0:w:4),a1| a1 pointe apres i1
        subqw   #3,d0
        moveq   #0,d6
        moveq   #0,d5           | initialisation retenue
                                | debut boucle multiplication
3$:     movl    a1@-,d4
        mulul   d2,d3:d4
        addl    d5,d4
        addxl   d6,d3
        movl    d4,a2@-
        movl    d3,d5
        dbra    d0,3$
        beq     5$
                                | ici retenue finale
        movw    #1,d0
        bsr     geti
        movw    a0@(6),d0
        addqw   #1,d0           | d0.w contient le(i0)
        bvc     4$
                                | ici debordement
        movl    #muler3,sp@-
        jsr     _pari_err
4$:     movw    d0,a0@(2)       | mise longueur
        movl    d5,a0@(8)       | mise retenue
5$:     movw    a0@(2),a0@(6)   | mise le(i0)
        movb    a1@(-4),a0@(4)
        tstl    a6@(8)
        bpl     mulsif
        negb    a0@(4)          | mise signe
mulsif: movl    a0,d0
mulsig: moveml  sp@+,d2-d6/a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Multiplication : entier court * reel = reel         #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur s2 * r1 de type R                    #
#                        de longueur L = L1 (zone creee)            #
#                                                                   #
#===================================================================#

_mulsr: link    a6,#-4
        moveml  d2-d6/a2,sp@-
        movl    a6@(8),d2       | d2.l contient s2
        bne     1$
                                | ici s2 = 0
	movl	_gzero,d0
        bra     mulsrf1
                                | ici s2 <> 0
1$:     movl    a6@(12),a1      | a1 pointe sur r1
        tstb    a1@(4)
        bne     2$
                                | ici r1 = 0
        moveq   #3,d0
        bsr     getr
        tstl    d2
        bpl     2$
        negl    d2
        bfffo   d2{#0:#0},d0
        movl    a1@(4),d1
        addl    #31,d1
        subl    d0,d1
        cmpl    #0x1000000,d1
        bcc     11$
        movl    d1,a0@(4)
        clrl    a0@(8)
        movl    a0,d0
        bra     mulsrf1
2$:     movw    a1@(2),d0
        bsr     getr            | allocation memoire pour resultat
        movl    a0,a6@(-4)      | sauvegarde adr. resultat ds var.locale
                                | ici s2 et r1 <> 0
        movl    d2,d4
        bpl     3$
        negl    d2              | d2.l contient |s2|
3$:     cmpl    #1,d2
        bne     4$
                                | ici |s2| = 1
        addql   #4,a0
        addql   #4,a1
        subqw   #2,d0
5$:     movl    a1@+,a0@+
        dbra    d0,5$           | copie de r1 dans resultat
        movl    a6@(-4),a0
        tstl    d4
        bpl     mulsrf
        negb    a0@(4)          | mise signe
        bra     mulsrf
                                | ici |s2| <> 1 et 0 , r1 <> 0
4$:     movb    a1@(4),a0@(4)
        tstl    d4
        bpl     6$
        negb    a0@(4)          | mise signe
6$:     lea     a0@(0,d0:w:4),a0| a0 pointe apres resultat
        lea     a1@(0,d0:w:4),a1| a1 pointe apres r1
        subqw   #3,d0           | d0.w contient L1-1
        movw    d0,d4           | d4.w idem
        movw    d4,d6
        moveq   #0,d1           | d1 a 0 pour les addx
        moveq   #0,d0           | initialisation retenue d0
                                | boucle de multiplication :
7$:     movl    a1@-,d5
        mulul   d2,d3:d5
        addl    d0,d5
        addxl   d1,d3
        movl    d5,a0@-
        movl    d3,d0           | nouvelle retenue d0
        dbra    d6,7$
        bfffo   d0{#0:#0},d1    | d1.l contient nb. de shifts
        lsll    d1,d0           | normalisation de d0
        moveq   #1,d6
        lsll    d1,d6
        subql   #1,d6           | masque de shift
        negb    d1
        addb    #32,d1
                                | boucle de shift
8$:     movl    a0@,d2
        rorl    d1,d2
        movl    d2,d3
        andl    d6,d3
        subl    d3,d2
        addl    d3,d0
        movl    d0,a0@+
        movl    d2,d0
        dbra    d4,8$
        movl    a6@(-4),a0      | a0 pointe sur resultat
        movl    a1@(-4),d0
        andl    #0xffffff,d0    | d0.l contient fexp1
        addl    d1,d0           | d0.l contient fexp resultat
        btst    #24,d0
        beq     9$
                                | ici debordement
11$:    movl    #muler2,sp@-
        jsr     _pari_err
9$:     movw    d0,a0@(6)       | mise exposant
        swap    d0
        movb    d0,a0@(5)
mulsrf: movl    a6@(-4),d0      | adresse du resultat
mulsrf1:moveml  sp@+,d2-d6/a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Multiplication : entier * entier = entier           #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur i2 * i1 de type I (zone creee)       #
#                                                                   #
#===================================================================#

_asmmulii: link    a6,#0
        moveml  d2-d7/a2-a4,sp@-
        movl    a6@(8),a1
        movl    a6@(12),a2      | a1,a2 pointent sur i1,i2
        movw    a1@(6),d1
        movw    a2@(6),d2       | d1.w, d2.w contient l1,l2
        cmpw    d1,d2
        bcc     1$
                                | ici l1>l2 : echanger i1 et i2
        exg     a1,a2
        exg     d1,d2           | maintenant l1<=l2
1$:     subqw   #2,d1           | d1 recoit L1
        bne     2$
                                | ici L1=0  <==> i1*i2 = 0
6$:     movl	_gzero,d0       | cree resultat nul de type I
        bra     muliig
                                | maintenant 1<=L1<=L2
2$:     movw    d2,d0           | d0 recoit l2
        addw    d1,d0           | d0 recoit l2 + L1 = L1 + L2 + 2
        bvc     3$
        movl    #muler1,sp@-
        jsr     _pari_err            | debordement
        bra     6$
3$:     bsr     geti            | allocation memoire pour resultat
        movw    d0,a0@(6)       | met long effect. (peut-etre 1 de trop)
        movb    a1@(4),d3
        movb    a2@(4),d4
        eorb    d4,d3
        addqb   #1,d3
        movb    d3,a0@(4)       | met signe du resultat
        lea     a0@(0,d0:w:4),a4| a4 pointe apres fin resultat = z
        lea     a1@(8,d1:w:4),a1| a1 pointe apres fin de i1 = y
        lea     a2@(0,d2:w:4),a3| a3 pointe apres fin de i2 = x
        subqw   #1,d1           | d1 recoit L1-1 compt bcl externe
        subqw   #3,d2           | d2 recoit L2-1 compt bcl interne
        movw    d2,d0           | sauvegarde compt interne dans d0
        moveq   #0,d7           | registre d7 fixe a 0
                                | Boucles de multiplication I*I :
| x=x1x2...xn multiplicande (x=i2,n=L2) pointe par a2 et a3
| y=y1...ym multiplicateur (y=i1,m=L1) pointe par a1
| z=z1z2...z(n+m) resultat pointe par a0 et a4
| a0 et a2 sont decrementes par la boucle interne (les valeurs initiales
| etant conservees dans a4 et a3)
#...................................................................#
                                | 1re boucle interne:initialise resultat
                                | (z recoit x*ym)
        movl    a3,a2           | a2 pointe apres xn
        movl    a4,a0           | a0 pointe apres z(n+m)
        movl    a1@-,d3         | d3 recoit ym
	subl	d4,d4           | d4 retenue k et X initialise a 0
m1:	movl	d4,d6		| nouvelle retenue dans d6
	movl	d3,d5		| dupliquer le multiplicateur
        mulul   a2@-,d4:d5      | d4:d5 recoit xi*ym (i=n,n-1,...,1)
        addxl   d5,d6
        addxl   d7,d4           | d4:d5 recoit xi*ym + k
        movl    d6,a0@-         | range z(i+m)
        dbra    d2,m1           | fin 1re bcl interne
        bra     bclf            | brancher fin de boucle externe
mext:   subql   #4,a4           | a4 pointe apres z(n+i)
        movl    a3,a2           | a2 pointe apres xn
        movl    a4,a0           | a0 pointe apres z(n+i)
        movl    d0,d2           | d2 recoit n-1 compteur bcl interne
        movl    a1@-,d3         | d3 recoit yj (j=m-1,m-2...1)
	subl	d4,d4           | d4 retenue k et X initialise a 0
mint:	movl	d4,d6		| nouvelle retenue dans d6
	movl	d3,d5		| dupliquer le multiplicateur
        mulul   a2@-,d4:d5      | d4:d5 recoit xi*yj (i=n,n-1,...,1)
        addxl   d5,d6
        addxl   d7,d4           | d4:d5 recoit xi*yj + k
        addl    d6,a0@-         | range partie basse de xi*yj+z(i+j)+k
        dbra    d2,mint         | fin de boucle interne
	addxl	d7,d4
bclf:   movl    d4,a0@-         | range derniere retenue
        dbra    d1,mext         | fin bcl externe
#...................................................................#
                                | derniere retenue = 0 ?
        beq     4$
        subql   #8,a0           | non : rien a faire
                                | a0 pointe sur resultat
        bra     muliif
                                | ici pas de retenue finale
4$:     subqw   #1,a0@(-2)
        subqw   #1,a0@(-6)      | rectifier longueurs
        movl    a0@(-4),a0@     | deplacer mots codes
        movl    a0@(-8),a0@-    | a0 pointe sur resultat
        addl    #4,_avma
muliif: movl    a0,d0
muliig: moveml  sp@+,d2-d7/a2-a4
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Multiplication : reel * reel = reel                 #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur r2 * r1 de type R (zone creee)       #
#                                                                   #
#       precision : L = inf ( L1 , L2 )                             #
#                                                                   #
#===================================================================#

_mulrr: link    a6,#-20          | variables locales pour murr aussi
        moveml  d2-d7/a2-a4,sp@-
        movl    a6@(8),a1       | a1 pointe sur r1
        movl    a6@(12),a2      | a2 pointe sur r2
        movb    a1@(4),d0
        andb    a2@(4),d0
        bne     munzr
                                | ici r1 ou r2 = 0
muzr:   moveq   #3,d0
        bsr     getr
        movl    a0,a6@(-8)
        movl    a1@(4),d1
        andl    #0xffffff,d1    | exposant de x1
        movl    a2@(4),d2
        andl    #0xffffff,d2    | exposant de y
        addl    d2,d1
        subl    #0x800000,d1
        cmpl    #0x1000000,d1
        bcs     1$
        movl    #muler4,sp@-    | debordement r*r
        jsr     _pari_err
1$:     tstl    d1
        bgt     2$
        movl    #muler5,sp@-    | underflow r*r
        jsr     _pari_err
2$:     movl    d1,a0@(4)
        clrl    a0@(8)
        bra     mulrrf

munzr:  movw    a2@(2),d0
	clrl	a6@(-12)	| Initialiser flag a 0
        cmpw    a1@(2),d0
        bls     1$
        movw    a1@(2),d0       | d0.w contient L+2=inf(L1,L2)+2
        exg     a1,a2           | a2 pointe sur le + court
	bra	2$
1$:	bne	2$
        lea     a1@(0,d0:w:4),a3 | a3 pointe sur x[L+1]
	movl	a3,a6@(-12)	| longueurs egales: flag egal adresse
	movl	a3@,a6@(-16)	| sauvegarde de x[L+1]
	clrl	a3@
2$:     bsr     getr
        movl    a0,a6@(-8)
        bsr     murr            | effectuer la multiplication
	tstl	a6@(-12)
	beq	mulrrf
	movl	a6@(-12),a3
	movl	a6@(-16),a3@	| remettre x[L+1]
mulrrf: movl    a6@(-8),d0      | adresse du resultat
        moveml  sp@+,d2-d7/a2-a4
        unlk    a6
        rts

#-------------------------------------------------------------------#
#       module interne de multiplication r0=r1*r2                   #
#               ( pour R*R et I*R)                                  #
#       entree : a1 et a2 pointent sur 2 reels                      #
#       r1,r2  non nuls avec L1>=L2=m                               #
#                a0 pointe sur une zone reelle de long l1           #
#       sortie : le produit r0 est mis a l'addresse a0              #
#                                                                   #
#-------------------------------------------------------------------#

| notation : r1 = x = x1x2...xmx(m+1)...  multiplicande
|            r2 = y = y1y2...ym           multiplicateur
|       ( le lgmot x(m+1) peut ne pas exister ! ( le1 >= le2 = m ) )
|             z = z0z1z2...zmz(m+1) resultat.
|       ( z0=0 ou 1 et z(m+1) a jeter)

murr:   movl    a1,a3
        lea     a3@(12),a3      | a3 pointe sur x2 (2me lgmot mant.x)
#       movw    a2@(2),d0       | d0.w=L2=m long commune des mantisses (mis a l'appel!)
        lea     a2@(0,d0:w:4),a2| a2 pointe apres ym
        lea     a0@(0,d0:w:4),a0| a0 pointe apres zm
        movl    a0@,a6@(-4)     | on sauvegarde le lg mot suivant z
        clrl    a0@+            | z(m+1) recoit 0,a0 pointe apres z(m+1)
        subqw   #3,d0           | d0 recoit m-1
        movl    d0,a6@(-20)     | sauvegarde m-1 compt. bcl externe
        clrw    d3              | d3=0,val initiale compt bcl interne
                                | Boucles triangulaires mult. R*R
#...................................................................#
bext:   movl    a0,a4           | a4 pointe apres z(m+1)
        movl    a3,a1           | a1 pointe sur x(j+1) (j=1,2...m)
        movw    d3,d2           | d3 recoit m-j compt bcl interne
        movl    a2@-,d4         | d4 recoit yj
        movl    a3@+,d5         | d5 recoit x(j+1)
	subl	d1,d1		| d1 a zero ainsi que bit X
        mulul   d4,d7:d5        | init.retenue d7(ignorer poids faible)
bint:   movl	d7,d6		| sauvegarder nouvelle retenue
	movl	d4,d5		| dupliquer multiplicateur
        mulul   a1@-,d7:d5      | d7:d5 recoit xi*yj
        addxl   d5,d6
        addxl   d1,d7           | d7:d5 recoit xi*yj + k
        addl    d6,a4@-         | nouveau z(i+j)
        dbra    d2,bint
	addxl	d1,d7
        movl    d7,a4@-         | range derniere retenue
        addqw   #1,d3           | augmente de 1 long bcl interne
        dbra    d0,bext         | fin bcl externe
#...................................................................#
        movl    a1@(-4),d1      | a1 pointe sur x1 (1er mot mant de x)
        andl    #0xffffff,d1    | exposant de x1
        movl    a2@(-4),d2      | a2 pointe sur y1
        andl    #0xffffff,d2    | exposant de y
        addl    d2,d1
        subl    #0x800000,d1
        tstl    a4@             | a4 pointe sur z1 : z normalise ?
        bpl     1$
        addl    #1,d1           | ici mantisse normalisee
        bra     2$
                                | ici il faut shifter de 1 a gauche
1$:     movl    a0,a4           | a4 pointe apres z(m+1)
        subqw   #2,a4
	movl	a6@(-20),d0	| recuperer m-1
        roxlw   a4@-            | initialise le carry
5$:     roxlw   a4@-            | shift par mots (d0 compteur=m-1)
        roxlw   a4@-
        dbra    d0,5$           | boucle de shift
2$:     cmpl    #0x1000000,d1
        bcs     3$
        movl    #muler4,sp@-    | debordement r*r
        jsr     _pari_err
3$:     tstl    d1
        bgt     4$
        movl    #muler5,sp@-    | underflow r*r
        jsr     _pari_err
4$:     movl    d1,a4@-         | range exposant
        movb    a1@(-4),d1
        movb    a2@(-4),d2      | signes
        eorb    d2,d1
        addqb   #1,d1
        movb    d1,a4@          | range signe resultat
        movl    a6@(-4),a0@(-4) | remet en place mot sous z(m+1)
murrf:  rts

#===================================================================#
#                                                                   #
#               Multiplication : entier * reel = reel               #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointeur sur i2 * r1 de type R (zone creee)     #
#                                                                   #
#===================================================================#

_mulir: link    a6,#-20
        moveml  d2-d7/a2-a4,sp@-
        movl    a6@(8),a2       | a2 pointe sur i2
        tstb    a2@(4)
        bne     1$
                                | ici i2 = 0
	movl	_gzero,d0
        bra     mulirf1
                                | ici i2 <> 0
1$:     movl    a6@(12),a1      | a1 pointe sur r1
        tstb    a1@(4)
        bne     2$
                                | ici r1 = 0
        moveq   #3,d0
        bsr     getr
        movw    a2@(6),d0
        lsll    #5,d0
        bfffo   a2@(8){#0:#0},d1
        subl    d1,d0
        subl    #65,d0
        addl    a1@(4),d0
        cmpl    #0x1000000,d0
        bcs     3$
        movl    #muler6,sp@-    | overflow I*R, R = 0
        jsr     _pari_err
3$:     movl    d0,a0@(4)
        clrl    a0@(8)
        movl    a0,d0
        bra     mulirf1
                                | ici i2 <> 0 et r1<> 0
2$:     movw    a1@(2),d0
        bsr     getr            | allocation memoire pour resultat
        movl    a0,a6@(-8)      | sauvegarde adresse resultat
	addqw	#1,d0
        bsr     getr            | allocation mem pour conversion i2->r2
        movl    a0,a7@-
        movl    a2,a7@-
        bsr     _affir
        addql   #4,sp
        movl    a7@,a2          | a2 recoit adr de r2=i2 (reste en pile)
        movl    a6@(-8),a0      | a0 recoit addresse du resultat
	exg	a1,a2		| Il faut que a2 soit le plus court!
	movw	a2@(2),d0	| Mettre la plus petite longueur dans d0 pour murr
        bsr     murr
        movl    a7@+,a0
        bsr     giv
mulirf: movl    a6@(-8),d0
mulirf1:moveml  sp@+,d2-d7/a2-a4
        unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**             PROGRAMMES DE DIVISION AVEC RESTE                 **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#               Division avec reste (par valeur)                    #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I                     #
#                a7@(8) pointe sur n1 de type I                     #
#                a7@(12) pointe sur n3 de type I                    #
#                a7@(16) pointe sur n4 de type I                    #
#       sortie : la zone pointee par a7@(12) contient n2 / n1       #
#                la zone pointee par a7@(16) contient le reste (du  #
#                signe du dividende)                                #
#       interdit : type S et R                                      #
#                                                                   #
#===================================================================#

_mpdvmdz:lea    _asmdvmdii,a0
        bra     mpopii

                                | division avec reste S/S=(I et I)
                                | sinon erreur

_dvmdssz:lea    _dvmdss,a0
        bra     mpopii

                                | division avec reste S/I=(I et I)
                                | sinon erreur

_dvmdsiz:lea    _dvmdsi,a0
        bra     mpopii

                                | division avec reste I/S=(I et I)
                                | sinon erreur

_dvmdisz:lea    _dvmdis,a0
        bra     mpopii

                                | division avec reste I/I=(I et I)
                                | sinon erreur

_dvmdiiz:lea    _asmdvmdii,a0
        bra     mpopii

#===================================================================#
#                                                                   #
#Division avec reste : entier court / entier court =(entier,entier) #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient s1 de type S                       #
#       sortie : a7@(12) pointe sur l'adresse du futur reste        #
#                d0 pointe sur s2 div s1 de type I                  #
#                le reste est du signe de s2 (zone creee)           #
#                                                                   #
#===================================================================#

_dvmdss:link    a6,#0
        movl    d2,sp@-
        movl    a6@(12),sp@-    | empilage s1
        movl    a6@(8),sp@-     | empilage s2
        bsr     _divss
dmd:    addql   #8,sp
        tstl    d1
        bne     1$
                                | ici reste nul
	movl	_gzero,a0
        bra     dvmdssf
                                | ici reste non nul
1$:     movl    d0,d2
        moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        tstl    d1
        bpl     2$
        negl    d1
        movb    #-1,a0@(4)
2$:     movl    d1,a0@(8)
        movl    d2,d0
dvmdssf:movl    a6@(16),a1
        movl    a0,a1@
        movl    sp@,d2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#   Division avec reste : entier court / entier = (entier,entier)   #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#                a7@(12) pointe sur l'adresse du futur reste        #
#       sortie : d0 pointe sur s2 div i1 de type I ;                #
#                reste du signe de s2 (zones creees)                #
#                                                                   #
#===================================================================#

_dvmdsi:movl    a7@(8),sp@-
        movl    a7@(8),sp@-
        bsr     _divsi
dmdi:   addql   #8,sp
        tstl    d1
        bne     1$
                                | ici reste nul
	movl	_gzero,sp@(12)@
	rts
                                | ici reste non nul
1$:     movl    d0,a1           | sauvegarde adresse quotient
        moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        tstl    d1
        bpl     2$
        negl    d1
        movb    #-1,a0@(4)
2$:     movl    d1,a0@(8)
3$:     movl    a1,d0
        movl    a0,sp@(12)@
        rts

#===================================================================#
#                                                                   #
#   Division avec reste : entier / entier court = (entier,entier)   #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient s1 de type S                       #
#                a7@(12) pointe sur l'adresse du futur reste        #
#       sortie : d0 pointe sur i2 div s1 de type I                  #
#                reste de type I du signe de s1 (zones creees)      #
#                                                                   #
#===================================================================#

_dvmdis:movl    a7@(8),sp@-
        movl    a7@(8),sp@-
        bsr     _divis
        bra     dmdi

#===================================================================#
#                                                                   #
#       Division avec reste : entier / entier = (entier,entier)     #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I (dividende)         #
#                a7@(8) pointe sur i1 de type I (diviseur)          #
#                a7@(12) contient un pointeur sur le reste si l'on  #
#                veut a la fois q et r, 0 si l'on ne veut que le    #
#                quotient, -1 si l'on ne veut que le reste          #
#       sortie : d0 pointe sur q si celui-ci est attendu, et sinon  #
#                sur r. a7@(12) pointe sur r si q et r sont attendus#
#                (toutes les zones sont creees)                     #
#       remarque : il s'agit de la 'fausse division' ; le reste est #
#                 du signe du dividende                             #
#                                                                   #
#                                                                   #
#       variables locales (etat pile apres link):                   #
#  -16 -14 -12 -10 -8  -6   -4    a6    4    8    12   16           #
#  +---+---+---+---+---+---+------+----+----+----+----+----+        #
#   n-m  k sgnq sgnr n   m  ad(q,r)      ret  i2   i1 ^r/0/-1       #
#                                                                   #
#===================================================================#

_asmdvmdii:link    a6,#-32
        moveml  d2-d7/a2-a4,sp@-
        movl    a6@(12),a1      | a1 pointe sur le diviseur i1
        movw    a1@(6),d1       | d1.w contient le1
        cmpw    #2,d1
        bne     dv1
                                | ici i1 = 0
        movl    #dvmer1,sp@-
dvmerr: jsr     _pari_err
                                | ici i1 <> 0
dv1:    movl    a6@(8),a2       | a2 pointe sur dividende i2
        movw    a2@(6),d2       | d2.w contient le2
        cmpw    #2,d2
        bne     dv3
                                | ici quotient=reste=0
dv2:    movl    a6@(16),d3
        cmpl    #-1,d3
        beq     1$
                                | ici quotient attendu (q=0)
	movl	_gzero,d0
1$:     tstl    d3
        beq     dvmiif
                                | ici reste attendu (r=0)
	movl	_gzero,a0
        btst    #0,d3           | test si fonction mod
        bne     2$
        movl    d3,a1           | d3 pointe sur l'adr. du reste
        movl    a0,a1@
        bra     dvmiif
2$:     movl    a0,d0
        bra     dvmiif
                                | ici i2 et i1 <> 0
dv3:    movw    d2,d0           | le2
        subw    d1,d0           | d0.w contient L2-L1
        bcc     dv4
                                | ici q=0 , r=i2
        movl    a6@(16),d3
        cmpl    #-1,d3
        beq     1$
                                | quotient attendu soit q=0
	movl	_gzero,d0
1$:     tstl    d3
        beq     dvmiif
                                | reste attendu soit r=i1
        movl    d0,d1
        movw    d2,d0
        bsr     geti
        movl    a0,a1
        subqw   #2,d0
        addql   #4,a0
        addql   #4,a2
2$:     movl    a2@+,a0@+
        dbra    d0,2$
        cmpl    #-1,d3
        beq     3$
        movl    d3,a0
        movl    a1,a0@
        movl    d1,d0
        bra     dvmiif
3$:     movl    a1,d0
        bra     dvmiif
                                | ici L2 >= L1
dv4:    movb    a1@(4),d3       | d3.b contient signe de i1
        movb    a2@(4),d4       | d4.b contient signe de i2
        eorb    d4,d3
        addqb   #1,d3           | d4.b contient signe de q
        movb    d3,a6@(-12)     | sauvegarde signe de q
        movb    d4,a6@(-10)     | sauvegarde signe de r
        movl    _avma,a6@(-20)  | sauvegarde _avma initial
        movw    d2,d0           | d0 recoit l2
        bsr     geti            | allocation memoire de travail :
                                | on va y former q0q1...q(n-m)r1r2...rm
                                | les memoires provisoires ne seront pas
                                | rendues par giv:on ecrase mot code
        movl    a0,a6@(-4)      | sauvegarde addresse zone de travail
        subqw   #2,d1
        subqw   #2,d2
        movw    d1,a6@(-6)      | sauvegarde L1 (=m)
        movw    d2,a6@(-8)      | sauvegarde L2 (=n)
        movw    d2,a6@(-16)
        subw    d1,a6@(-16)     | n-m dans a6@(-16)
        addql   #8,a2
        addql   #8,a1
        movl    a1@,d3          | d3.l=y1 (1er lgmot du diviseur i1)
        subqw   #1,d2           | d2 recoit n-1
        subqw   #1,d1           | d1 recoit m-1
        bne     divlon
                                | ici division simple (m = 1)
divsim: clrl    d4
1$:     movl    a2@+,d5
        divul   d3,d4:d5
        movl    d5,a0@+
        dbra    d2,1$
        movl    d4,a0@          | reste mis derriere quotient
        movl    a0,a2           | a2 pointe sur reste
        clrw    a6@(-14)        | on n'a pas fait de shift
        bra     ranger
                                | ici division longue (m > 1)
divlon: bfffo   d3{#0:#0},d4    | d4 recoit nb de shift pour normaliser
        movw    d4,a6@(-14)     | sauvegarde du nb. de shifts = k
        bne     1$
                                | ici pas de normalisation
        movl    a0,a4
        movl    #0,a4@+         | met a 0 1er lgmot soit x0
4$:     movl    a2@+,a4@+       | recopie x1x2...xn
        dbra    d2,4$
        movl    a0,a2           | a2 pointe sur x0,a4 pointe apres xn
        lea     a1@(4,d1:w:4),a3| a1 pointe sur y1,a3 pointe apres ym
        bra     nosh
                                | ici on normalise le diviseur i1=y
                                | et on decale autant le dividende:
1$:     lsll    d4,d3           | normalisation de y1
        movw    a6@(-6),d0      | on demande m lgmots
        bsr     geti            | allocation pour copie normalisee de y
        moveq   #1,d6
        lsll    d4,d6
        subql   #1,d6           | masque de shift
        movl    a0,a3
        subqw   #1,d0           | d0 compt. mis a m-1
        addql   #4,a1           | a1 pointe sur y2 2me lg mot diviseur
        bra     3$
2$:     movl    a1@+,d1         | boucle shift vers la gauche ds copie
        roll    d4,d1
        movl    d1,d5
        andl    d6,d1
        addl    d1,d3
        movl    d3,a3@+
        subl    d1,d5
        movl    d5,d3
3$:     dbra    d0,2$
        movl    d3,a3@+
        movl    a0,a1           | a1 pointe sur 1er lgmot y1 normalise
                                | a3 pointe apres ym
                                | transfert avec shift du dividende:
        movl    a6@(-4),a4      | a4 pointe sur zone de travail
        moveq   #0,d3
        movw    a6@(-8),d0
        subqw   #1,d0           | d0 recoit n-1 compteur
5$:     movl    a2@+,d1         | boucle de shift du dividende i2
        roll    d4,d1           | sur place
        movl    d1,d5
        andl    d6,d1
        addl    d1,d3
        movl    d3,a4@+
        subl    d1,d5
        movl    d5,d3
        dbra    d0,5$
        movl    d3,a4@
        movl    a6@(-4),a2      | a2 pointe sur x0 ;(a4 pointe sur xn)
nosh:   movw    a6@(-6),d6      | d6 recoit m
        lea     a2@(4,d6:w:4),a4| a4 pointe apres xm
        subqw   #1,d6           | d6 recoit m-1 compteur bcls internes
        movw    a6@(-16),d7     | d7 recoit n-m compteur bcl externe
#-------------------------------------------------------------------#
                                | boucles de division I / I :
        | a1 pointe sur y1, a3 pointe apres ym : diviseur y1y2...ym
        | a2 pointe sur x0, a4 pointe apres xm : dividende x0x1...xn
        | d7 contient n-m compt. boucle externe
        | d6 contient m compt. boucles internes (n>=m>=2)
        | la zone x0x1...xn recoit q0q1...q(n-m)r1r2...rm

bclext: movl    a1@,d0          | d0 recoit y1 (1er lgmot diviseur)
        cmpl    a2@,d0          | xi = y1 ? (i=0,1...n)
        bne     1$
        moveq   #-1,d1          | oui: essayer q=2^32-1
        addl    a2@(4),d0       | calcul du reste
                                | r=xix(i+1) mod y1 = xi+x(i+1)
        bcs     4$              | si r>=2^32 , q est ok
        movl    d0,d2           | sinon d2 recoit r
        bra 2$                  | rejoindre cas general
1$:     movl    a2@,d2          | si xi<y1 :
        movl    a2@(4),d1       | d2:d1 recoit xix(i+1)
        divul   d0,d2:d1        | d1 recoit q = xix(i+1) div y1
                                | d2 recoit r = xix(i+1) mod y1
2$:     movl    a1@(4),d3       | d3 recoit y2
        mulul   d1,d4:d3        | d4:d3 recoit q*y2
        subl    a2@(8),d3
        subxl   d2,d4           | d4:d3 recoit q*y2-(r,x(i+2))
        bls     4$              | si <= 0 alors q ok
3$:     subql   #1,d1           | sinon diminuer q
        subl    a1@(4),d3       | corriger reste partiel:
        subxl   d0,d4           | d3:d4 recoit d3:d4-y1y2
        bhi     3$              | tant que q*y1y2>xix(i+1)x(i+2)
                                | recommencer q recoit q-1
                                | ici q*y1y2 <= xix(i+1)x(i+2)
                                | on va former le nouveau reste
                                | en remplacant x(i+1)...x(i+m) par
                                | x(i+1)...x(i+m) - q*y1...ym
4$:     movw    d6,d0           | d0 recoit m-1 compteur
        movl    a3,a1           | a1 pointe apres ym
        movl    a4,a2           | a2 pointe apres x(i+m)
        moveq   #0,d2           | d2 fixe a 0 pour les addxl
        subl    d3,d3           | d3 recoit k retenue initialisee a 0 et X=0
5$:     movl    a1@-,d5         | d5 recoit x(i+j) j=m,m-1,...,1
        mulul   d1,d4:d5
        addxl   d3,d5
        addxl   d2,d4
        subl    d5,a2@-         | nouvel x(i+j)
        movl    d4,d3
        dbra    d0,5$
	addxl	d2,d3
        subl    d3,a2@(-4)      | soustrait derniere retenue
        bcc     6$              | si pas carry q=qi est definitif
        subql   #1,d1           | sinon encore 1 de trop
        movw    d6,d0           | repositionner compteur m-1
        movl    a3,a1
        movl    a4,a2           | repositionner pointeurs
7$:     addxl   a1@-,a2@-
        dbra    d0,7$           | boucle de remise a jour du reste
                                | il y a forcement carry final a ignorer
6$:     movl    d1,a2@(-4)      | qi est range sur l'ancien xi
        addql   #4,a4           | a4 pointe apres x(i+m+1)
        dbra    d7,bclext       | boucler pour q0q1...q(n-m)
                                | fin des boucles de division I/I
                                | a2 pointe apres q(n-m),ie sur r1
#-------------------------------------------------------------------#
                                | rangement des resultats

ranger: clrl    a6@(-28)
        clrl    a6@(-32)
        movl    _avma,a6@(-24)  | actuel _avma
        movl    a6@(-20),d7     | _avma initial
        subl    _avma,d7        | nb d'octets memoire provisoires
                                | offset:ajouter aux addresses fournies
        movl    a6@(16),d3
        cmpl    #-1,d3
        beq     rngres
                                | ici quotient attendu
        movl    a6@(-4),a0      | a0 pointe sur q0
        movw    a6@(-16),d0     | d0 recoit n-m
        movw    d0,d1
        addqw   #2,d0
        tstl    a0@
        beq     1$
        addqw   #1,d0
1$:     bsr     geti            | allocation memoire pour quotient
        movl    a0,a6@(-28)     | a6@(-28) recoit adr. provisoire de q
        addl    d7,a6@(-28)     | ajoute offset memoires provisoires
                                | a6@(-28) contient adr definitive de q
        lea     a0@(0,d0:w:4),a1
        movl    a2,a3           | a2 et a3 pointe sur r1
2$:     movl    a3@-,a1@-       | recopie q0,q1...q(n-m)
        dbra    d1,2$
        movw    d0,a0@(6)       | met long effective de q
        movb    a6@(-12),a0@(4) | met signe de q
        cmpw    #2,d0
        bne     rngres
        clrb    a0@(4)          | rectifier signe lorsque q=0
rngres: tstl    d3
        beq     rendre
                                | ici reste attendu
        movw    a6@(-6),d0
        subqw   #1,d0           | d0 recoit m-1
4$:     tstl    a2@+
        dbne    d0,4$           | chasse les zeros
        bne     1$
                                | ici r=0 : ranger 0
        movw    #2,d0
        bsr     geti
        movl    #2,a0@(4)
        addl    d7,a0           | ajoute offset
        movl    a0,a6@(-32)     | adr. definit. de r
        bra     rendre
1$:     subql   #4,a2           | a2 pointe sur 1er ri non nul
        movw    d0,d1
        addqw   #3,d0
        bsr     geti            | allocation memoire pour reste
        movl    a0,a6@(-32)
        addl    d7,a6@(-32)     | ajoute offset memoires provisoires
        movb    a6@(-10),a0@(4) | met signe de r
        movw    d0,a0@(6)       | met long effect provisoire (si shift)
        addql   #8,a0
        movw    a6@(-14),d3     | d3 recoit k nb de shifts
        bne     2$
                                | ici k=0 pas de shift
5$:     movl    a2@+,a0@+
        dbra    d1,5$           | recopie des ri effectifs
        bra     rendre
2$:     moveq   #-1,d6          | ici shift de r
        lsrl    d3,d6           | d6 recoit masque de shift
        moveq   #0,d5
        bset    d3,d5           | d5 recoit 2^k
        moveq   #0,d2
        cmpl    a2@,d5          | comparer 1er ri a 2^k
        bls     3$
        movl    a2@+,d2         | ici ri < 2^k  : le shifter
        rorl    d3,d2
        subqw   #1,d0           | et diminuer de 1 la long de la boucle
        subqw   #1,a0@(-2)      | ainsi que la long effective de r
3$:     movl    a2@+,d5         | boucle de shift de r
        rorl    d3,d5           | boucle jamais vide car r>=2^k
        movl    d5,d4
        andl    d6,d4
        addl    d4,d2
        movl    d2,a0@+
        subl    d4,d5
        movl    d5,d2
        dbra    d1,3$
rendre: movl    a6@(-20),a0     | rendre memoires provisoires
        movl    a6@(-24),a1     | il faut rendre la zone entre a1 et a0
        movl    a1,d0
        subl    _avma,d0
        lsrl    #2,d0           | nb de lgmots a deplacer
        subqw   #1,d0
1$:     movl    a1@-,a0@-
        dbra    d0,1$
        movl    a0,_avma        | nouvel _avma
        movl    a6@(-28),d0
        bne     2$
        movl    a6@(-32),d0
        bra     dvmiif
2$:     tstl    a6@(-32)
        beq     dvmiif
        movl    a6@(16),a1
        movl    a6@(-32),a1@
dvmiif: moveml  sp@+,d2-d7/a2-a4
        unlk    a6
        rts



#===================================================================#
#                                                                   #
#                       Divisibilite de i2 par i1                   #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I                     #
#                a7@(8) pointe sur n1 de type I                     #
#                a7@(12) contient un pointeur ( pour quotient )     #
#       sortie : d0 contient 1 si n1 divise n2                      #
#                            0 sinon
#       a7@(12) pointe sur n2 / n1 de type I  (zone creee)          #
#       lorsque n1 divise n2,  sinon n'est pas affecte.             #
#                                                                   #
#===================================================================#

_mpdivis:link a6,#-8
        movl    _avma,a6@(-8)
        pea     a6@(-4)
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        bsr     _asmdvmdii
        lea     sp@(12),sp
        tstb    a6@(-4)@(4)             | reste nul ?
        beq     1$
                                        | ici reste non nul
        moveq   #0,d0
        movl    a6@(-8),_avma           | desallouer q et r
        bra     2$
                                        | ici reste nul
1$:     movl    a6@(16),sp@-
        movl    d0,sp@-                 | adresse du quotient
        bsr     _affii
        moveq   #1,d0
        movl    a6@(-8),_avma                   | desallouer reste
2$:     unlk    a6
        rts


#===================================================================#
#                                                                   #
#               Flag de divisibilite de i2 par i1                   #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I                     #
#                a7@(8) pointe sur n1 de type I                     #
#       sortie : d0 contient 1 si n1 divise n2                      #
#                            0 sinon                                #
#                                                                   #
#===================================================================#

_divise: movl   #-1,sp@-
        movl    sp@(12),sp@-
        movl    sp@(12),sp@-
        bsr     _asmdvmdii
        lea     sp@(12),sp
        movl    d0,a0
        moveq   #1,d0
        tstb    a0@(4)                  | reste nul ?
        beq     giv
                                        | ici reste non nul
        moveq   #0,d0
        bra     giv




#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES DE DIVISION                    **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Division generale                           #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#       sortie : d0 pointe sur n2 / n1 de type I ou R (zone creee)  #
#                Le reste est du signe du dividende                 #
#       interdit : type S                                           #
#       precision : voir routines specialisees                      #
#                                                                   #
#===================================================================#

_mpdiv: cmpb    #1,sp@(8)@
        bne     1$
        cmpb    #1,sp@(4)@
        beq     _divii
        bra     _divri
1$:     cmpb    #1,sp@(4)@
        beq     _divir
        bra     _divrr

#===================================================================#
#                                                                   #
#                       Division (par valeur)                       #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I ou R                #
#                a7@(8) pointe sur n1 de type I ou R                #
#                a7@(12) pointe sur n3 de type I ou R               #
#       sortie : la zone pointee par a7@(12) contient n2 / n1 de    #
#                type le type de n3                                 #
#       interdit : type S ainsi que les divisions suivantes :       #
#                R/I=I , I/R=I ,R/R=I                               #
#                                                                   #
#===================================================================#

_mpdivz:movl    a2,sp@-
        movl    _avma,sp@-
        movl    sp@(12),a1
        movl    sp@(16),a0
        movl    sp@(20),a2      | a0,a1,a2 pointent sur n1,n2,n3
        cmpb    #1,a2@
        bne     1$
                                | ici T3 = I
        cmpb    #1,a1@
        beq     2$
                                | ici T3 = I et (T2 = R ou T1 = R)
3$:     movl    #divzer1,sp@-
        jsr     _pari_err
                                | ici T3 = I et T2 = I
2$:     cmpb    #1,a0@
        bne     3$
                                | ici T3 = T2 = T1 = I
        movl    a0,sp@-
        movl    a1,sp@-
        bsr     _divii
        movl    a2,sp@(4)
        movl    d0,sp@
        bsr     _affii
        addql   #8,sp
        bra     divzf
                                | ici T3 = R
1$:     movl    a0,sp@-
        cmpb    #1,a0@
        beq     4$
                                | ici T3 = R et T1 = R
        movl    a1,sp@-
        cmpb    #1,a1@
        beq     5$
                                | ici T3 =T2 = T1 = R
        bsr     _divrr
        bra     6$
                                | ici T3 = T1 = R et T2 = I
5$:     bsr     _divir
        bra     6$
                                | ici T3 = R et T1 = I
4$:     cmpb    #1,a1@
        beq     7$
                                | ici T3 = T2 = R et T1 = I
        movl    a1,sp@-
        bsr     _divri
        bra     6$
                                | ici T3 = R et T2 = T1 = I
7$:     movw    a2@(2),d0
        addqw   #1,d0
        bsr     getr
        movl    a0,sp@-
        movl    a1,sp@-
        bsr     _affir
	addql	#4,sp
        bsr     _divri
6$:     movl    a2,sp@(4)
        movl    d0,sp@
        bsr     _affrr
        addql   #8,sp
divzf:  movl    sp@+,_avma
        movl    sp@+,a2
        rts

                                | division S/R=R sinon erreur

_divsrz:lea     _divsr,a0
        bra     mpopz

                                | division R/S=R sinon erreur

_divrsz:lea     _divrs,a0
        bra     mpopz

                                | division I/R=R sinon erreur

_divirz:lea     _divir,a0
        bra     mpopz

                                | division R/I=R sinon erreur

_divriz:lea     _divri,a0
        bra     mpopz

                                | division R/R=R sinon erreur

_divrrz:lea     _divrr,a0
        bra     mpopz
#===================================================================#
#                                                                   #
#       Division par valeur : entier / entier = entier ou reel      #
#                                                                   #
#       entree : a7@(4) contient i2 de type S                       #
#                a7@(8) contient i1 de type S                       #
#                a7@(12) pointe sur i3 ou r3 de type I ou R         #
#       sortie : a7@(12) pointe sur i2 / i1 de type I ou R          #
#                                                                   #
#===================================================================#

_divssz:cmpb    #1,sp@(12)@
        bne     divssr
divssi: movl    sp@(8),sp@-
        movl    sp@(8),sp@-
        bsr     _divss
        movl    sp@(20),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bra     giv
divssr: movl    _avma,sp@-
        movw    sp@(16)@(2),d0
        bsr     getr
        movl    a0,sp@-
        movl    sp@(12),sp@-
        bsr     _affsr          | conversion dividende en R
        movl    sp@(4),sp@      | dividende converti
        movl    sp@(20),sp@(4)  | diviseur (type S)
        bsr     _divrs
        movl    sp@(24),sp@(4)
        movl    d0,sp@
        bsr     _affrr
        addql   #8,sp
        movl    sp@+,_avma
        rts

#===================================================================#
#                                                                   #
#       Division par valeur : S / I = entier ou reel                #
#                                                                   #
#       entree : a7@(4) contien i2 de type S                        #
#                a7@(8) pointe sur i1 de type I                     #
#                a7@(12) pointe sur i3 ou r3 de type I ou R         #
#       sortie : a7@(12) pointe sur i2 / i1 de type I ou R          #
#                                                                   #
#===================================================================#

_divsiz:link    a6,#0
        moveml  a2-a4,sp@-
        movl    a6@(16),a3
        cmpb    #1,a3@
        bne     divsir
divsii: movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        bsr     _divsi
        movl    a6@(16),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bsr     giv
divsizf:moveml  sp@+,a2-a4
        unlk    a6
        rts
divsir: movl    _avma,a2
        movw    a3@(2),d0
        addqw   #1,d0
        bsr     getr
        movl    a0,a4
        movl    a0,sp@-
        movl    a6@(8),sp@-
        bsr     _affsr          | conversion dividende en R
        addql   #2,d0
        bsr     getr
        movl    a0,sp@(4)
        movl    a6@(12),sp@
        bsr     _affir          | conversion diviseur en R
        movl    a4,sp@
        bsr     _divrr
        movl    a3,sp@(4)
        movl    d0,sp@
        bsr     _affrr
        addql   #8,sp
        movl    a2,_avma
        bra     divsizf

#===================================================================#
#                                                                   #
#       Division par valeur : I / S = entier ou reel                #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient i1 de type S                       #
#                a7@(12) pointe sur i3 ou r3 de type I ou R         #
#       sortie : a7@(12) pointe sur i2 / i1 de type I ou R          #
#                                                                   #
#===================================================================#

_divisz:cmpb    #1,sp@(12)@
        bne     divisr
divisi: movl    sp@(8),sp@-
        movl    sp@(8),sp@-
        bsr     _divis
        movl    sp@(20),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bra     giv
divisr: movl    _avma,sp@-
        movw    sp@(16)@(2),d0
        bsr     getr
        movl    a0,sp@-
        movl    sp@(12),sp@-
        bsr     _affir          | conversion dividende en R
        movl    sp@(4),sp@      | dividende converti
        movl    sp@(20),sp@(4)  | diviseur (type S)
        bsr     _divrs
        movl    sp@(24),sp@(4)
        movl    d0,sp@
        bsr     _affrr
        addql   #8,sp
        movl    sp@+,_avma
        rts

#===================================================================#
#                                                                   #
#       Division par valeur : entier / entier = entier ou reel      #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#                a7@(12) pointe sur i3 ou r3 de type I ou R         #
#       sortie : a7@(12) pointe sur i2 / i1 de type I ou R          #
#                                                                   #
#===================================================================#

_diviiz:link    a6,#0
        moveml  a2-a4,sp@-
        movl    a6@(16),a3
        cmpb    #1,a3@
        bne     diviir
diviii: movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        bsr     _divii
        movl    a6@(16),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bsr     giv
diviizf:moveml  sp@+,a2-a4
        unlk    a6
        rts
diviir: movl    _avma,a2
        movw    a3@(2),d0
        bsr     getr
        movl    a0,a4
        movl    a0,sp@-
        movl    a6@(8),sp@-
        bsr     _affir          | conversion dividende en R
        addql   #2,d0
        bsr     getr
        movl    a0,sp@(4)
        movl    a6@(12),sp@
        bsr     _affir          | conversion diviseur en R
        movl    a4,sp@
        bsr     _divrr
        movl    a3,sp@(4)
        movl    d0,sp@
        bsr     _affrr
        addql   #8,sp
        movl    a2,_avma
        bra     diviizf


#===================================================================#
#                                                                   #
#               Division : entier court / entier court = entier     #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur s2 div s1 de type I (zone creee)     #
#                d1.l contient le reste(du signe du dividende)      #
#                                                                   #
#===================================================================#

_divss: link    a6,#0
        moveml  d2-d3,sp@-
	moveq	#0,d3
        movl    a6@(12),d1      | d1.l recoit s1
        bne     1$
                                | ici s1 = 0
        movl    #diver1,sp@-
        jsr     _pari_err
                                | ici s1 <> 0
1$:     movl    a6@(8),d2       | d2.l recoit s2
	bpl	9$
	moveq	#-1,d3
9$:     divsll  d1,d3:d2
        bne     2$
                                | ici quotient nul
3$:     movl	_gzero,d0
        movl    d3,d1
        bra     divssg
                                | ici quotient non nul
2$:     moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        tstl    d2
        bpl     4$
        negl    d2
        movb    #-1,a0@(4)
4$:     movl    d2,a0@(8)
        movl    d3,d1
divssf: movl    a0,d0
divssg: moveml  sp@+,d2-d3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Division : entier court / entier = entier           #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient i1 de type I                       #
#       sortie : d0 pointe sur s2 div i1 de type I (zone creee)     #
#                d1.l contient le reste (du signe du dividende)     #
#                                                                   #
#===================================================================#

_divsi: link    a6,#0
        moveml  d2-d4,sp@-
        movl    a6@(12),a1      | a1 pointe sur le diviseur i1
        tstb    a1@(4)
        bne     1$
                                | ici i1 = 0
        movl    #diver2,sp@-
        jsr     _pari_err
                                | ici i1 <> 0
1$:     movl    a6@(8),d2       | d2.l contient le dividende s2
        bne     3$
                                | ici quotient et reste nuls
2$:     movl	_gzero,d0
        moveq   #0,d1
        bra     divsig
                                | ici i1 et s2 <> 0
3$:     movw    a1@(6),d1       | d1.w contient le1
        cmpw    #3,d1
        beq     4$
                                | ici quotient nul et reste=s2
6$:     movl	_gzero,a0
        movl    d2,d1
        bra     divsif
                                | ici L1 = 1
4$:     movl    a1@(8),d1       | d1.l contient |i1|
        movl    d2,d3           | d3.l contient s2
        bpl     5$
        negl    d3              | d3.l contient |s2|
5$:     moveq   #0,d4
        divul   d1,d4:d3
        beq     6$
        moveq   #3,d0
        bsr     geti
        movl    d3,a0@(8)       | ranger mantisse
        movl    a1@(4),a0@(4)
        tstl    d2
        bpl     7$
        movb    #-1,a0@(4)      | mise a jour du signe
7$:     movl    d4,d1
        tstb    a1@(4)
        bpl     divsif
        negl    d1              | mise a jour reste
divsif: movl    a0,d0
divsig: moveml  sp@+,d2-d4
        unlk    a6
        movl	d1,_hiremainder
        rts

#===================================================================#
#                                                                   #
#               Division : entier court / reel = reel               #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur s2 / r1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_divsr: link    a6,#-32
        moveml  d2/a2-a4,sp@-
        movl    a6@(12),a1      | a1 pointe sur r1
        tstb    a1@(4)
        bne     2$
                                | ici r1 = 0
        movl    #diver3,sp@-
        jsr     _pari_err
                                | ici r1 <> 0
2$:     tstl    a6@(8)
        bne     1$
                                | ici s2 = 0
	movl	_gzero,d0
        bra     divsrf
                                | ici s2 et r1 <> 0
1$:     moveq   #0,d0
        movw    a1@(2),d0
        bsr     getr            | allocation pour resultat
        movl    a6@(8),d2       | d2.l recoit s2
        movl    a0,a4
        addqw   #1,d0
        bsr     getr
        movl    a0,sp@-         | sauvegarde adr. copie
        movl    d2,sp@-
        bsr     _affsr
        addql   #4,sp
        movl    a0,a2           | a2 pointe sur copie s2
        movl    a4,a0           | a0 pointe sur resultat
        bsr     dvrr
        movl    sp@+,a0
        bsr     giv             | desallouer copie
        movl    a4,d0
divsrf: moveml  sp@+,d2/a2-a4
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Division : entier / entier court = entier           #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur i2 / s1 de type I (zone creee)       #
#               le reste est dans d1.l (du signe du dividende)      #
#                                                                   #
#===================================================================#

_divis: link    a6,#0
        moveml  d2-d6/a2,sp@-
        movl    a6@(12),d1      | d1 recoit s1 diviseur
        bne     1$
        movl    #diver4,sp@-
        jsr     _pari_err
1$:     bpl     2$
        negl    d1
                                | ici d1 contient |s1|
2$:     movl    a6@(8),a2       | a2 pointe sur i2 dividende
        movw    a2@(6),d2       | d2 recoit le2
        movw    a2@(4),d5       | signe de i2
        bne     4$
                                | ici i2=0 : q=0 , r=0
3$:     movl	_gzero,d0
        moveq   #0,d1           | reste nul
        bra     divisg
                                | ici i2 et s1 <>0
4$:     movw    d2,d0           | d0 recoit le2
        addql   #8,a2
        movl    a2@+,d4
	moveq	#0,d3
        divull  d1,d3:d4        | calcul de q0
        bne     5$
                                | ici q0 = 0
        subqw   #1,d0           | diminuer long. effective
        cmpw    #2,d0
        bne     5$
                                | ici q=0 , reste dans d3
	movl	_gzero,a0
        bra     10$
                                | ici q <> 0
5$:     bsr     geti
        movl    a0,a1
        movw    d0,a0@(6)       | met long. effect.
        movb    #1,a0@(4)
        movw    a6@(12),d6      | 'signe de s1'
        eorw    d5,d6
        bpl     6$              | si de meme signe
        movb    #-1,a0@(4)      | si de signes contraires
6$:     addql   #8,a1
        tstl    d4              | q0 = 0 ?
        beq     7$
        movl    d4,a1@+         | non: ranger q0
7$:     subqw   #3,d2           | d2 recoit L1 -1 compteur
        bra     9$
8$:     movl    a2@+,d4         | boucle de division
        divul   d1,d3:d4
        movl    d4,a1@+
9$:     dbra    d2,8$
10$:    movl    d3,d1           | le reste est mis dans d1
        tstw    d5              | i1 > 0 ?
        bpl     divisf
        negl    d1              | non : changer signe de r
divisf: movl    a0,d0           | met addresse resultat
divisg: moveml  sp@+,d2-d6/a2
        unlk a6
        movl	d1,_hiremainder
        rts

#===================================================================#
#                                                                   #
#               Division : entier / entier = entier                 #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur i2 / i1 de type I (zone creee)       #
#                Le reste est du signe du dividende                 #
#                                                                   #
#===================================================================#

_divii: clrl    sp@-
        movl    sp@(12),sp@-    | empilage de i1
        movl    sp@(12),sp@-    | empilage de i2
        bsr     _asmdvmdii
        lea     sp@(12),sp      | depilage
        rts

#===================================================================#
#                                                                   #
#               Division : entier / reel = reel                     #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur i2 / r1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_divir: link    a6,#-32         | var. locales pour appel dvrr
        moveml  a2-a3,sp@-
        movl    a6@(12),a1      | a1 pointe sur r1
        tstb    a1@(4)
        bne     1$
                                | ici r1 = 0
        movl    #diver5,sp@-
        jsr     _pari_err
                                | ici r1 <> 0
1$:     movl    a6@(8),a2       | a2 pointe sur i2
        tstb    a2@(4)
        bne     2$
                                | ici i2 = 0
	movl	_gzero,d0
        bra     divirf
2$:     moveq   #0,d0           | ici i2 et r1 <> 0
        movw    a1@(2),d0       | d0.w contient l1
        bsr     getr            | allocation pour resultat
        movl    a0,a3
        addqw   #1,d0
        bsr     getr            | allocation pour conversion i2 type R
        movl    a0,a6@(-16)     | sauvegarde adr. du transforme i2'
        movl    a0,sp@-
        movl    a2,sp@-
        bsr     _affir
        addql   #8,sp
        movl    a0,a2           | a2 pointe sur i2'
        movl    a3,a0           | a0 pointe sur resultat
        bsr     dvrr
        movl    a6@(-16),a0
        bsr     giv             | desallouer i2'
        movl    a3,d0
divirf: moveml  sp@+,a2-a3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Division : reel / entier court = reel               #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur s1 de type S                     #
#       sortie : d0 pointe sur r2 / s1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_divrs: link    a6,#0
        moveml  d2-d6/a2,sp@-
        movl    a6@(12),d1      | d1 recoit s1 diviseur
        bne     1$
                                | ici s1 = 0
        movl    #diver6,sp@-
        jsr     _pari_err
                                | ici diviseur s1 <> 0
1$:     movl    a6@(8),a2       | a2 pointe sur r2 dividende
        tstb    a2@(4)
        bne     2$
                                | ici r2 = 0
        moveq   #3,d0
        bsr     getr
        tstl    d1
        bpl     11$
        negl    d1
11$:    bfffo   d1{#0:#0},d0
        addl    a2@(4),d0
        subl    #31,d0
        bmi     9$
        movl    d0,a0@(4)
        clrl    a0@(8)
        bra     divrsf
                                | ici r2 et s1 <> 0
2$:     movw    a2@(2),d0       | d0 recoit l2
        bsr     getr            | allocation pour resultat
        movb    a2@(4),a0@(4)   | signe de r2
        tstl    d1
        bpl     3$
        negl    d1              | d1 recoit |s1| <= 2^31
                                | s1 est tjrs <= 1er mot mantisse
                                | le 1er quotient partiel est non nul
        negb    a0@(4)
3$:     movl    a0,a1
        addql   #8,a1
        addql   #8,a2
        subqw   #3,d0           | d0 recoit L2-1 compteur
        movl    d0,d2           | conserve dans d2
        moveq   #0,d3           | 1er reste
4$:     movl    a2@+,d4
        divul   d1,d3:d4
        movl    d4,a1@+
        dbra    d0,4$           | boucle de division

        movl    a0@(8),d0       | resultat normalise ?
        bpl     10$
        moveq   #0,d1           | ici normalise ; nb shift = 0
        bra     5$
                                | ici il faut normaliser

10$:    moveq   #0,d4
        divul   d1,d3:d4        | traite dernier reste: quotient
                                | a recuperer par le shift
        bfffo   d0{#0:#0},d1    | nb de shift dans d1
        lsll    d1,d0           | shift 1er lg mot d0
        movl    a0,a1
        addql   #8,a1
        moveq   #1,d6
        lsll    d1,d6
        subql   #1,d6           | d6 masque de shift
        bra     7$
6$:     movl    a1@(4),d3
        roll    d1,d3
        movl    d3,d5
        andl    d6,d3
        addl    d3,d0
        movl    d0,a1@+
        subl    d3,d5
        movl    d5,d0
7$:     dbra    d2,6$
        roll    d1,d4           | shifter dernier quotient
        andl    d6,d4
        addl    d4,d0
        movl    d0,a1@
5$:     movl    a6@(8),a2       | a2 pointe sur r2 dividende
        movl    a2@(4),d2
        andl    #0xffffff,d2    | exposant biaise de r2
        subl    d1,d2           | exposant resultat
        bpl     8$
                                | ici underflow
9$:     movl    #diver7,sp@-
        jsr     _pari_err
8$:     movw    d2,a0@(6)
        swap    d2
        movb    d2,a0@(5)       | range exposant
divrsf: movl    a0,d0
        moveml  sp@+,d2-d6/a2
        unlk    a6
        rts


#===================================================================#
#                                                                   #
#               Division : reel / entier = reel                     #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur r2 / i1 de type R (zone creee)       #
#                                                                   #
#===================================================================#

_divri: link    a6,#-32         | var. locales pour appel dvrr
        moveml  d2-d3/a2-a3,sp@-
        movl    a6@(12),a1      | a1 pointe sur le diviseur i1
        tstb    a1@(4)
        bne     1$
                                | ici i1 = 0
        movl    #diver8,sp@-
        jsr     _pari_err
                                | ici i1 <> 0
1$:     movl    a6@(8),a2       | a2 pointe sur le dividende r2
        tstb    a2@(4)
        bne     2$
                                | ici r2 = 0
        moveq   #3,d0
        bsr     getr
        movw    a1@(6),d0
        lsll    #5,d0
        bfffo   a1@(8){#0:#0},d1
        addl    a2@(4),d1
        addl    #65,d1
        subl    d0,d1
        bpl     3$
        movl    #diver12,sp@-   | underflow R/I avec R = 0
        jsr     _pari_err
3$:     movl    d1,a0@(4)
        clrl    a0@(8)
        movl    a0,d0
        bra     divrif
                                | ici r2 et i1 <> 0
2$:     moveq   #0,d0
        movw    a2@(2),d0
        bsr     getr            | allocation pour resultat
	movl	_avma,a3        | eviter le chevauchement.
	subql	#8,a3
	movl	a3,_avma
	movl	#2,a3@		| Hack pour que giv rende ceci
        movl    a0,a3           | sauvegarde adr. resultat
        addqw   #1,d0
        bsr     getr            | allocation pour conversion i1 type R
        movl    a0,a6@(-16)     | sauvegarde adr. copie
        movl    a0,sp@-
        movl    a1,sp@-
        bsr     _affir
        addql   #8,sp
        movl    a0,a1           | a1 pointe sur copie i1
        movl    a3,a0           | a0 pointe sur resultat
        bsr     dvrr
        movl    a6@(-16),a0
        bsr     giv             | desallouer copie
        movl    a3,d0
divrif: moveml  sp@+,d2-d3/a2-a3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Division : reel / reel = reel                       #
#                                                                   #
#       entree : a7@(4) pointe sur r2 de type R                     #
#                a7@(8) pointe sur r1 de type R                     #
#       sortie : d0 pointe sur r2 / r1 de type R (zone creee)       #
#       precision : L = inf ( L1 , L2 )                             #
#                                                                   #
#===================================================================#

_divrr: link    a6,#-32         | var. locales pour appel dvrr
        movl    a2,sp@-
        movl    a6@(12),a1      | a1 pointe sur r1=y diviseur
        movl    a6@(8),a2       | a2 pointe sur r2=x dividende
        tstb    a1@(4)          | r1 = 0 ?
        bne     1$
                                | ici r1 = 0
        movl    #diver9,sp@-
        jsr     _pari_err
1$:     tstb    a2@(4)          | r2 = 0 ?
        bne     3$
                                | ici r2=0, r1<>0 : resultat nul
        moveq   #3,d0
        bsr     getr
        movl    a1@(4),d0
        andl    #0xffffff,d0    | exposant de r1
        subl    a2@(4),d0
        negl    d0
        addl    #0x800000,d0
        cmpl    #0x1000000,d0
        bcs     4$
        movl    #diver11,sp@-   | debordement r/r
        jsr     _pari_err
4$:     tstl    d0
        bgt     5$
        movl    #diver10,sp@-   | underflow r/r
        jsr     _pari_err
5$:     movl    d0,a0@(4)
        clrl    a0@(8)
        bra     divrrf
3$:     movw    a1@(2),d0
        cmpw    a2@(2),d0
        bls     2$
        movw    a2@(2),d0       | d0 recoit l=inf(l1,l2)
2$:     bsr     getr
        bsr     dvrr            | effectuer la division !
divrrf: movl    a0,d0
        movl    sp@,a2
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#       module interne de division r/r (pour R/R,R/I,I/R et S/R)    #
#       --------------------------------------------------------    #
#       entree : a1 et a2 pointent sur 2 reels r1 et r2             #
#       tous 2 non nuls.                                            #
#       a0 pointe sur un type reel de longueur l=inf(l1,l2)         #
#       ce module a besoin de variables locales reservees et        #
#       pointees par a6 dans le programme appelant.                 #
#       sortie : le quotient r2/r1 est mis a l'addresse initiale a0 #
#       (qui n'est pas affectee)                                    #
#===================================================================#

dvrr:   moveml  d2-d7/a2-a4,sp@-
        movb    a1@(4),d1       | signe de r1
        movb    a2@(4),d2       | signe de r2
        eorb    d2,d1
        addqb   #1,d1
        movb    d1,a6@(-2)      | sauvegarde signe resultat
        movl    a2@(4),d2
        andl    #0xffffff,d2
        movl    a1@(4),d1
        andl    #0xffffff,d1
        subl    d1,d2
        addl    #0x800000,d2	| exposant provisoire avec offset
        movl    d2,a6@(-6)      | sauvegarde

        movw    a0@(2),d0       | d0.w recoit longueur resultat ( inf(l1,l2) )
        movw    a1@(2),d1
	cmpw	#3,d1		| diviseur de longeur 3 ?
	bne	5$
	movl	a1@(8),d1	
	movl	a2@(8),d3
	clrl	d2
	cmpw	#3,a2@(2)
	beq	7$
	movl	a2@(12),d2
7$:	cmpl	d3,d1
	bls	6$
	divul	d1,d3:d2
	movl	d2,a0@(8)
	movl	a6@(-6),d0	| ici mantisse correcte, soustraire 1 a l'exposant
	subql	#1,d0
	bra	comd2
6$:	lsrl	#1,d3
	roxrl	#1,d2		| shifter de 1 a droite le quadword
	divul	d1,d3:d2
	movl	d2,a0@(8)
	movl	a6@(-6),d0	| exposant correct
	bra 	comd2
5$:     subw    d0,d1           | flag nombre de mots du diviseur
        movw    d1,a6@(-28)     | a sauvegarder.
        subqw   #2,d0
        movw    d0,d7           | d0 et d7 recoit m=inf(l1,l2)-2
        movw    d7,a6@(-12)     | d7 sera compt boucle externe
        movl    a0@,a6@(-10)    | sauvegarde 1er lg mot code resultat
                                | (on a besoin de toute la place)
	movw	a2@(2),d6
	subqw	#2,d6		| sauvegarde l2-2
        addql   #8,a2           | a2 pointe sur y1 (1er mot dividende
                                | on note y=y1y2...ym le dividende
        movl    a0,a4
        clrl    a4@+
1$:     movl    a2@+,a4@+       | on recopie m+1 lgmots mantisse de y
        dbra    d0,1$           | precede par un zero
	cmpw	d7,d6		| l2>l1 ?
	bgt	4$
	clrl	a4@(-4)		| Si l2<=l1, y(m+1) n'existe pas
                                | a4 pointe apres y(m+1)
4$:     movl    a0,a2           | a2 pointe sur y0=0 1er mot dividende
        addql   #8,a1           | a1 pointe sur x1 1er mot diviseur
        lea     a1@(8,d7:w:4),a3| a3 pointe apres x(m+2)
        movl    a3,a6@(-32)
        movw    a6@(-28),d6     | (peut etre n'importe quoi mais va etre
        bne     2$              | corrige)
        movl    a3@(-8),a6@(-20)
        clrl    a3@(-8)
2$:     subqw   #1,d6
        bgt     3$
        movl    a3@(-4),a6@(-24)
        clrl    a3@(-4)
3$:     moveq   #0,d6           | d6 recoit 0 pour les addx

                                | Boucles de division R/R
                                | d7 compt bcl externe initialise a m
                                | pour trouver q0q1...qm
                                | d0 compt bcl interne initialise
                                | par d7 a chaque tour
#...................................................................#
dext:   movl    a1@,d0          | d0 recoit x1 (1er mot diviseur)
        cmpl    a2@,d0          | compare a yi
        bne     1$
        movl    #-1,d1          | essayer q=2^32-1
        addl    a2@(4),d0
        bcs     4$
        movl    d0,d2
        bra     2$
1$:     bcc	9$
	
	moveml	a3-a4/d7,sp@-	| le quotient precedent etait trop faible
	addql	#4,a3
	subxl	a3@-,a4@-
10$:	subxl	a3@-,a4@-
	dbra	d7,10$
11$:	addql	#1,a4@-
	beq	11$
	moveml  sp@+,a3-a4/d7

9$:	movl    a2@,d2          | d2 recoit yi
        movl    a2@(4),d1       | d2:d1 recoit yiy(i+1)
        divul   d0,d2:d1        | d1 recoit q = yiy(i+1) div x1
                                | d2 recoit r = yiy(i+1) mod x1
2$:     movl    a1@(4),d3       | d3 recoit x2
        mulul   d1,d4:d3        | d4:d3 recoit q*x2
        subl    a2@(8),d3
        subxl   d2,d4           | d4:d3 recoit q*x2-(r,y(i+2))
        bls     4$

3$:     subql   #1,d1           | ici q est trop grand : q-1
        subl    a1@(4),d3
        subxl   d0,d4           | correction du reste partiel
        bhi     3$              | boucler tant que trop
                                | ici q =yiy(i+1)y(i+2) div x1x2 correct
                                | on va calculer le reste partiel
4$:     movw    d7,d0           | d0  recoit m-i compteur
        movl    a3,a1           | a3,a1 pointent apres y(m+2-i)
        movl    a4,a2           | a4,a2 pointent apres y(m+1)
        movl    a1@-,d2
        mulul   d1,d3:d2        | initialise retenue d3 par
        subl    d2,d2           | poids fort de q*y(m+2-i). d2 et X a 0
5$:     movl    a1@-,d5
        mulul   d1,d4:d5        | boucle interne de multiplication et
        addxl   d3,d5           | soustraction :
        addxl   d2,d4           | yi...y(m+1) recoit yi...y(m+1)-
        subl    d5,a2@-         |      q*x1...x(m+1-i)
        movl    d4,d3
        dbra    d0,5$
        addxl   d2,d3
        subl    d3,a2@(-4)
        bcc     6$
                                | ici carry: q encore 1 de trop
        subql   #1,d1
        movw    d7,d0
        movl    a3,a1
        movl    a4,a2
        subql   #4,a1           | correction sur a1 (car on avait prevu
                                | d'initialiser la retenue)
7$:     addxl   a1@-,a2@-
        dbra    d0,7$           | boucle de readdition(met reste a jour)
6$:     movl    d1,a2@(-4)      | qi correct ! ranger a la place de xi
        subql   #4,a3           | a3 p. un mot de moins pour bcle suiv.
                                | a3 pointe sur x(m-i+1)
bcdf:   dbra    d7,dext         | fin de boucle externe de division
#...................................................................#
	movl	a6@(-32),a3
        movw    a6@(-28),d5     | remise eventuelle de xm+1 et xm+2
        bne     7$
        movl    a6@(-20),a3@(-8)
7$:     subqw   #1,d5
        bgt     8$
        movl    a6@(-24),a3@(-4)
8$:     movw    a6@(-12),d5
        movw    d5,d4           | d4 recoit m
6$:     movl    a2@-,a2@(4)
        dbra    d5,6$
        movl    a6@(-10),a2@+   | 1er lg mot code;a2 pointe sur q1
        movl    a6@(-6),d0      | exposant biaise
        movl    a2@,d1          | d1 recoit q0=0 ou 1
        bne     1$
                                | ici q0=0 : mantisse correcte
        subql   #1,d0           | retrancher 1 a l'exposant
        bra     comd2
1$:     addql   #4,a2           | ici q0=1 : shifter de 1 a droite
        subqw   #1,d4           | d4 recoit m-1
        asrw    #1,d1           | met carry flag
5$:     roxrw   a2@+
        roxrw   a2@+
        dbra    d4,5$           | boucle de normalisation
comd2:  cmpl    #0x1000000,d0
        ble     3$
        movl    #diver10,sp@-   | underflow
        jsr     _pari_err
3$:     bcs     4$
        movl    #diver11,sp@-   | overflow
        jsr     _pari_err
4$:     movl    d0,a0@(4)       | range exposant
        movb    a6@(-2),a0@(4)  | range signe
        moveml  sp@+,d2-d7/a2-a4
dvrrf:  rts




#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES D ' INVERSION                  **#
#**             ( programmes par valeurs : le resultat est        **#
#*                      mis dans un REEL existant deja  )         **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#


_mpinvsr:movl   sp@(8),sp@-
        movl    sp@(8),sp@-
        pea     1
        bsr     divssr
        lea     sp@(12),sp
        rts

_mpinvz:cmpb    #1,sp@(4)@
        bne     _mpinvrr

_mpinvir:movl   sp@(8),sp@-
        movl    sp@(8),sp@-
        pea     1
        bsr     _divsiz
        lea     sp@(12),sp
        rts

_mpinvrr:movl   sp@(8),sp@-
        movl    sp@(8),sp@-
        pea     1
        bsr     _divsrz
        lea     sp@(12),sp
        rts



#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**                     PROGRAMMES MODULO                         **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#






#===================================================================#
#                                                                   #
#                       Modulo (par valeur)                         #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I                     #
#                a7@(8) pointe sur n1 de type I                     #
#                a7@(12) pointe sur n3 de type I                    #
#       sortie : la zone pointee par a7@(12) contient le reste de   #
#                la division de n2 par n1                           #
#                compris entre 0 et abs(n1)-1                       #
#       interdit : type S et R                                      #
#                                                                   #
#===================================================================#

_mpmodz:lea     _modii,a0
        bra     mpopi

                                | modulo S mod S = I sinon erreur

_modssz:lea     _modss,a0
        bra     mpopi

                                | modulo S mod I = I sinon erreur

_modsiz:lea     _modsi,a0
        bra     mpopi

                                | modulo I mod S = I sinon erreur

_modisz:lea     _modis,a0
        bra     mpopi

                                | modulo I mod I = I sinon erreur

_modiiz:lea     _modii,a0
        bra     mpopi

#===================================================================#
#                                                                   #
#               entier court Modulo entier court = entier           #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur s2 mod s1 de type I (zone creee)     #
#                compris entre 0 et abs(s1)-1                       #
#                                                                   #
#===================================================================#

_modss: link    a6,#0
        moveml  d2-d3,sp@-
	moveq	#0,d3
        movl    a6@(12),d1      | d1.l contient s1
        bne     1$
                                | ici s1 = 0
        movl    #moder1,sp@-
        jsr     _pari_err
                                | ici s1 <> 0
1$:     movl    a6@(8),d2       | d2.l contient s2
	bpl	9$
	moveq	#-1,d3
9$:     divsll  d1,d3:d2
        tstl    d3
        bne     2$
                                | ici reste nul
3$:     movl	_gzero,d0
        bra     modssf
                                | ici reste non nul
2$:     bmi     5$
                                | ici reste > 0
        moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        movl    d3,a0@(8)
        bra 7$
                                | ici reste < 0
5$:     movl    a6@(12),sp@-
        movl    d3,sp@-
        tstl    d1
        bpl     6$
                                | ici s1 < 0
        bsr     _subss
        addql   #8,sp
        bra     modssf
                                | ici s1 > 0
6$:     bsr     _addss
        addql   #8,sp
        bra     modssf
7$:     movl    a0,d0
modssf: moveml  sp@+,d2-d3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               entier court Modulo entier = entier                 #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) ppinte sur i1 de type I                     #
#       sortie : d0 pointe sur s2 mod i1 de type I (zone creee)     #
#                compris entre 0 et abs(i1)-1                       #
#                                                                   #
#===================================================================#

_modsi: link    a6,#0
        moveml  d2-d3,sp@-
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        bsr     _divsi
        addql   #8,sp
        movl    d0,a0
        bsr     giv             | desallouer memoire provisoire
        tstl    d1              | tester le reste
        bne     1$
                                | ici reste nul
        movl	_gzero,d0
        bra     modsif
                                | ici reste non nul
1$:     bmi     3$
                                | ici reste > 0
        movl    d1,d3           | d3.l recoit le reste
        moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        movl    d3,a0@(8)
        bra     2$
                                | ici reste < 0
3$:     movl    a6@(12),sp@-
        movl    d1,sp@-
        movl    a6@(12),a1      | a1 pointe sur i1
        tstb    a1@(4)
        bpl     5$
                                | ici i1 < 0
        bsr     _subsi
        bra     6$
                                | ici i1 > 0
5$:     bsr     _addsi
6$:     addql   #8,sp
        bra     modsif
2$:     movl    a0,d0
modsif: moveml  sp@+,d2-d3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               entier Modulo entier court = entier                 #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur i2 mod s1 de type I (zone creee)     #
#                compris entre 0 et abs(s1)-1                       #
#                                                                   #
#===================================================================#

_modis: link    a6,#0
        moveml  d2-d3,sp@-
        movl    a6@(12),sp@-
        movl    a6@(8),sp@-
        bsr     _divis
        addql   #8,sp
        movl    d0,a0
        bsr     giv
        tstl    d1
        bne     1$
                                | ici reste nul
	movl	_gzero,d0
        bra     modisf
                                | ici reste non nul
1$:     bmi     3$
                                | ici reste > 0
        movl    d1,d3
        moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        movl    d3,a0@(8)
        bra     2$
                                | ici reste < 0
3$:     movl    a6@(12),sp@-
        movl    d1,sp@-
        movl    a6@(12),d1      | d1.l contient s1
        bpl     5$
        bsr     _subss
        bra     6$
5$:     bsr     _addss
6$:     addql   #8,sp
        bra     modisf
2$:     movl    a0,d0
modisf: moveml  sp@+,d2-d3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               entier Modulo entier = entier                       #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur i2 mod i1 de type I                  #
#                compris entre 0 et abs(i1)-1(zone creee)           #
#                                                                   #
#===================================================================#

_modii: link    a6,#-4
        movl    #-1,sp@-
        movl    a6@(12),sp@-    | empilage adresse i1
        movl    a6@(8),sp@-     | empilage adresse i2
        movl    _avma,a6@(-4)   | sauvegarde adr. tete pile PARI
        bsr     _asmdvmdii
        movl    d0,a1           | a1 pointe sur resultat
        tstb    a1@(4)
        bpl     modiif
                                | ici reste negatif
        movl    a1,sp@          | empilage adr. du reste
        tstb    a6@(12)@(4)     | test signe du modulo
        bpl     1$
        bsr     _subii
        bra     2$
1$:     bsr     _addii
2$:     movl    sp@+,a1
        movl    _avma,a0
        movw    a0@(2),d0
        subqw   #1,d0
        movl    a6@(-4),a0      | a0 pointe sur pile initiale
3$:     movl    a1@-,a0@-
        dbra    d0,3$           | ecraser resultat intermediaire
        movl    a0,_avma
        movl    a0,d0           | nouvelle adresse resultat
modiif: unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**     PROGRAMMES DE RESTE DES DIVISIONS ENTIERES                **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#                       Reste (par valeur)                          #
#                                                                   #
#       entree : a7@(4) pointe sur n2 de type I                     #
#                a7@(8) pointe sur n1 de type I                     #
#                a7@(12) pointe sur n3 de type I                    #
#       sortie : la zone pointee par a7@(12) contient le reste de   #
#                la division de n2 par n1 (du signe du dividende)   #
#       interdit : type S et R                                      #
#                                                                   #
#===================================================================#

_mpresz:lea     _resii,a0
        bra     mpopi

                                | reste de S/S = I sinon erreur

_resssz:lea     _resss,a0
        bra     mpopi

                                | reste de S/I = I sinon erreur

_ressiz:lea     _ressi,a0
        bra     mpopi

                                | reste de I/S = I sinon erreur

_resisz:lea     _resis,a0
        bra     mpopi

                                | reste de I/I = I sinon erreur

_resiiz:lea     _resii,a0
        bra     mpopi

#===================================================================#
#                                                                   #
#               Reste : entier court / entier court = entier        #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur le reste de la division s2 / s1      #
#                de type I (zone creee)                             #
#                Le reste est du signe du dividende                 #
#                                                                   #
#===================================================================#

_resss: link    a6,#0
        moveml  d2-d3,sp@-
	moveq	#0,d3
        movl    a6@(12),d1      | d1.l contient le diviseur s1
        bne     1$
                                | ici s1 = 0
        movl    #reser1,sp@-
        jsr     _pari_err
                                | ici s1 <> 0
1$:     movl    a6@(8),d2       | d2.l contient s2
	bpl	9$
	moveq	#-1,d3
9$:     divsll  d1,d3:d2
        tstl    d3
        bne     2$
                                | ici reste nul
	movl	_gzero,d0
        bra     resssg
                                | ici reste non nul
2$:     moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        tstl    d3
        bpl     3$
        negl    d3
        movb    #-1,a0@(4)
3$:     movl    d3,a0@(8)
resssf: movl    a0,d0
resssg: moveml  sp@+,d2-d3
        unlk    a6
        rts

#===================================================================#
#                                                                   #
#               Reste : entier court / entier = entier              #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur le reste de la division s2 / i1      #
#                de type I (zone creee)                             #
#                Le reste est du signe du dividende                 #
#                                                                   #
#===================================================================#

_ressi: movl    sp@(8),sp@-     | empilage adr. i1
        movl    sp@(8),sp@-     | empilage s2
        bsr     _divsi
        movl    d0,a0           | a0 pointe sur resultat prov.
        bsr     giv
        tstl    d1              | d1.l contient le reste
        bne     1$
                                | ici reste nul
	movl	_gzero,d0
        bra     ressig
                                | ici reste non nul
1$:     moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        tstl    d1
        bpl     2$
        negl    d1
        movb    #-1,a0@(4)
2$:     movl    d1,a0@(8)
ressif: movl    a0,d0
ressig: addql   #8,sp
        rts

#===================================================================#
#                                                                   #
#               Reste : entier / entier court = entier              #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) contient s1 de type S                       #
#       sortie : d0 pointe sur le reste de la division i2 / s1      #
#                (zone creee)                                       #
#                Le reste est du signe du dividende                 #
#                                                                   #
#===================================================================#

_resis: movl    sp@(8),sp@-     | empilage s1
        movl    sp@(8),sp@-     | empilage adr.i2
        bsr     _divis
        movl    d0,a0
        bsr     giv             | desallouer memoire provisoire
        tstl    d1              | le reste est dans d1.l
        bne     1$
                                | ici reste nul
	movl	_gzero,d0
        bra     resisg
                                | ici reste non nul
1$:     moveq   #3,d0
        bsr     geti
        movl    #0x1000003,a0@(4)
        tstl    d1
        bpl     2$
        negl    d1
        movb    #-1,a0@(4)
2$:     movl    d1,a0@(8)
resisf: movl    a0,d0
resisg: addql   #8,sp
        rts

#===================================================================#
#                                                                   #
#               Reste : entier / entier = entier                    #
#                                                                   #
#       entree : a7@(4) pointe sur i2 de type I                     #
#                a7@(8) pointe sur i1 de type I                     #
#       sortie : d0 pointe sur le reste de la division i2 / i1      #
#                de type I (zone creee)                             #
#                ( du signe du dividende)                           #
#                                                                   #
#===================================================================#

_resii: movl    #-1,sp@-
        movl    sp@(12),sp@-
        movl    sp@(12),sp@-
        bsr     _asmdvmdii
        lea     sp@(12),sp
        rts

#===================================================================#
#                                                                   #
#                       Operations par valeur                       #
#                                                                   #
#       entree : a7@(4) contient n2 de type S ou pointe sur n2      #
#                de type I ou R                                     #
#                a7@(8) contient n1 de type S ou pointe sur n1      #
#                de type I ou R                                     #
#                a7@(12) pointe sur n3 de type I ou R               #
#       sortie : la zone pointee par a7@(12) contient n2 op n1      #
#       remarque : les erreurs de type sont detectees dans l'       #
#                  affectation du resultat                          #
#                                                                   #
#===================================================================#

                                | operation a trois operandes
                                | les trois operandes sont de type I

mpariz: movb    sp@(12)@,d0
        addb    sp@(8)@,d0
        addb    sp@(4)@,d0
        cmpb    #3,d0
        beq     mpopz
        movl    #arier1,sp@-
        jsr     _pari_err

                                | le troisieme operande est de type I

mpopi:  cmpb    #1,sp@(12)@
        beq     mpopz
        movl    #arier2,sp@-
        jsr     _pari_err
                                | operation quelconque

mpopz:  movl    sp@(8),sp@-     | 2eme operande
        movl    sp@(8),sp@-     | 1er operande
        jsr     a0@
        movl    sp@(20),sp@(4)  | 3eme operande
        movl    d0,sp@          | resultat operation
        jsr     _mpaff
        addql   #8,sp
        movl    d0,a0
        bra     giv

                                | operation a quatre operandes
                                | avec deux resultats de type I

mpopii: movb    sp@(16)@,d0
        addb    sp@(12)@,d0
        cmpb    #2,d0
        beq     mpopz2
        movl    #arier2,sp@-
        jsr     _pari_err

                                | operation a quatre operande

mpopz2: link    a6,#-8
        movl    _avma,a6@(-8)
        pea     a6@(-4)
        movl    a6@(12),sp@-    | 2eme operande
        movl    a6@(8),sp@-     | 1er operande
        jsr     a0@
        addql   #4,sp
        movl    a6@(-4),sp@
        movl    a6@(20),sp@(4)
        bsr     _mpaff          | rangement 2 eme resultat
        movl    d0,sp@
        movl    a6@(16),sp@(4)
        bsr     _mpaff          | rangement 1 er resultat
        addql   #8,sp
        movl    a6@(-8),_avma
        unlk    a6
        rts





#*******************************************************************#
#*******************************************************************#
#**                                                               **#
#**     PROGRAMMES PAR VALEUR UTILISES POUR LA LECTURE-ECRITURE   **#
#**                                                               **#
#*******************************************************************#
#*******************************************************************#





#===================================================================#
#                                                                   #
#       Multiplication par valeur : entier court * entier = entier  #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#                a7@(12) pointe sur i3 de type I                    #
#       sortie : i3 pointe sur s2 * i1                              #
#                                                                   #
#===================================================================#

_mulsii:movl    sp@(8),sp@-
        movl    sp@(8),sp@-
        bsr     _mulsi
        movl    sp@(20),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bra     giv

#===================================================================#
#                                                                   #
#       Addition par valeur : entier court + entier = entier        #
#                                                                   #
#       entree : a7@(4) contient s2 de type S                       #
#                a7@(8) pointe sur i1 de type I                     #
#                a7@(12) pointe sur i3 de type I                    #
#       sortie : i3 pointe sur s2 + i1                              #
#                                                                   #
#===================================================================#

_addsii:movl    sp@(8),sp@-
        movl    sp@(8),sp@-
        bsr     _addsi
        movl    sp@(20),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bra     giv

#===================================================================#
#                                                                   #
#                       division I / S = I                          #
#                                                                   #
#       entree: a7@(4) pointe sur i2, a7@(8) contient s1            #
#               a7@(12) pointe sur un type I                        #
#       sortie: a7@(12) pointe sur i2 div s1                        #
#               d1 contient i2 mod s1                               #
#                                                                   #
#===================================================================#

_divisii:movl   sp@(8),sp@-
        movl    sp@(8),sp@-
        bsr     _divis
        movl    sp@(20),sp@(4)
        movl    d0,sp@
        bsr     _affii
        movl    sp@,a0
        addql   #8,sp
        bra     giv
