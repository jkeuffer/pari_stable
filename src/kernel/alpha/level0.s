# $Id$
#
# Copyright (C) 2000  The PARI group.
#
# This file is part of the PARI/GP package.
#
# PARI/GP is free software; you can redistribute it and/or modify it under the
# terms of the GNU General Public License as published by the Free Software
# Foundation. It is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY WHATSOEVER.
#
# Check the License for details. You should have received a copy of it, along
# with the package; see the file 'COPYING'. If not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

	.text	

        .set noreorder
        .align 3
        .globl addll
        .ent addll 0
addll:	
        .frame $30,0,$26,0
        .prologue 0
	addq	$16,$17,$0
	cmpult	$0,$16,$1
	stq	$1,overflow
	ret	$31,($26),1
	.end	addll			

        .set noreorder
        .align 3
        .globl addllx
        .ent addllx 0
addllx:	
	ldq     $2,overflow
        addq    $16,$17,$0
        cmpult  $0,$16,$16
        addq    $0,$2,$0
        cmpult  $0,$2,$2
        addq    $16,$2,$16
        stq     $16,overflow
        ret     $31,($26),1
        .end    addllx

	
        .set noreorder
        .align 3
        .globl subll
        .ent subll 0
subll:	
        .frame $30,0,$26,0
        .prologue 0
	subq	$16,$17,$0
	cmpult	$16,$0,$1
	stq	$1,overflow
	ret	$31,($26),1
	.end	subll			

        .set noreorder
        .align 3
        .globl subllx
        .ent subllx 0
subllx:	
	.frame $30,0,$26,0
        .prologue 0
        ldq $2,overflow
        subq $16,$17,$17
        cmpult $16,$17,$16
        subq $17,$2,$0
        cmpult $17,$0,$17
        addq $16,$17,$16
        stq $16,overflow
        ret $31,($26),1
        .end subllx

        .set noreorder
        .align 3
        .globl shiftl
        .ent shiftl 0
shiftl:	
        .frame $30,0,$26,0
        .prologue 0
	subq	$31,$17,$1
	sll	$16,$17,$0
	srl	$16,$1,$2
	stq	$2,hiremainder
	ret	$31,($26),1
	.end	shiftl

        .set noreorder
        .align 3
        .globl shiftlr
        .ent shiftlr 0
shiftlr:	
        .frame $30,0,$26,0
        .prologue 0
	subq	$31,$17,$1
	srl	$16,$17,$0
	sll	$16,$1,$2
	stq	$2,hiremainder
	ret	$31,($26),1
	.end	shiftlr

        .set noreorder
        .align 3
        .globl bfffo
        .ent bfffo 0
bfffo:	
        .frame $30,0,$26,0
        .prologue 0
	lda	$6,tabshi
	ldiq	$7,60
	zapnot	$16,0xf0,$1
	beq	$1,$32
	srl	$16,32,$16
	subq	$7,32,$7
$32:	lda	$3,-1($31)
	ldah	$3, 1($3)
	cmpule	$16,$3,$2
	bne	$2,$33
	srl	$16,16,$16
	subq	$7,16,$7
$33:	cmpule	$16,0xff,$3
	bne	$3,$34
	srl	$16,8,$16
	subq	$7,8,$7
$34:	cmpule	$16,0xf,$4
	bne	$4,$35
	srl	$16,4,$16
	subq	$7,4,$7
$35:	s8addq	$16,$6,$5
	ldq	$1,0($5)
	addq	$1,$7,$0
	ret	$31,($26),1
	.end	bfffo
	
        .set noreorder
        .align 3
        .globl mulll
        .ent mulll 0
mulll:	
        .frame $30,0,$26,0
        .prologue 0
	umulh	$16,$17,$1
	mulq	$16,$17,$0
	stq	$1,hiremainder
	ret	$31,($26),1
	.end	mulll

        .set noreorder
        .align 3
        .globl addmul
        .ent addmul 0
addmul:	
        .frame $30,0,$26,0
        .prologue 0
	mulq	$16,$17,$2
	umulh	$16,$17,$1
	ldq	$3,hiremainder
	addq	$2,$3,$0
	cmpult	$0,$2,$4
	addq	$1,$4,$5
	stq	$5,hiremainder
	ret	$31,($26),1
	.end	addmul
		
 # This program is a modification of a file contained in the gmp-1.9
 # library, copyright Free Software Foundation, with permission.
	.globl	pari_err
        .set noreorder
        .align 3
        .globl divll
        .ent divll 0
divll:	
        .frame $30,0,$26,0
        .prologue 0

	ldq	$7,hiremainder
	ldiq	$2,16
	cmpule	$17,$7,$3
	bne	$3,errorhandler
	blt	$17,Largedivisor

Loop1:	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$17,$7,$20
	subq	$7,$17,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$17,$7,$20
	subq	$7,$17,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$17,$7,$20
	subq	$7,$17,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$17,$7,$20
	subq	$7,$17,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	subq	$2,1,$2
	bgt	$2,Loop1
	stq	$7,hiremainder
	bis	$31,$16,$0
	ret	$31,($26),1

Largedivisor:
	and	$16,1,$4

	srl	$16,1,$16
	sll	$7,63,$3
	or	$3,$16,$16
	srl	$7,1,$7

	and	$17,1,$6
	srl	$17,1,$5
	addq	$5,$6,$5

Loop2:	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$5,$7,$20
	subq	$7,$5,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$5,$7,$20
	subq	$7,$5,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$5,$7,$20
	subq	$7,$5,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	cmplt	$16,0,$3
	addq	$7,$7,$7
	bis	$7,$3,$7
	addq	$16,$16,$16
	cmpule	$5,$7,$20
	subq	$7,$5,$3
	cmovne	$20,$3,$7
	bis	$16,$20,$16
	subq	$2,1,$2
	bgt	$2,Loop2

	addq	$7,$7,$7
	addq	$4,$7,$7
	bne	$6,Odd
	stq	$7,hiremainder
	bis	$31,$16,$0
	ret	$31,($26),1

Odd:
	# q' in $16. r' in $7
	addq	$7,$16,$7
	cmpult	$7,$16,$3	# $3 := carry from addq
	beq	$3,LLp6
	addq	$16,1,$16
	subq	$7,$17,$7
LLp6:	cmpult	$7,$17,$3
	bne	$3,LLp7
	addq	$16,1,$16
	subq	$7,$17,$7
LLp7:
	stq	$7,hiremainder
	bis	$31,$16,$0
	ret	$31,($26),1

errorhandler:
	ldiq	$16,0x2f
	jmp	pari_err
	
	.end	divll

	.align	3
tabshi:	.quad	4,3,2,2,1,1,1,1,0,0,0,0,0,0,0,0
	.globl	hiremainder
	.comm	hiremainder,8
	.globl	overflow
	.comm	overflow,8
