; $Id$
; 
; Copyright (C) 2000  The PARI group.
; 
; This file is part of the PARI/GP package.
; 
; PARI/GP is free software; you can redistribute it and/or modify it under the
; terms of the GNU General Public License as published by the Free Software
; Foundation. It is distributed in the hope that it will be useful, but WITHOUT
; ANY WARRANTY WHATSOEVER.
; 
; Check the License for details. You should have received a copy of it, along
; with the package; see the file 'COPYING'. If not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

; This file modified by Nigel Smart from the original by Dominique Bernardi.
; HP as is needed, with +DA1.1
	.space  $PRIVATE$,SPNUM=1,PRIVATE,SORT=16
	.subspa $SHORTDATA$,QUAD=0x1,ALIGN=0x8,ACCESS=0x1f,SORT=24
        .import $global$,data        ; The value in the %dp register
	.export	hiremainder,data
	.export	overflow,data
	.word
	.align	8
hiremainder	.comm	4
	.align	8
overflow	.comm	4

        .code
	.export	addll,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	addllx,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	subll,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	subllx,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	bfffo,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	mulll,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	addmul,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	divll,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr

	.proc
	.callinfo
addll	.entry
	addil	lt'overflow,%r19,%r1
	add	%arg0,%arg1,%ret0
	ldw	rt'overflow(%r1),%r20
	addc	0,0,%r22
	stw	%r22,0(%r20)
	.exit
	.procend

	.proc
	.callinfo
addllx	.entry
	addil	lt'overflow,%r19,%r1
	ldw	rt'overflow(%r1),%r20
	ldw	0(%r20),%r22
	addb,uv	%r22,%arg0,addllx2	
	add	%arg0,%arg1,%ret0
	addc	0,0,%r22
	stw	%r22,0(%r20)
	.exit
addllx2 ldi	1,%r22
	stw	%r22,0(%r20)
	.exit	
	.procend

	.proc
	.callinfo
subll	.entry
	addil	lt'overflow,%r19,%r1
	sub	%arg0,%arg1,%ret0
	ldw	rt'overflow(%r1),%r20
	addc	0,0,%r22
	subi	1,%r22,%r22
	stw	%r22,0(%r20)
	.exit
	.procend

	.proc
	.callinfo
subllx	.entry
	addil	lt'overflow,%r19,%r1
	ldw	rt'overflow(%r1),%r20
	ldw	0(%r20),%r22
	sub,>>=	%arg0,%arg1,%ret0
	sub,tr	%ret0,%r22,%ret0
	sub,>>=	%ret0,%r22,%ret0
	addi,tr	1,0,%r22
	ldi	0,%r22
	stw	%r22,0(%r20)
	.exit
	.procend

	.proc
	.callinfo
bfffo	.entry
	comb,=,n	%r0,%arg0,l$0
	ldi	31,%ret0
	extru,<>	%arg0,15,16,%r0
	shd,tr	%arg0,%r0,16,%arg0
	addi	-16,%ret0,%ret0
	extru,<>	%arg0,7,8,%r0
	shd,tr	%arg0,%r0,24,%arg0
	addi	-8,%ret0,%ret0
	extru,<>	%arg0,3,4,%r0
	shd,tr	%arg0,%r0,28,%arg0
	addi	-4,%ret0,%ret0
	extru,<>	%arg0,1,2,%r0
	shd,tr	%arg0,%r0,30,%arg0
	addi	-2,%ret0,%ret0
	extru,=	%arg0,0,1,%r0
	addi	-1,%ret0,%ret0
	b,n	l$1
l$0	ldi	32,%ret0
l$1	.exit
	.procend
	
	.proc
	.callinfo
mulll	.entry
	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%r20
	stw	%arg0,0(%r20)
	fldws	0(%r20),%fr4
	stw	%arg1,0(%r20)
	fldws	0(%r20),%fr5
	xmpyu	%fr4,%fr5,%fr6
	fstds	%fr6,0(%r20)
	ldws	4(%r20),%ret0
	.exit
	.procend

	.proc
	.callinfo
addmul	.entry
	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%r20
	ldw	0(%r20),%r22
	stw	%arg0,0(%r20)
	fldws	0(%r20),%fr4
	stw	%arg1,0(%r20)
	fldws	0(%r20),%fr5
	xmpyu	%fr4,%fr5,%fr6
	fstds	%fr6,0(%r20)
	ldws	4(%r20),%ret0
	add,nuv	%r22,%ret0,%ret0
	b,n	suite
	.exit
suite	ldw	0(%r20),%ret1
	addi	1,%ret1,%ret1
	stw	%ret1,0(%r20)
	.exit
	.procend

hirem	.reg	%r22
loquo	.reg	%ret0
div	.reg	%arg1

nibble	.macro
	ds	hirem,div,hirem
	addc	loquo,loquo,loquo
	ds	hirem,div,hirem
	addc	loquo,loquo,loquo
	ds	hirem,div,hirem
	addc	loquo,loquo,loquo
	ds	hirem,div,hirem
	addc	loquo,loquo,loquo
	.endm
			
divll	.proc
	.callinfo
	.entry
	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%r20
	ldw	0(%r20),hirem

	comb,<	div,0,l$50
	copy	%arg0,loquo
	sub	0,div,%r21
	ds	0,%r21,0
	addc	loquo,loquo,loquo
	nibble
	nibble
	nibble
	nibble
	nibble
	nibble
	nibble
	nibble
	add,>=	0,hirem,0
	add	hirem,div,hirem
	stw	hirem,0(%r20)
	.exit
	
l$50	copy	div,%arg0
	extru,<>	div,31,1,%r20
	b	l$51
	extru	div,30,31,div
	addb,nsv	%r20,div,l$51
	copy	hirem,%r1
	copy	loquo,hirem
	b	l$52
	copy	%r1,loquo
	
l$51	extru	loquo,31,1,%r1
	shd	hirem,loquo,1,loquo
	extru	hirem,30,31,hirem
	sub	0,div,%r21
	ds	0,%r21,0
	addc	loquo,loquo,loquo
	nibble
	nibble
	nibble
	nibble
	nibble
	nibble
	nibble
	nibble
	add,>=	0,hirem,0
	add	hirem,div,hirem
	comb,=	0,%r20,l$53
	sh1add	hirem,%r1,hirem
l$52	copy	%arg0,div
	addb,nuv,n	loquo,hirem,l$54
	sub	hirem,div,hirem
	addi	1,loquo,loquo
l$54	comb,<<,n	hirem,div,l$53
	sub	hirem,div,hirem
	addi	1,loquo,loquo
	
l$53	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%r20
	stw	hirem,0(%r20)
	.exit	
	.procend

	.end
