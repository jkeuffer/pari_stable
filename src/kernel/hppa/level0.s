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
	.shortdata
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
	.export	shiftl,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	shiftlr,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	bfffo,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	mulll,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	addmul,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr
	.export	divll,entry,priv_lev=3,argw0=gr,argw1=gr,rtnval=gr

	.proc
	.callinfo
addll	.enter
	addil	lt'overflow,%r19,%r1
	add	%arg0,%arg1,%ret0
	ldw	rt'overflow(%r1),%t3
	addc	0,0,%t1
	stw	%t1,0(%t3)
	.leave
	.procend

	.proc
	.callinfo
addllx	.enter
	addil	lt'overflow,%r19,%r1
	ldw	rt'overflow(%r1),%t3
	ldw	0(%t3),%t1
	addb,uv	%t1,%arg0,addllx2	
	add	%arg0,%arg1,%ret0
	addc	0,0,%t1
	stw	%t1,0(%t3)
	.leave
addllx2 ldi	1,%t1
	stw	%t1,0(%t3)
	.leave	
	.procend

	.proc
	.callinfo
subll	.enter
	addil	lt'overflow,%r19,%r1
	sub	%arg0,%arg1,%ret0
	ldw	rt'overflow(%r1),%t3
	addc	0,0,%t1
	subi	1,%t1,%t1
	stw	%t1,0(%t3)
	.leave
	.procend

	.proc
	.callinfo
subllx	.enter
	addil	lt'overflow,%r19,%r1
	ldw	rt'overflow(%r1),%t3
	ldw	0(%t3),%t1
	sub,>>=	%arg0,%arg1,%ret0
	sub,tr	%ret0,%t1,%ret0
	sub,>>=	%ret0,%t1,%ret0
	addi,tr	1,0,%t1
	ldi	0,%t1
	stw	%t1,0(%t3)
	.leave
	.procend

	.proc
	.callinfo
shiftl	.enter
	addil	lt'hiremainder,%r19,%r1
	subi	32,%arg1,%arg1
	ldw	rt'hiremainder(%r1),%t3
l$30	mfctl	%cr11,%t1
	mtctl	%arg1,%cr11
	vshd	%arg0,0,%ret0;
	vshd	0,%arg0,%t2
	mtctl	%t1,%cr11
l$31	stw	%t2,0(%t3)
	.leave
	.procend

	.proc
	.callinfo
shiftlr	.enter
	addil	lt'hiremainder,%r19,%r1
l$40	mfctl	%cr11,%t1
	mtctl	%arg1,%cr11
	ldw	rt'hiremainder(%r1),%t3
	vshd	0,%arg0,%ret0;
	vshd	%arg0,0,%t2
	mtctl	%t1,%cr11
l$41	stw	%t2,0(%t3)
	.leave
	.procend

	.proc
	.callinfo
bfffo	.enter
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
l$1	.leave
	.procend
	
	.proc
	.callinfo
mulll	.enter
	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%t3
	stw	%arg0,0(%t3)
	fldws	0(%t3),%fr4
	stw	%arg1,0(%t3)
	fldws	0(%t3),%fr5
	xmpyu	%fr4,%fr5,%fr6
	fstds	%fr6,0(%t3)
	ldws	4(%t3),%ret0
	.leave
	.procend

	.proc
	.callinfo
addmul	.enter
	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%t3
	ldw	0(%t3),%t1
	stw	%arg0,0(%t3)
	fldws	0(%t3),%fr4
	stw	%arg1,0(%t3)
	fldws	0(%t3),%fr5
	xmpyu	%fr4,%fr5,%fr6
	fstds	%fr6,0(%t3)
	ldws	4(%t3),%ret0
	add,nuv	%t1,%ret0,%ret0
	b,n	suite
	.leave
suite	ldw	0(%t3),%ret1
	addi	1,%ret1,%ret1
	stw	%ret1,0(%t3)
	.leave
	.procend

hirem	.reg	%t1
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
	.enter
	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%t3
	ldw	0(%t3),hirem

	comb,<	div,0,l$50
	copy	%arg0,loquo
	sub	0,div,%t2
	ds	0,%t2,0
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
	stw	hirem,0(%t3)
	.leave
	
l$50	copy	div,%arg0
	extru,<>	div,31,1,%t3
	b	l$51
	extru	div,30,31,div
	addb,nsv	%t3,div,l$51
	copy	hirem,%r1
	copy	loquo,hirem
	b	l$52
	copy	%r1,loquo
	
l$51	extru	loquo,31,1,%r1
	shd	hirem,loquo,1,loquo
	extru	hirem,30,31,hirem
	sub	0,div,%t2
	ds	0,%t2,0
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
	comb,=	0,%t3,l$53
	sh1add	hirem,%r1,hirem
l$52	copy	%arg0,div
	addb,nuv,n	loquo,hirem,l$54
	sub	hirem,div,hirem
	addi	1,loquo,loquo
l$54	comb,<<,n	hirem,div,l$53
	sub	hirem,div,hirem
	addi	1,loquo,loquo
	
l$53	addil	lt'hiremainder,%r19,%r1
	ldw	rt'hiremainder(%r1),%t3
	stw	hirem,0(%t3)
	.leave	
	.procend

	.end
