; $id: level0.s,v 2.0.0.6 1998/02/21 17:30:11 karim exp karim $
; This file modified by Nigel Smart from the original by Dominique Bernardi.
; HP as is needed, with +DA1.1
	.shortdata
        .import $global$        ; The value in the %dp register
	.export	hiremainder
	.export	overflow
	.word
	.align	8
hiremainder	.word
	.align	8
overflow	.word

        .code
	.export	addll,entry
	.export	addllx,entry
	.export	subll,entry
	.export	subllx,entry
	.export	shiftl,entry
	.export	shiftlr,entry
	.export	bfffo,entry
	.export	mulll,entry
 	.export	addmul,entry
	.export	divll,entry

	.proc
	.callinfo
addll	.enter
	add	%arg0,%arg1,%ret0
	addc	0,0,%t1
	stw	%t1,overflow-$global$(%dp)
	.leave
	.procend

	.proc
	.callinfo
addllx	.enter
	ldw	overflow-$global$(%dp),%t1
	addb,uv	%t1,%arg0,addllx2	
	add	%arg0,%arg1,%ret0
	addc	0,0,%t1
	stw	%t1,overflow-$global$(%dp)
	.leave
addllx2	ldi	1,%t1
	stw	%t1,overflow-$global$(%dp)
	.leave	
	.procend

	.proc
	.callinfo
subll	.enter
	sub	%arg0,%arg1,%ret0
	addc	0,0,%t1
	subi	1,%t1,%t1
	stw	%t1,overflow-$global$(%dp)
	.leave
	.procend

	.proc
	.callinfo
subllx	.enter
	ldw	overflow-$global$(%dp),%t1
	sub,>>=	%arg0,%arg1,%ret0
	sub,tr	%ret0,%t1,%ret0
	sub,>>=	%ret0,%t1,%ret0
	addi,tr	1,0,%t1
	ldi	0,%t1
	stw	%t1,overflow-$global$(%dp)
	.leave
	.procend

	.proc
	.callinfo
shiftl	.enter
	subi	32,%arg1,%arg1
l$30	mfctl	%cr11,%t1
	mtctl	%arg1,%cr11
	vshd	%arg0,0,%ret0;
	vshd	0,%arg0,%t2
	mtctl	%t1,%cr11
l$31	stw	%t2,hiremainder-$global$(%dp)
	.leave
	.procend

	.proc
	.callinfo
shiftlr	.enter
l$40	mfctl	%cr11,%t1
	mtctl	%arg1,%cr11
	vshd	0,%arg0,%ret0;
	vshd	%arg0,0,%t2
	mtctl	%t1,%cr11
l$41	stw	%t2,hiremainder-$global$(%dp)
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
	ldo	hiremainder-$global$(%dp),%r1
	stw	%arg0,0(%r1)
	fldws	0(%r1),%fr4
	stw	%arg1,0(%r1)
	fldws	0(%r1),%fr5
	xmpyu	%fr4,%fr5,%fr6
	fstds	%fr6,0(%r1)
	ldws	4(%r1),%ret0
	.leave
	.procend

	.proc
	.callinfo
addmul	.enter
	ldo	hiremainder-$global$(%dp),%r1
	ldw	0(%r1),%t1
	stw	%arg0,0(%r1)
	fldws	0(%r1),%fr4
	stw	%arg1,0(%r1)
	fldws	0(%r1),%fr5
	xmpyu	%fr4,%fr5,%fr6
	fstds	%fr6,0(%r1)
	ldws	4(%r1),%ret0
	add,nuv	%t1,%ret0,%ret0
	b,n	suite
	.leave
suite	ldw	0(%r1),%ret1
	addi	1,%ret1,%ret1
	stw	%ret1,0(%r1)
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
	ldw	hiremainder-$global$(%dp),hirem

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
	stw	hirem,hiremainder-$global$(%dp)
	.leave
	
l$50	copy	div,%arg0
	extru,<>	div,31,1,%t3
	b	l$51
	extru	div,30,31,div
	addb,nsv	%t3,div,l$51
	copy	hirem,%t4
	copy	loquo,hirem
	b	l$52
	copy	%t4,loquo
	
l$51	extru	loquo,31,1,%t4
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
	sh1add	hirem,%t4,hirem
l$52	copy	%arg0,div
	addb,nuv,n	loquo,hirem,l$54
	sub	hirem,div,hirem
	addi	1,loquo,loquo
l$54	comb,<<,n	hirem,div,l$53
	sub	hirem,div,hirem
	addi	1,loquo,loquo
	
l$53	stw	hirem,hiremainder-$global$(%dp)
	.leave	
	.procend

	.end
