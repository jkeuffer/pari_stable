; $Id$
	import hiremainder,overflow
	
	toc
		tc hiremainder[TC], hiremainder
		tc overflow[TC], overflow
	
	export addll[DS],.addll[PR],addllx[DS],.addllx[PR]
	export subll[DS],.subll[PR],subllx[DS],.subllx[PR]
	export mulll[DS],.mulll[PR],addmul[DS],.addmul[PR]
	export divll[DS],.divll[PR],bfffo[DS],.bfffo[PR]

	toc
		tc addll[TC], addll[DS]
		tc addllx[TC], addllx[DS]
		tc subll[TC], subll[DS]
		tc subllx[TC], subllx[DS]
		tc mulll[TC], mulll[DS]
		tc addmul[TC], addmul[DS]
		tc divll[TC], divll[DS]
		tc bfffo[TC], bfffo[DS]
	
	csect	addll[DS]
		dc.l	.addll[PR]
		dc.l	TOC[tc0]
		dc.l	0
		
	csect	.addll[PR]
		addc	r3,r3,r4
		subfe	r5,r5,r5
		addi	r5,r5,1
		lwz		r6,overflow{TC}(RTOC)
		stw		r5,0x0000(r6)
		blr

	csect	addllx[DS]
		dc.l	.addllx[PR]
		dc.l	TOC[tc0]
		dc.l	0

	csect	.addllx[PR]
		addc	r3,r3,r4
		subfe	r5,r5,r5
		lwz		r6,overflow{TC}(RTOC)
		lwz		r7,0x0000(r6)
		addc	r3,r7,r3
		subfe	r8,r8,r8
		addc	r5,r8,r5
		addi	r5,r5,2
		stw		r5,0x0000(r6)
		blr

	csect	subll[DS]
		dc.l	.subll[PR]
		dc.l	TOC[tc0]
		dc.l	0
		
	csect	.subll[PR]
		subfc	r3,r4,r3
		subfe	r5,r5,r5
		neg		r5,r5
		lwz		r6,overflow{TC}(RTOC)
		stw		r5,0x0000(r6)
		blr

	csect	subllx[DS]
		dc.l	.subllx[PR]
		dc.l	TOC[tc0]
		dc.l	0

	csect	.subllx[PR]
		subfc	r3,r4,r3
		subfe	r5,r5,r5
		lwz		r6,overflow{TC}(RTOC)
		lwz		r7,0x0000(r6)
		subfc	r3,r7,r3
		subfe	r8,r8,r8
		addc	r5,r8,r5
		neg		r5,r5
		stw		r5,0x0000(r6)
		blr

	csect	mulll[DS]
		dc.l	.mulll[PR]
		dc.l	TOC[tc0]
		dc.l	0
		
	csect	.mulll[PR]
	
; version PowerPC, plus lente
;		mulhwu	r5,r3,r4
;		lwz		r6,hiremainder{TC}(RTOC)
;		stw		r5,0x0000(r6)
;		mullw	r3,r3,r4
;		blr
; version POWER
		lwz		r6,hiremainder{TC}(RTOC)
		dialect	POWER
		mul		r5,r3,r4
		dialect	POWERPC
		cmpwi	r3,0
		bge		@1
		add		r5,r5,r4
@1		cmpwi	r4,0
		bge		@2
		add		r5,r5,r3
@2		stw		r5,0x0000(r6)
		mfspr	r3,mq
		blr

	csect	addmul[DS]
		dc.l	.addmul[PR]
		dc.l	TOC[tc0]
		dc.l	0
		
	csect	.addmul[PR]
; version PowerPC, plus lente
;		mulhwu	r5,r3,r4
;		mullw	r3,r3,r4
;		lwz		r6,hiremainder{TC}(RTOC)
;		lwz		r7,0x0000(r6)
;		addc	r3,r7,r3
;		addze	r5,r5
;		stw		r5,0x0000(r6)
;		blr
; version POWER
		lwz		r6,hiremainder{TC}(RTOC)
		dialect	POWER
		mul		r5,r3,r4
		dialect	POWERPC
		cmpwi	r3,0
		bge		@1
		add		r5,r5,r4
@1		cmpwi	r4,0
		bge		@2
		add		r5,r5,r3
@2		lwz		r7,0x0000(r6)
		mfspr	r3,mq
		addc	r3,r7,r3
		addze	r5,r5
		stw		r5,0x0000(r6)
		blr

	csect	divll[DS]
		dc.l	.divll[PR]
		dc.l	TOC[tc0]
		dc.l	0
		
	csect	.divll[PR]
	
; version POWER
; chargement de a puis a1 dans r5, b puis b1 dans r3 et c puis c1 dans r4
		lwz		r6,hiremainder{TC}(RTOC)
		lwz		r5,0x0000(r6)

; etape 1, f est code dans cr5, eb dans r7 et ec dans cr6
; si f = 1, on garde une copie de c dans r10
		cmpwi	5,r4,0
		bge		5,@1
		andi.	r7,r4,1
		mcrf	6,0
		mr		r10,r4
		srwi	r4,r4,1
		andi.	r7,r3,1
		srwi	r3,r3,1
		rlwimi	r3,r5,31,0,0
		srwi	r5,r5,1

; modif
		cmplw	r5,r4
		bne		@1
		slwi	r3,r3,1
		add		r3,r3,r7
		addc	r4,r3,r10
		subfe.	r5,r5,r5
		li		r3,-1
		beq		@5
		subi	r3,r3,1
		add		r4,r10,r4
		b		@5
		
; etape 2 r3 recoit q et mq recoit r
@1		add		r8,r5,r5
		addi	r8,r8,1
		cmplw	r4,r8
		bgt		@2
		bne		@3
		cmpwi	r3,0
		bge		@2
@3		slwi	r9,r4,31
		srwi	r8,r4,1
		subfc	r3,r9,r3
		subfe	r5,r8,r5
		mtspr	mq,r3
		dialect	POWER
		div		r3,r5,r4
		dialect	POWERPC
		mfspr	r4,mq
		oris	r3,r3,0x8000
		b		@4
@2		mtspr	mq,r3
		dialect	POWER
		div		r3,r5,r4
		dialect	POWERPC
		mfspr	r4,mq

; etape 3 r4 recoit r
@4		bge		5,@5
		slwi	r4,r4,1
		add		r4,r4,r7
		beq		6,@5

; etape 4 modifiee
		subfc	r4,r3,r4
		subfe.	r5,r5,r5
		beq		@5
		subi	r3,r3,1
		addc	r4,r4,r10
		subfe.	r5,r5,r5
		beq		@5
		subi	r3,r3,1
		addc	r4,r4,r10

; retour
@5		stw		r4,0x0000(r6)
		blr
		
	csect	bfffo[DS]
		dc.l	.bfffo[PR]
		dc.l	TOC[tc0]
		dc.l	0
		
	csect	.bfffo[PR]
		cntlzw	r3,r3
		blr

