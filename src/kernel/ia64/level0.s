	.section	.rodata
	.align 16
.LC0:	data4 0x00000000, 0x80000000, 0x0000403f, 0x00000000	
	data4 0x00000000, 0x80000000, 0x0000407f, 0x00000000	

	
	.text
	.align	16
	.global	invert_word
	.proc	invert_word#
invert_word:	
	addl		r14 = @ltoff(.LC0),gp
	add		r8 = r32,r32;;			
	ld8		r14 = [r14]
	cmp.eq		p6,p7 = 0,r8;;			
	ldfe		f10 = [r14],16			
	setf.sig	f7 = r32
	mov		r8 = -1
   (p6)	br.ret.spnt	b0;;
	ldfe		f8 = [r14]			
	fmpy.s1		f11 = f7,f10;;			
	fsub.s1		f6 = f8,f11;;
	frcpa.s1	f8,p6 = f6,f7;;
   (p6) fnma.s1		f9 = f7,f8,f1
   (p6) fmpy.s1		f10 = f6,f8;;
   (p6) fmpy.s1		f11 = f9,f9
   (p6) fma.s1		f10 = f9,f10,f10;;
   (p6) fma.s1		f8 = f9,f8,f8
   (p6) fma.s1		f9 = f11,f10,f10;;
   (p6) fma.s1		f8 = f11,f8,f8
   (p6) fnma.s1		f10 = f7,f9,f6;;
   (p6) fma.s1		f8 = f10,f8,f9;;
	fcvt.fxu.trunc.s1 f8 = f8;;
	xmpy.hu		f10 = f8,f7;;			
	getf.sig	r8 = f8
	getf.sig	r14 = f10;;
	add		r32 = r32,r14;;
	cmp.ltu		p6,p7 = r32,r14;;		
   (p6) add		r8 = -1,r8			
	br.ret.sptk	b0
	
	.endp	invert_word#
