/* $Id$ */

/* This file defines some "level 0" kernel functions for SPARC V8 */
/* These are optimised for MicroSparc                             */
/* The following symbols are defined in this file :               */
/* divll bfffo (& tabshi)                                         */
/*   But divll has to use hiremainder, so it is different when    */
/*   hiremainder is inline or not                                 */
/*   If libpari.so is compiled with gcc, you should compile all   */
/*   files with gcc                                               */

#if defined(NO_UNDERSCORE) || defined(linux)
#  define C(entrypoint) entrypoint
#elif defined(sun) || defined(NeXT)
#  ifdef __STDC__
#    define C(entrypoint) _##entrypoint
#  else
#    define C(entrypoint) _/**/entrypoint
#  endif
#endif
#if defined(sun) || defined(linux)
#  define GLOBL .global
#elif defined(NeXT)
#  define GLOBL .globl
#endif

#if   defined(sun) || defined(linux)
	.seg	"data"
	.align	4
C(tabshi): .word	4,3,2,2,1,1,1,1,0,0,0,0,0,0,0,0

	.seg "text"
#elif defined(NeXT)
.data
	.align	3
C(tabshi):
	.long 4
	.long 3
	.long 2
	.long 2
	.long 1
	.long 1
	.long 1
	.long 1
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0
	.long 0

.text
	.align 2
#endif
	GLOBL	C(bfffo),C(divll)

C(bfffo): sethi	%hi(0xffff0000),%o1
	andcc	%o1,%o0,%g0
	bnz,a	1f
	clr	%o2
	sll	%o0,16,%o0
	mov	16,%o2
1:	sethi	%hi(0xff000000),%o1
	andcc	%o1,%o0,%g0
	bnz	2f
	sethi	%hi(0xf0000000),%o1
	sll	%o0,8,%o0
	add	%o2,8,%o2
2:	andcc	%o1,%o0,%g0
	bnz,a	3f
	srl	%o0,28,%o0
	add	%o2,4,%o2
	srl	%o0,24,%o0
3:	set	C(tabshi),%o3
	sll	%o0,2,%o0
	ld	[%o3+%o0],%o1
	retl
	add	%o2,%o1,%o0

#ifdef __GNUC__
C(divll):	 wr	 %g5,%g0,%y
#else /* ! __GNUC__ */
C(divll): sethi	%hi(C(hiremainder)),%o4
	ld	[%o4+%lo(C(hiremainder))],%o2
	wr	%o2,%g0,%y
#endif
	mov	%o0,%o3
	nop
	nop
	udivcc	%o0,%o1,%o0
	bvc	1f
	umul	%o0,%o1,%o5
	mov	0x2f,%o0
	call	C(pari_err),1
	nop
#ifdef __GNUC__
1:	retl
	sub   %o3,%o5,%g5
#else /* ! __GNUC__ */
1:	subcc	%o3,%o5,%o2
	retl
	st	%o2,[%o4+%lo(C(hiremainder))]
#endif
