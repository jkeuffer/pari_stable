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

/* This file defines some "level 0" kernel functions for SPARC V8 */
/* These are optimised for MicroSparc                             */
/* The following symbols are defined in this file :               */
/* divll bfffo (& tabshi)                                         */
/*   But divll has to use hiremainder, so it is different when    */
/*   hiremainder is inline or not                                 */
/*   If libpari.so is compiled with gcc, you should compile all   */
/*   files with gcc                                               */

#if defined(NO_UNDERSCORE) || defined(linux) || defined(__NetBSD__)
#  define C(entrypoint) entrypoint
#elif defined(sun) || defined(NeXT)
#  ifdef __STDC__
#    define C(entrypoint) _##entrypoint
#  else
#    define C(entrypoint) _/**/entrypoint
#  endif
#endif
#if defined(sun) || defined(linux) || defined(__NetBSD__)
#  define GLOBL .global
#elif defined(NeXT)
#  define GLOBL .globl
#endif

#if   defined(sun) || defined(linux) || defined(__NetBSD__)
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

C(divll): sethi	%hi(C(hiremainder)),%o4
	ld	[%o4+%lo(C(hiremainder))],%o2
	wr	%o2,%g0,%y
	mov	%o0,%o3
	udivcc	%o0,%o1,%o0
	umul	%o0,%o1,%o5
1:	subcc	%o3,%o5,%o2
	retl
	st	%o2,[%o4+%lo(C(hiremainder))]
