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

/* The following symbols are defined in this file: bfffo (& tabshi) */

#if   defined(sun)
      .type C(tabshi),#object
      .size C(tabshi),64
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
	GLOBL	C(bfffo)

C(bfffo): sethi	%hi(65535),%o2
	or	%o2,%lo(65535),%o2
	cmp	%o0,%o2
	bleu	1f
	mov	28,%o1
	mov	12,%o1
	srl	%o0,16,%o0
1:	cmp	%o0,255
	bleu	2f
	cmp	%o0,15
	add	%o1,-8,%o1
	srl	%o0,8,%o0
	cmp	%o0,15
2:	bleu	3f
	sethi	%hi(C(tabshi)),%o2
	add	%o1,-4,%o1
	srl	%o0,4,%o0
3:	or	%o2,%lo(C(tabshi)),%o2
	sll	%o0,2,%o3
	ld	[%o3+%o2],%o0
	retl
	add	%o1,%o0,%o0

#if   defined(sun)
      .type C(bfffo),#function
#endif
