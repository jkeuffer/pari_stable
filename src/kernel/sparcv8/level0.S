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
/* With gcc, those symbols are inline and defined in level0.h     */
/* overflow hiremainder                                           */
/* addll addllx subll subllx shiftl shiftlr mulll addmul          */

#ifndef __GNUC__
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
	.seg "text"
#elif defined(NeXT)
.text
	.align 2
#endif
	GLOBL	C(addll),C(subll),C(addllx),C(subllx)
	GLOBL	C(shiftl),C(shiftlr),C(shiftl2),C(shiftlr1),C(shiftlr2)
	GLOBL	C(mulll),C(overflow),C(hiremainder),C(addmul)
	
C(addll): sethi	%hi(C(overflow)),%o3
	addcc	%o0,%o1,%o0
	addx	%g0,%g0,%o2
	retl
	st	%o2,[%o3+%lo(C(overflow))]
C(subll): sethi	%hi(C(overflow)),%o3
	subcc	%o0,%o1,%o0
	addx	%g0,%g0,%o2
	retl
	st	%o2,[%o3+%lo(C(overflow))]
C(addllx): sethi	%hi(C(overflow)),%o3
	ld	[%o3+%lo(C(overflow))],%o2
	subcc	%g0,%o2,%g0
	addxcc	%o0,%o1,%o0
	addx	%g0,%g0,%o2
	retl
	st	%o2,[%o3+%lo(C(overflow))]
C(subllx): sethi	%hi(C(overflow)),%o3
	ld	[%o3+%lo(C(overflow))],%o2
	subcc	%g0,%o2,%g0
	subxcc	%o0,%o1,%o0
	addx	%g0,%g0,%o2
	retl
	st	%o2,[%o3+%lo(C(overflow))]
C(shiftl): sethi	%hi(C(hiremainder)),%o3
	neg	%o1,%o4
	srl	%o0,%o4,%o2
	st	%o2,[%o3+%lo(C(hiremainder))]
	retl
	sll	%o0,%o1,%o0
C(shiftl2): sethi	%hi(C(hiremainder)),%o3
	srl	%o0,%o2,%o4
	st	%o4,[%o3+%lo(C(hiremainder))]
	retl
	sll	%o0,%o1,%o0
C(shiftlr): sethi %hi(C(hiremainder)),%o3
	neg	%o1,%o4
	sll	%o0,%o4,%o2
	st	%o2,[%o3+%lo(C(hiremainder))]
	retl
	srl	%o0,%o1,%o0
C(shiftlr1): sethi %hi(C(hiremainder)),%o3
	sll	%o0,31,%o2
	st	%o2,[%o3+%lo(C(hiremainder))]
	retl
	srl	%o0,1,%o0
C(shiftlr2): sethi %hi(C(hiremainder)),%o3
	sll	%o0,%o2,%o4
	st	%o4,[%o3+%lo(C(hiremainder))]
	retl
	srl	%o0,%o1,%o0
	
C(mulll): umul	%o0,%o1,%o0
	sethi	%hi(C(hiremainder)),%o3
	rd	%y,%o2
	retl
	st	%o2,[%o3+%lo(C(hiremainder))]
	
C(addmul): umul	%o0,%o1,%o0
	sethi	%hi(C(hiremainder)),%o3
	ld	[%o3+%lo(C(hiremainder))],%o2
	rd	%y,%o4
	addcc	%o0,%o2,%o0
	addx	%g0,%o4,%o4
	retl
	st	%o4,[%o3+%lo(C(hiremainder))]
	
#if   defined(sun) || defined(linux)
	.seg	"bss"
	.align	4
C(hiremainder): .skip  4
C(overflow): .skip  4
#elif defined(NeXT)
	.comm C(overflow),8
	.comm C(hiremainder),8
#endif
#endif /* !defined(__GNUC__) */
