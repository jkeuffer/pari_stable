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
/* divll                                                          */
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

	GLOBL	C(divll)

C(divll): sethi	%hi(C(hiremainder)),%o4
	ld	[%o4+%lo(C(hiremainder))],%o2
	wr	%o2,%g0,%y
	mov	%o0,%o3
	udivcc	%o0,%o1,%o0
	umul	%o0,%o1,%o5
1:	subcc	%o3,%o5,%o2
	retl
	st	%o2,[%o4+%lo(C(hiremainder))]


#if   defined(sun)
	.type C(divll),#function
#endif
