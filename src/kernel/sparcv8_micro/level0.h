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

#ifdef ASMINLINE
#define divll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__( "wr      %1,%%g0,%%y;\
         mov     %2,%%o4;\
	 udivcc  %2,%3,%0;\
         umul    %0,%3,%%o5;\
	 sub     %%o4,%%o5,%1"\
	: "=r" (__value), "=r" (hiremainder) \
	: "r" (__arg1), "r" (__arg2), "1" (hiremainder) \
        : "%o4","%o5","cc");	\
__value;})								
#endif
