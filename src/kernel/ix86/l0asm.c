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

/***********************************************************************/
/**								      **/
/**		       Low level arithmetic for PARI		      **/
/**                   written by Bruno Haible 14.11.1992              **/
/**                        macroified 21.1.1998                       **/
/**								      **/
/***********************************************************************/

/* processor: Intel ix86 in native mode
 * assembler syntax: GNU or SUN, moves go from left to right
 * compiler: GNU gcc or SUN cc
 * parameter passing convention: on the stack 4(%esp),8(%esp),...
 * registers: %eax,%edx,%ecx may be modified,
 *            everything else must be saved and restored
 * result: passed in %eax
 * word length: 32 bits
 */

/* If the C compiler is GNU C, better stuff is contained in asmix86inline.h,
   but we compile and link this file nevertheless because it defines the
   global variable `hiremainder'. */

/* This should ideally be determined at configure time. */
#if defined(__EMX__) || defined(__DJGCC__) || defined(__GO32__) || (defined(linux) && !defined(__ELF__)) || defined(__386BSD__) || defined(__NetBSD__) || (defined(__FreeBSD__) && !defined(__ELF__)) || defined(NeXT) || defined(__CYGWIN32__) || defined(__MINGW32__)
#  define ASM_UNDERSCORE
#endif

#include "l0asm.h"

#if defined(__EMX__) && defined(__NO_AOUT) /* No underscores, rest as is */
#   undef C
#   define C(entrypoint) /**/entrypoint
#endif


#undef ALIGN
#ifdef _MSC_VER
  #define ALIGN
#else
#if defined(ASM_UNDERSCORE) && !(defined(__CYGWIN32__) || defined(__MINGW32__))
  /* BSD syntax assembler */
  #define ALIGN  .align 3
#else
  /* ELF syntax assembler */
  #define ALIGN  .align 8
#endif
#endif

        GLOBL(C(addll))
        GLOBL(C(subll))
        GLOBL(C(addllx))
        GLOBL(C(subllx))
        GLOBL(C(shiftl))
        GLOBL(C(shiftlr))
        GLOBL(C(bfffo))
        GLOBL(C(mulll))
        GLOBL(C(addmul))
        GLOBL(C(divll))
        GLOBL(C(overflow))
        GLOBL(C(hiremainder))

#ifdef _MSC_VER
unsigned long overflow, hiremainder;
#else
#ifdef BSD_SYNTAX
#  if defined(__EMX__) && defined(__NO_AOUT) /* Otherwise IBM linker will
					        ignore this module */
.data
.align 2
C(overflow):
    .long 0
C(hiremainder):
    .long 0
.text
#  else
.comm C(overflow),4
.comm C(hiremainder),4
#  endif
#endif
#ifdef ELF_SYNTAX
.comm C(overflow),4,4
.comm C(hiremainder),4,4
#endif
#endif

TEXT()

	ALIGN
FUNBEGIN(addll)
        INSN2(xor,l     ,R(edx),R(edx))             /* clear %edx    */
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x         */
        INSN2(add,l     ,X4 MEM_DISP(esp,8),R(eax)) /* add y         */
        INSN2(adc,l     ,R(edx),R(edx))             /* %edx := carry */
        INSN2(mov,l     ,R(edx),C(overflow))        /* set overflow  */
	ret                                         /* return %eax   */
FUNEND()

	ALIGN
FUNBEGIN(addllx)
        INSN2(xor,l     ,R(edx),R(edx))             /* clear %edx      */
        INSN2(xor,l     ,R(eax),R(eax))             /* clear %eax      */
        INSN2(sub,l     ,C(overflow),R(eax))        /* set carry       */
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x           */
        INSN2(adc,l     ,X4 MEM_DISP(esp,8),R(eax)) /* add y and carry */
        INSN2(adc,l     ,R(edx),R(edx))             /* %edx := carry   */
        INSN2(mov,l     ,R(edx),C(overflow))        /* set overflow    */
	ret                                         /* return %eax     */
FUNEND()

	ALIGN
FUNBEGIN(subll)
        INSN2(xor,l     ,R(edx),R(edx))             /* clear %edx    */
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x         */
        INSN2(sub,l     ,X4 MEM_DISP(esp,8),R(eax)) /* subtract y    */
        INSN2(adc,l     ,R(edx),R(edx))             /* %edx := carry */
        INSN2(mov,l     ,R(edx),C(overflow))        /* set overflow  */
	ret                                         /* return %eax   */
FUNEND()

	ALIGN
FUNBEGIN(subllx)
        INSN2(xor,l     ,R(edx),R(edx))             /* clear %edx           */
        INSN2(xor,l     ,R(eax),R(eax))             /* clear %eax           */
        INSN2(sub,l     ,C(overflow),R(eax))        /* set carry            */
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x                */
        INSN2(sbb,l     ,X4 MEM_DISP(esp,8),R(eax)) /* subtract y and carry */
        INSN2(adc,l     ,R(edx),R(edx))             /* %edx := carry        */
        INSN2(mov,l     ,R(edx),C(overflow))        /* set overflow         */
	ret                                         /* return %eax          */
FUNEND()

	ALIGN
FUNBEGIN(shiftl)
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x                          */
        INSN2(mov,b     ,X1 MEM_DISP(esp,8),R(cl))  /* get shift count i              */
        INSN2(xor,l     ,R(edx),R(edx))             /* clear %edx                     */
        INSN2SHCL(shld,l,R(eax),R(edx))             /* shift %edx left by i bits,
                                                       feeding in %eax from the right */
        INSN2(shl,l     ,R(cl),R(eax))              /* shift %eax left by i bits      */
        INSN2(mov,l     ,R(edx),C(hiremainder))     /* set hiremainder                */
	ret                                         /* return %eax                    */
FUNEND()

	ALIGN
FUNBEGIN(shiftlr)
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x                         */
        INSN2(mov,b     ,X1 MEM_DISP(esp,8),R(cl))  /* get shift count i             */
        INSN2(xor,l     ,R(edx),R(edx))             /* clear %edx                    */
        INSN2SHCL(shrd,l,R(eax),R(edx))             /* shift %edx right by i bits,
                                                       feeding in %eax from the left */
        INSN2(shr,l     ,R(cl),R(eax))              /* shift %eax right by i bits    */
        INSN2(mov,l     ,R(edx),C(hiremainder))     /* set hiremainder               */
	ret                                         /* return %eax                   */
FUNEND()

	ALIGN
FUNBEGIN(bfffo)
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x                         */
        INSN2(bsr,l     ,R(eax),R(edx))             /* %edx := number of leading bit */
        INSN2(mov,l     ,NUM(31),R(eax))
        INSN2(sub,l     ,R(edx),R(eax))             /* result is 31 - %edx           */
        ret                                         /* return %eax                   */
FUNEND()

	ALIGN
FUNBEGIN(mulll)
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x                */
        INSN1(mul,l     ,X4 MEM_DISP(esp,8))        /* %edx|%eax := x * y   */
        INSN2(mov,l     ,R(edx),C(hiremainder))     /* store high word      */
        ret                                         /* return low word %eax */
FUNEND()

	ALIGN
FUNBEGIN(addmul)
        INSN2(xor,l     ,R(ecx),R(ecx))             /* clear %ecx           */
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get x                */
        INSN1(mul,l     ,X4 MEM_DISP(esp,8))        /* %edx|%eax := x * y   */
        INSN2(add,l     ,C(hiremainder),R(eax))     /* add 0|hiremainder    */
        INSN2(adc,l     ,R(ecx),R(edx))
        INSN2(mov,l     ,R(edx),C(hiremainder))     /* store high word      */
        ret                                         /* return low word %eax */
FUNEND()

        ALIGN
FUNBEGIN(divll)
        INSN2(mov,l     ,X4 MEM_DISP(esp,4),R(eax)) /* get low word x        */
        INSN2(mov,l     ,C(hiremainder),R(edx))     /* get high word         */
        INSN1(div,l     ,X4 MEM_DISP(esp,8))        /* divide %edx|%eax by y */
        INSN2(mov,l     ,R(edx), C(hiremainder))    /* store remainder       */
        ret                                         /* return quotient %eax  */
FUNEND()

	ALIGN
