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

/* This file defines the parameters of the GEN type               */

typedef long *GEN;
typedef int (*QSCOMP)(const void *, const void *);

#ifdef ULONG_NOT_DEFINED
  typedef unsigned long ulong;
#endif

#ifdef __M68K__
#  define OLD_CODES
#endif

#ifdef LONG_IS_64BIT
#  define TWOPOTBYTES_IN_LONG  3
#else
#  define TWOPOTBYTES_IN_LONG  2
#endif

#define DEFAULTPREC    2 + (8>>TWOPOTBYTES_IN_LONG)
#define MEDDEFAULTPREC 2 + (16>>TWOPOTBYTES_IN_LONG)
#define BIGDEFAULTPREC 2 + (24>>TWOPOTBYTES_IN_LONG)
#define TWOPOTBITS_IN_LONG (TWOPOTBYTES_IN_LONG+3)
#define BYTES_IN_LONG (1UL<<TWOPOTBYTES_IN_LONG)
#define BITS_IN_LONG  (1UL<<TWOPOTBITS_IN_LONG)
#define HIGHBIT (1UL << (BITS_IN_LONG-1))
#define BITS_IN_HALFULONG (BITS_IN_LONG>>1)
#define MAXULONG (~0x0UL)
#define MAXHALFULONG ((1UL<<BITS_IN_HALFULONG) - 1)
#define LOWMASK  (MAXHALFULONG)
#define HIGHMASK (~LOWMASK)
#define SMALL_MASK (HIGHBIT>>1)
/* You may want to change the following 32 to BITS_IN_LONG */
#define BITS_IN_RANDOM 32

/* Order of bits in codewords:
 *  x[0]         TYPBITS, CLONEBIT, LGBITS
 *  x[1].real    SIGNBITS, EXPOBITS
 *       int     SIGNBITS, LGEFINTBITS
 *       ser,pol SIGNBITS, VARNBITS ,LGEFBITS 
 *       padic   VALPBITS, PRECPBITS 
 * Length of bitfields are independant and satisfy:
 *  TYPnumBITS  + LGnumBITS   + 1 <= BITS_IN_LONG (optimally =)
 *  SIGNnumBITS + EXPOnumBITS     <= BITS_IN_LONG
 *  SIGNnumBITS + LGnumBITS       <= BITS_IN_LONG
 *  SIGNnumBITS + LGEFnumBITS + 2 <= BITS_IN_LONG
 *  VALPnumbits               + 1 <= BITS_IN_LONG */
#ifdef OLD_CODES
#  define TYPnumBITS   8 /* obsolete (for hard-coded assembler in mp.s) */
#  define SIGNnumBITS  8
#else
#  define TYPnumBITS   7
#  define SIGNnumBITS  2
#endif

#ifdef LONG_IS_64BIT
#  define   LGnumBITS 32
#  define EXPOnumBITS 48
#  define LGEFnumBITS 46 /* otherwise MAXVARN too large */
#  define VALPnumBITS 32
#else
# ifdef OLD_CODES
#   define  LGnumBITS 16 /* obsolete */
# else
#   define  LGnumBITS 24
# endif
#  define EXPOnumBITS 24
#  define LGEFnumBITS 16
#  define VALPnumBITS 16 
#endif

/* no user serviceable parts below :-) */
#define VARNnumBITS (BITS_IN_LONG - SIGNnumBITS - LGEFnumBITS)
#define PRECPSHIFT VALPnumBITS
#define  VARNSHIFT LGEFnumBITS
#define   TYPSHIFT (BITS_IN_LONG - TYPnumBITS)
#define  SIGNSHIFT (LGEFnumBITS+VARNnumBITS)

#define EXPOBITS    ((1UL<<EXPOnumBITS)-1)
#define SIGNBITS    (0xffffUL << SIGNSHIFT)
#define  TYPBITS    (0xffffUL <<  TYPSHIFT)
#define PRECPBITS   (~VALPBITS)
#define LGBITS      ((1UL<<LGnumBITS)-1)
#define LGEFINTBITS LGBITS
#define LGEFBITS    ((1UL<<LGEFnumBITS)-1)
#define VALPBITS    ((1UL<<VALPnumBITS)-1)
#define VARNBITS    (MAXVARN<<VARNSHIFT)
#define MAXVARN     ((1UL<<VARNnumBITS)-1)
#define HIGHEXPOBIT (1UL<<(EXPOnumBITS-1))
#define HIGHVALPBIT (1UL<<(VALPnumBITS-1))
#define CLONEBIT    (1UL<<LGnumBITS)

#define evaltyp(x)     (((ulong)(x)) << TYPSHIFT)
#define evalvarn(x)    (((ulong)(x)) << VARNSHIFT)
#define evalsigne(x)   (((long)(x)) << SIGNSHIFT)
#define evalprecp(x)   (((long)(x)) << PRECPSHIFT)
#define _evalexpo(x)  (HIGHEXPOBIT + (x))
#define _evalvalp(x)  (HIGHVALPBIT + (x))
#define evallgefint(x) (x)
#define _evallg(x)    (x)
#define _evallgef(x)  (x)

#define typ(x)        ((((ulong)(x))&1)? (long)t_SMALL: (long)(((ulong) ((GEN) (x))[0]) >> TYPSHIFT))
#define settyp(x,s)   (((GEN)(x))[0]=\
                        (((GEN)(x))[0]&(~TYPBITS)) | evaltyp(s))
#define smalltos(x)   (((long)(x))>>1)

#define isclone(x)    (((GEN) (x))[0] & CLONEBIT)
#define setisclone(x) (((GEN) (x))[0] |= CLONEBIT)
#define unsetisclone(x) (((GEN) (x))[0] &= (~CLONEBIT))

#define lg(x)         ((((ulong)(x))&1)?1L: ((long) (((GEN) (x))[0] & LGBITS)))
#define setlg(x,s)    (((GEN)(x))[0]=\
                        (((GEN)(x))[0]&(~LGBITS)) | evallg(s))

#define signe(x)      (((long) ((GEN) (x))[1]) >> SIGNSHIFT)
#define setsigne(x,s) (((GEN)(x))[1]=\
                        (((GEN)(x))[1]&(~SIGNBITS)) | evalsigne(s))

#define lgef(x)       (((GEN) (x))[1] & LGEFBITS)
#define setlgef(x,s)  (((GEN)(x))[1]=\
                        (((GEN)(x))[1]&(~LGEFBITS)) | evallgef(s))

#define lgefint(x)      (((GEN) (x))[1] & LGEFINTBITS)
#define setlgefint(x,s) (((GEN)(x))[1]=\
                          (((GEN)(x))[1]&(~LGEFINTBITS)) | evallgefint(s))

#define expo(x)       ((long) ((((GEN) (x))[1] & EXPOBITS) - HIGHEXPOBIT))
#define setexpo(x,s)  (((GEN)(x))[1]=\
		       (((GEN)(x))[1]&(~EXPOBITS)) | evalexpo(s))

#define valp(x)       ((long) ((((GEN)(x))[1] & VALPBITS) - HIGHVALPBIT))
#define setvalp(x,s)  (((GEN)(x))[1]=\
		       (((GEN)(x))[1]&(~VALPBITS)) | evalvalp(s))

#define precp(x)      ((long) (((ulong) ((GEN) (x))[1]) >> PRECPSHIFT))
#define setprecp(x,s) (((GEN)(x))[1]=\
		       (((GEN)(x))[1]&(~PRECPBITS)) | evalprecp(s))

#define varn(x)       ((((GEN) (x))[1]&VARNBITS) >> VARNSHIFT)
#define setvarn(x,s)  (((GEN)(x))[1]=\
		       (((GEN)(x))[1]&(~VARNBITS)) | evalvarn(s))

