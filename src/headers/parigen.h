/******************************************************************/
/* This file defines the parameters of the GEN type               */
/* $Id$ */

typedef long *GEN;
typedef int (*QSCOMP)(const void *, const void *);
#ifdef ULONG_NOT_DEFINED
  typedef unsigned long ulong;
#endif

#ifdef __M68K__
#  define OLD_CODES
#endif

#ifdef LONG_IS_64BIT
#  define MAXULONG     (0xffffffffffffffffUL)
#  define MAXHALFULONG (0x00000000ffffffffUL)
#  define HIGHBIT      (0x8000000000000000UL)
#  define HIGHMASK     (0xffffffff00000000UL)
#  define LOWMASK      (0x00000000ffffffffUL)
#  define SMALL_MASK   (0x4000000000000000UL)

#  define DEFAULTPREC     3
#  define MEDDEFAULTPREC  4
#  define BIGDEFAULTPREC  5
#  define TWOPOTBYTES_IN_LONG  3
#  define TWOPOTBITS_IN_LONG   6
#  define BYTES_IN_LONG        8
#  define BITS_IN_LONG        64
#  define BITS_IN_HALFULONG   32
/* For a 64-bit random generator, change the following 32 to 64 */
#  define BITS_IN_RANDOM      32

#else

#  define MAXULONG     (0xffffffffUL)
#  define MAXHALFULONG (0x0000ffffUL)
#  define HIGHBIT      (0x80000000UL)
#  define HIGHMASK     (0xffff0000UL)
#  define LOWMASK      (0x0000ffffUL)
#  define SMALL_MASK   (0x40000000UL)

#  define DEFAULTPREC     4
#  define MEDDEFAULTPREC  6
#  define BIGDEFAULTPREC  8
#  define TWOPOTBYTES_IN_LONG  2
#  define TWOPOTBITS_IN_LONG   5
#  define BYTES_IN_LONG        4
#  define BITS_IN_LONG        32
#  define BITS_IN_HALFULONG   16
#  define BITS_IN_RANDOM      32
#endif

#ifndef LONG_IS_64BIT
/*  second codeword x[1], for types: INT,REAL,PADIC,POL,SER */
#   define EXPOBITS    (0x00ffffffUL)
#   define HIGHEXPOBIT (0x00800000L)
#   define LGEFBITS    (0x0000ffffUL)
#   define VALPBITS    (0x0000ffffUL) /* used only for type PADIC */
#   define HIGHVALPBIT (0x00008000L)  /* used only for type PADIC, SER */
#   define PRECPBITS   (0xffff0000UL) /* used only for type PADIC */
#   define PRECPSHIFT  16
#   define VARNSHIFT   16

# ifndef OLD_CODES
#   define SIGNBITS    (0xc0000000UL)
#   define VARNBITS    (0x3fff0000UL)
#   define LGEFINTBITS (0x00ffffffUL)
#   define SIGNSHIFT   30
#   define MAXVARN     16383
# else
#   define SIGNBITS    (0xff000000UL)
#   define VARNBITS    (0x00ff0000UL)
#   define LGEFINTBITS (0x0000ffffUL)
#   define SIGNSHIFT   24
#   define MAXVARN     255
# endif

/*  first codeword x[0] */
# ifndef OLD_CODES
#   define TYPBITS      (0xfe000000UL)
#   define CLONEBIT     (0x01000000UL)
#   define LGBITS       (0x00ffffffUL)
#   define TYPSHIFT     25
# else
#   define TYPBITS      (0xff000000UL)
#   define CLONEBIT     (0x00010000UL)
#   define LGBITS       (0x0000ffffUL)
#   define TYPSHIFT     24
# endif
#endif

#ifdef LONG_IS_64BIT
/*  first codeword x[0] */
#  define TYPBITS      (0xffff000000000000UL)
#  define CLONEBIT     (0x0000000100000000UL)
#  define LGBITS       (0x00000000ffffffffUL)
#  define TYPSHIFT     48

/*  second codeword x[1] */
#  define SIGNBITS     (0xffff000000000000UL)
#  define VARNBITS     (0x0000ffff00000000UL)
#  define LGEFBITS     (0x00000000ffffffffUL)
#  define SIGNSHIFT    48
#  define MAXVARN      65535

#  define EXPOBITS     (0x0000ffffffffffffUL)
#  define HIGHEXPOBIT  (0x0000800000000000L)
#  define LGEFINTBITS  (0x00000000ffffffffUL)
#  define VALPBITS     (0x00000000ffffffffUL)
#  define HIGHVALPBIT  (0x0000000080000000L)
#  define PRECPBITS    (0xffffffff00000000UL)
#  define PRECPSHIFT   32
#  define VARNSHIFT    32
#endif

#define evaltyp(x)     (((ulong)(x)) << TYPSHIFT)
#define evalvarn(x)    (((ulong)(x)) << VARNSHIFT)
#define evalsigne(x)   (((long)(x)) << SIGNSHIFT)
#define evalprecp(x)   (((long)(x)) << PRECPSHIFT)
#define evalexpo(x)    (HIGHEXPOBIT + (x))
#define evalvalp(x)    (HIGHVALPBIT + (x))
#define evallgefint(x) (x)
#define m_evallg(x)    (x)
#define m_evallgef(x)  (x)

#define typ(x)        ((((long)(x))&1)? t_SMALL: (((ulong) ((GEN) (x))[0]) >> TYPSHIFT))
#define settyp(x,s)   (((GEN)(x))[0]=\
                        (((GEN)(x))[0]&(~TYPBITS)) | evaltyp(s))
#define smalltos(x)   (((long)(x))>>1)

#define isclone(x)    (((GEN) (x))[0] & CLONEBIT)
#define setisclone(x) (((GEN) (x))[0] |= CLONEBIT)
#define unsetisclone(x) (((GEN) (x))[0] &= (~CLONEBIT))

#define lg(x)         ((((long)(x))&1)?1: ((long) (((GEN) (x))[0] & LGBITS)))
#define setlg(x,s)    (((GEN)(x))[0]=\
                        (((GEN)(x))[0]&(~LGBITS)) | evallg(s))

#define signe(x)      (((long) ((GEN) (x))[1]) >> SIGNSHIFT)
#define setsigne(x,s) (((GEN)(x))[1]=\
                        (((GEN)(x))[1]&(~SIGNBITS)) | evalsigne(s))

#define lgef(x)       ((long) (((GEN) (x))[1] & LGEFBITS))
#define setlgef(x,s)  (((GEN)(x))[1]=\
                        (((GEN)(x))[1]&(~LGEFBITS)) | evallgef(s))

#define lgefint(x)      ((long) (((GEN) (x))[1] & LGEFINTBITS))
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

#define varn(x)       ((long) ((((GEN) (x))[1]&VARNBITS) >> VARNSHIFT))
#define setvarn(x,s)  (((GEN)(x))[1]=\
		       (((GEN)(x))[1]&(~VARNBITS)) | evalvarn(s))

