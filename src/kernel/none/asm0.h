/* $Id$ */

/* This file defines the prototypes of "level 0" kernel functions    */
/* It is intended for use with an external "asm" definition          */

#define LOCAL_OVERFLOW
#define SAVE_OVERFLOW
#define LOCAL_HIREMAINDER
#define SAVE_HIREMAINDER

BEGINEXTERN
extern  ulong overflow;
extern  ulong hiremainder;
extern long addll(ulong x, ulong y);
extern long addllx(ulong x, ulong y);
extern long subll(ulong x, ulong y);
extern long subllx(ulong x, ulong y);
extern long shiftl(ulong x, ulong y);
extern long shiftlr(ulong x, ulong y);
extern long mulll(ulong x, ulong y);
extern long addmul(ulong x, ulong y);
extern long divll(ulong x, ulong y);
extern int  bfffo(ulong x);
ENDEXTERN
