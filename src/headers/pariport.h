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

/*******************************************************************/
/*                                                                 */
/*           DECLARATIONS SPECIFIC TO THE PORTABLE VERSION         */
/*                                                                 */
/*******************************************************************/

/* mp.c */

#define affrs(x,s)     (err(affer4))
#define affri(x,y)     (err(affer5))
#define cmpis(x,y)     (-cmpsi((y),(x)))
#define cmprs(x,y)     (-cmpsr((y),(x)))
#define cmpri(x,y)     (-cmpir((y),(x)))
#define subis(x,y)     (addsi(-(y),(x)))
#define subrs(x,y)     (addsr(-(y),(x)))

#define divii(a,b)     (dvmdii((a),(b),NULL))
#define resii(a,b)     (dvmdii((a),(b),ONLY_REM))

#define mpshift(x,s)   ((typ(x)==t_INT)?shifti((x),(s)):shiftr((x),(s)))
#define affsz(s,x)     ((typ(x)==t_INT)?affsi((s),(x)):affsr((s),(x)))
#define mptruncz(x,y)  (gop1z(mptrunc,(x),(y)))
#define mpentz(x,y)    (gop1z(mpent,(x),(y)))
#define mpaddz(x,y,z)  (gop2z(mpadd,(x),(y),(z)))
#define addsiz(s,y,z)  (gops2sgz(addsi,(s),(y),(z)))
#define addsrz(s,y,z)  (gops2sgz(addsr,(s),(y),(z)))
#define addiiz(x,y,z)  (gop2z(addii,(x),(y),(z)))
#define addirz(x,y,z)  (gop2z(addir,(x),(y),(z)))
#define addriz(x,y,z)  (gop2z(addir,(y),(x),(z)))
#define addrrz(x,y,z)  (gop2z(addrr,(x),(y),(z)))
#define mpsubz(x,y,z)  (gop2z(mpsub,(x),(y),(z)))
#define subss(x,y)     (addss(-(y),(x)))
#define subssz(x,y,z)  (addssz((x),-(y),(z)))
#define subsiz(s,y,z)  (gops2sgz(subsi,(s),(y),(z)))
#define subsrz(x,y,z)  {gpmem_t av=avma; gaffect(subsr((x),(y)),(z)); avma=av; }
#define subisz(y,s,z)  (gops2sgz(addsi,-(s),(y),(z)))
#define subrsz(y,s,z)  (gops2sgz(addsr,-(s),(y),(z)))
#define subiiz(x,y,z)  {gpmem_t av=avma; gaffect(subii((x),(y)),(z)); avma=av; }
#define subirz(x,y,z)  {gpmem_t av=avma; gaffect(subir((x),(y)),(z)); avma=av; }
#define subriz(x,y,z)  (gop2z(subri,(x),(y),(z)))
#define subrrz(x,y,z)  {gpmem_t av=avma; gaffect(subrr((x),(y)),(z)); avma=av; }
#define mpmulz(x,y,z)  (gop2z(mpmul,(x),(y),(z)))
#define mulsiz(s,y,z)  (gops2sgz(mulsi,(s),(y),(z)))
#define mulsrz(s,y,z)  (gops2sgz(mulsr,(s),(y),)(z))
#define muliiz(x,y,z)  (gop2z(mulii,(x),(y),(z)))
#define mulirz(x,y,z)  (gop2z(mulir,(x),(y),(z)))
#define mulriz(x,y,z)  (gop2z(mulir,(y),(x),(z)))
#define mulrrz(x,y,z)  (gop2z(mulrr,(x),(y),(z)))
#define mpinvsr(s,y)   (divssz(1,(s),(y)))
#define mpinvir(x,y)   (divsiz(1,(x),(y)))
#define mpinvrr(x,y)   (divsrz(1,(x),(y)))
#define mpdvmdz(x,y,z,t) (dvmdiiz((x),(y),(z),(t)))
#define modssz(s,y,z)  (gops2ssz(modss,(s),(y),(z)))
#define modsiz(s,y,z)  (gops2sgz(modsi,(s),(y),(z)))
#define modisz(y,s,z)  (gops2gsz(modis,(y),(s),(z)))
#define ressiz(s,y,z)  (gops2sgz(ressi,(s),(y),(z)))
#define resisz(y,s,z)  (gops2gsz(resis,(y),(s),(z)))
#define resssz(s,y,z)  (gops2ssz(resss,(s),(y),(z)))
#define divirz(x,y,z)  (gop2z(divir,(x),(y),(z)))
#define divriz(x,y,z)  (gop2z(divri,(x),(y),(z)))
#define divsrz(s,y,z)  (gops2sgz(divsr,(s),(y),(z)))
#define divrsz(y,s,z)  (gops2gsz(divrs,(y),(s),(z)))
