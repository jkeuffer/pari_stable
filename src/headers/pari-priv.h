/* $Id$

Copyright (C) 2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#define lswap(x,y) {long _z=x; x=y; y=_z;}
#define pswap(x,y) {GEN *_z=x; x=y; y=_z;}
#define swap(x,y)  {GEN  _z=x; x=y; y=_z;}
#define dswap(x,y) { double _t=x; x=y; y=_t; }
#define pdswap(x,y) { double* _t=x; x=y; y=_t; }
#define swapspec(x,y, nx,ny) {swap(x,y); lswap(nx,ny);}

GEN arith_proto(long f(GEN), GEN x, int do_error);
GEN arith_proto2(long f(GEN,GEN), GEN x, GEN n);
GEN arith_proto2gs(long f(GEN,long), GEN x, long y);
GEN garith_proto(GEN f(GEN), GEN x, int do_error);
GEN garith_proto2gs(GEN f(GEN,long), GEN x, long y);

#define both_odd(x,y) ((x)&(y)&1)

