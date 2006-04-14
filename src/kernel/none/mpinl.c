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
#define DISABLE_INLINE
#include "pari.h"
ulong hiremainder, overflow;
#undef INLINE
#define INLINE
BEGINEXTERN
#include "parilvl0.h"
#include "parilvl1.h"
#ifdef addll
#  undef addll
#  undef addllx
#  undef subll
#  undef subllx
#  include "../src/kernel/none/addll.h"
#endif
#ifdef mulll
#  undef mulll
#  undef addmul
#  include "../src/kernel/none/mulll.h"
#endif
#ifdef divll
#  undef divll
#  include "../src/kernel/none/divll.h"
#endif
#ifdef bfffo
#  undef bfffo
#  include "../src/kernel/none/bfffo.h"
#endif
ENDEXTERN
