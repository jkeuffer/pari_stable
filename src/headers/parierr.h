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

enum {
/* Force errors into non-0 */
  talker2 = 1, bugparier, /* untrappable errors */

  alarmer, openfiler,

  talker, flagerr, impl, archer, notfuncer,

  precer, typeer, consister, user,

  errpile, overflower,

/* alglin.c */
  matinv1, mattype1,

/* arith.c  */
  arither1, primer1, invmoder,

/* base.c   */
  constpoler, notpoler, redpoler, zeropoler,

/* gen.c */
  operi, operf, gdiver,

/* init.c */
  memer,

/* trans.c */
  negexper, sqrter5,

/* NO ERROR */
  noer
};

enum { warner, warnprec, warnfile, warnmem };
