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

#include "pari.h"

const char *errmessage[]=
{ "", /* force error into non-0 */

  "", /* syntaxer */
  "", /* bugparier */

  "", /* alarmer */
  "", /* openfiler */

  "", /* talker */
  "invalid flag", /* flagerr */
  "", /* impl */
  "sorry, not yet available on this system", /* archer */
  "not a function in function call", /* notfuncer */

  "precision too low", /* precer */
  "incorrect type", /* typeer */
  "inconsistent data", /* consister */
  "", /* user */

  "the PARI stack overflows !", /* errpile */
  "", /* overflower */

  /*  ALGLIN.C  */
  "non invertible matrix in gauss", /* matinv1 */
  "not a square matrix", /* mattype1 */

  /*  ARITH.C  */
  "not an integer argument in an arithmetic function", /* arither1 */
  "not enough precomputed primes", /* primer1 */
  "", /* invmoder*/

  /*  BASE.C  */
  "constant polynomial", /* constpoler */
  "not a polynomial", /* notpoler */
  "reducible polynomial", /* redpoler */
  "zero polynomial", /* zeropoler */

  /*  GEN.C */
  "", /* operi */
  "", /* operf */
  "division by zero", /* gdiver */

  /*  INIT.C  */
  "not enough memory", /* memer */

  /*  TRANS.C  */
  "negative exponent", /* negexper */
  "non quadratic residue in gsqrt", /* sqrter5 */

  "what's going on ?" /* noer */
};
