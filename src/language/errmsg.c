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

char *errmessage[]=
{
/* no_error */
  "bug in error-handling code",

/* cant_deflate */
  "can't deflate",

/* Always catched up to this point */

/* caracer1 */
  "unexpected character",
/* paramer1 */
  "unknown function or error in formal parameters",
/* varer1 */
  "variable name expected",
/* obsoler */
  "obsolete function",
/* openfiler */
  "error opening ",
/* talker2 */
  "",

/* NO CONTEXT NOW */

/* talker */
  "",
/* flagerr */
  "invalid flag",
/* warner */
  "Warning:",
/* warnprec */
  "Warning: increasing prec",
/* warnfile */
  "Warning: failed to",
/* accurer */
  "accuracy problems",
/* bugparier */
  "bug in",
/* impl */
  "sorry,",
/* archer */
  "sorry, not yet available on this system",
/* warnmem */
  "collecting garbage in",
/* precer */
  "precision too low",

/* siginter */
  "",
/* typeer */
  "incorrect type",
/* consister */
  "inconsistent data",
/* user */
  "",

    /*  MP.S  */

/* affer2 */
  "impossible assignment I-->S",
/* affer3 */
  "impossible assignment I-->I",

/* errpile */
  "the PARI stack overflows !",
/* errlg */
  "object too big, length can't fit in a codeword",
/* errexpo */
  "exponent overflow",
/* errvalp */
  "valuation overflow",
/* rtodber */
  "underflow or overflow in a R->dbl conversion",

  /*  ALGLIN.C  */

/* matinv1 */
  "non invertible matrix in gauss",
/* mattype1 */
  "not a square matrix",

  /*  ANAL.C  */

/* valencer1 */
  "unknown identifier valence, please report",
/* breaker */
  "break not allowed",

  /*  ARITH.C  */

/* arither1 */
  "not an integer argument in an arithmetic function",
/* arither2 */
  "non-positive argument (<= 0) in an arithmetic function",
/* arither3 */
  "zero argument in an arithmetic function",
/* funder2 */
  "discriminant not congruent to 0 or 1 mod 4",
/* generer */
  "primitive root does not exist in gener",
/* primer1 */
  "not enough precomputed primes",
/* primer2 */
  "not enough precomputed primes, need primelimit ~ ",
/* invmoder*/
  "impossible inverse modulo: ",
  /*  BASE.C  */

/* constpoler */
  "constant polynomial",
/* notpoler */
  "not a polynomial",
/* redpoler */
  "reducible polynomial",
/* zeropoler */
  "zero polynomial",
/* idealer1 */
  "not a number field in some number field-related function",
/* idealer2 */
  "not an ideal in an ideal-related function",

  /*  BIBLI.C  */

/* intger2 */
  "too many iterations for desired precision in integration routine",
/* lllger3 */
  "not a definite matrix in lllgram",

  /*  ELLIPTIC.C  */

/* elliper1 */
  "bad argument for an elliptic curve related function",

  /*  GEN.C */

/* operi */
  "impossible",
/* operf */
  "forbidden",
/* gdiver */
  "division by zero",
/* inter2 */
  "a log/atan appears in the integration, PARI cannot handle that",
/* overwriter */
  "trying to overwrite a universal object",

  /*  INIT.C  */

/* memer */
  "not enough memory",
/* gerper */
  "significant pointers are lost in gerepile !!! (please report)",

  /*  TRANS.C  */

/* infprecer */
  "infinite precision",
/* negexper */
  "negative exponent",
/* sqrter5 */
  "non quadratic residue in gsqrt",

/* noer */
  "what's going on ?"
};
