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
/* caseer */
  "this should be an integer",
/* caseer2 */
  "incorrect type or length in matrix assignment",
/* member */
  "incorrect type in .",
/* nparamer1 */
  "too many parameters in user-defined function call",
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

/* affer1 */
  "impossible assignment S-->I",
/* affer2 */
  "impossible assignment I-->S",
/* affer3 */
  "impossible assignment I-->I",
/* affer4 */
  "impossible assignment R-->S",
/* affer5 */
  "impossible assignment R-->I",
/* shier1 */
  "overflow in integer shift",
/* shier2 */
  "overflow in real shift",
/* truer1 */
  "overflow in truncation",

/* adder1 */
  "overflow in S+I",
/* adder2 */
  "overflow in I+I",
/* adder3 */
  "overflow in I+R",
/* adder4 */
  "overflow in R+R",
/* adder5 */
  "underflow in R+R",
/* muler1 */
  "overflow in I*I",
/* muler2 */
  "overflow in S*R",
/* muler3 */
  "overflow in S*I",
/* muler4 */
  "overflow in R*R",

/* muler5 */
  "underflow in R*R",
/* muler6 */
  "overflow in I*R (R=0)",
/* diver1 */
  "division by zero in S/S",
/* diver2 */
  "division by zero in S/I",
/* diver3 */
  "division by zero in S/R",
/* diver4 */
  "division by zero in I/S",
/* diver5 */
  "division by zero in I/R",
/* diver6 */
  "division by zero in R/S",
/* diver7 */
  "underflow in R/S",
/* diver8 */
  "division by zero in R/I",

/* diver9 */
  "division by zero in R/R",
/* diver10 */
  "underflow in R/R",
/* diver11 */
  "overflow in R/R",
/* diver12 */
  "underflow in R/I (R=0)",
/* divzer1 */
  "forbidden division R/R-->I or I/R-->I or R/I-->I",
/* dvmer1 */
  "division by zero in dvmdii",
/* moder1 */
  "zero modulus in modss",
/* reser1 */
  "division by zero in resss",
/* arier1 */
  "forbidden type in an arithmetic function",
/* arier2 */
  "third operand of type real",

/* errpile */
  "the PARI stack overflows !",
/* errlg */
  "object too big, length can't fit in a codeword",
/* errlgef */
  "degree overflow",
/* errexpo */
  "exponent overflow",
/* errvalp */
  "valuation overflow",
/* rtodber */
  "underflow or overflow in a R->dbl conversion",

  /*  ALGLIN.C  */

/* concater */
  "impossible concatenation in concat",
/* matinv1 */
  "non invertible matrix in gauss",
/* mattype1 */
  "not a square matrix",
/* suppler2 */
  "not linearly independent columns in suppl",

  /*  ANAL.C  */

/* valencer1 */
  "unknown identifier valence, please report",
/* breaker */
  "break not allowed",

  /*  ARITH.C  */

/* arither1 */
  "not an integer argument in an arithmetic function",
/* arither2 */
  "negative or zero argument in an arithmetic function",
/* facter */
  "negative argument in factorial function",
/* hiler1 */
  "insufficient precision for p=2 in hilbert",
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

/* polrationer */
  "not a rational polynomial",
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

/* changer1 */
  "incorrect second argument in changevar",
/* intger2 */
  "too many iterations for desired precision in integration routine",
/* lllger3 */
  "not a definite matrix in lllgram",
/* lllger4 */
  "not an integral matrix in lllgramint",

  /*  ELLIPTIC.C  */

/* elliper1 */
  "bad argument for an elliptic curve related function",
/* heller1 */
  "point not on elliptic curve",

  /*  GEN.C */

/* operi */
  "impossible",
/* operf */
  "forbidden",
/* gdiver */
  "division by zero in gdiv, gdivgs or ginv",
/* inter2 */
  "a log/atan appears in the integration, PARI cannot handle that",
/* overwriter */
  "trying to overwrite a universal object",

  /*  INIT.C  */

/* memer */
  "not enough memory",
/* gerper */
  "significant pointers are lost in gerepile !!! (please report)",

  /*  PLOT.C  */

/* ploter4 */
  "not vectors in plothraw",
/* ploter5 */
  "vectors not of the same length in plothraw",

  /*  POLARIT.C */

/* rootper1 */
  "incorrect type(s) or zero polynomial in rootpadic or factorpadic",
/* rootper2 */
  "root does not exist in rootpadic",
/* rootper4 */
  "nonpositive precision in rootpadic",

  /*  TRANS.C  */

/* infprecer */
  "infinite precision",
/* negexper */
  "negative exponent",
/* sqrter5 */
  "non quadratic residue in gsqrt",
/* sqrter6 */
  "odd exponent in gsqrt",
/* gamer2 */
  "negative or zero integer argument in mpgamma",
/* thetaer1 */
  "q>=1 in theta",

/* noer */
  "what's going on ?"
};
