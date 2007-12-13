/*
Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

BEGINEXTERN

typedef enum {Fseq,
              Fmatrix,FmatrixL,FmatrixR,
              Faffect,
              Ffacteurmat,
              Fmatrixelts,Fmatrixlines,
              Fmat,Fvec,Fnoarg,
              Flistarg,
              Frefarg,
              Fconst,Fsmall,
              Ftag,
              Fentry,Fcall,Ffunction,Fderfunc,Flambda
} Ffunc;

static THREAD const char *FFs[] = {
  "Fseq",               /* sequential chaining of two exprs */
  "Fmatrix",            /* creation of index for an element of a matrix or of a vector */
  "FmatrixL",           /* creation of index for a "left" of a matrix, taking columns */
  "FmatrixR",           /* creation of index for a "right" of a matrix, taking rows */
  "Faffect",            /* affectation or creation of a closure */
  "Ffacteurmat",        /* taking a part of a matrix */
  "Fmatrixelts",        /* catenation of exprs to create a line of a matrix */
  "Fmatrixlines",       /* catenation of lines to create a column of matrix */
  "Fmat",               /* creation of a matrix */
  "Fvec",               /* creation of a vector */
  "Fnoarg",             /* void node */
  "Flistarg",           /* catenation of arguments of a function */
  "Frefarg",            /* & lvalue : argument by reference */
  "Fconst",             /* constant : CST str, quote, int, real, member, entry */
  "Fsmall",             /* small integer constant */
  "Ftag",               /* typecast for gp2c */
  "Fentry",             /* identifier */
  "Fcall",              /* call of a closure function */
  "Ffunction",          /* declaration of a function */
  "Fderfunc",           /* declaration of a derivative */
  "Flambda"};           /* creation of a closure function */

#define Flastfunc  (Fdeffunc)
#define FneedENTRY (Fconst)

typedef struct node_s
{
  Ffunc f;           /*node function   */
  long x;            /*node left child */
  long y;            /*node right child*/
  const char *str;   /*text start      */
  size_t len;        /*text length     */
} node;

typedef enum {CSTstr, CSTquote, CSTint, CSTreal, CSTmember, CSTentry} CSTtype;

typedef enum {OPor, OPand, OPeq, OPne, OPge, OPg, OPle, OPl, OPs, OPp, OPsl, OPsr, OPmod, OPdr, OPeuc, OPd, OPm, OPpow, OPcat, OPstore, OPss, OPpp, OPse ,OPpe ,OPsle ,OPsre ,OPmode ,OPdre ,OPeuce ,OPde ,OPme, OPpl, OPn, OPnb, OPfact, OPderiv, OPtrans, OPhist, OPlength, OPnboperator} OPerator;

extern THREAD node *pari_tree;

ENDEXTERN
