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

typedef enum {Gvoid, Gsmall, Gvec, Gvar, Ggen} Gtype;

typedef enum {OCpushlong='A',OCpushgen,OCpushreal,OCpushstoi,
              OCpushvalue,OCpushvar,
              OCpop,
              OCstoi,OCitos,OCtostr,OCvarn,OCcopy,
              OCprecreal,OCprecdl,
              OCvec,OCmat,OCcol,
              OCstackgen,OCstore,
              OCcompo1,OCcompo2,OCcompoC,OCcompoL,
              OCnewptr,OCpushptr,OCendptr,
              OCcompo1ptr,OCcompo2ptr,OCcompoCptr,OCcompoLptr,
              OCcalllong,OCcallgen,OCcallgen2,OCcallint,OCcallvoid,OCcalluser,
              OCderivgen,OCderivuser,
              OCdeffunc,OCgetarg,OCdefaultarg,
              OCglobalvar} op_code;

ENDEXTERN
