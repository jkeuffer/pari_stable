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
/*        SOME GP FUNCTION THAT MAY BE USEFUL OUTSIDE OF IT        */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#ifdef macintosh
#  include "rect.h"
#  include "anal.h"
#else
#  include "../graph/rect.h"
#  include "../language/anal.h"
#endif

extern void kill0(entree *ep);

#ifdef HAS_DLOPEN
#include <dlfcn.h>

void 
install0(char *name, char *code, char *gpname, char *lib)
{
  void *f, *handle;

 /* dlopen(NULL) returns a handle to the running process. 
  * Bug report Y. Uchikawa: does not work for gp-dyn on FreeBSD 2.2.5
  */
#if defined(__FreeBSD__) || defined(__CYGWIN__)
  if (! *lib) lib = DL_DFLT_NAME;
#else
  if (! *lib) lib = NULL;
#endif
  if (! *gpname) gpname=name;
  if (lib) lib = expand_tilde(lib);

/* OSF1 has dlopen but not RTLD_GLOBAL*/
#ifndef RTLD_GLOBAL
#define RTLD_GLOBAL 0
#endif

  handle = dlopen(lib,RTLD_LAZY|RTLD_GLOBAL);

  if (!handle)
  {
    const char *s = dlerror(); if (s) fprintferr("%s\n\n",s);
    if (lib) err(talker,"couldn't open dynamic library '%s'",lib);
    err(talker,"couldn't open dynamic symbol table of process");
  }
  f = dlsym(handle,name);
  if (!f)
  {
    if (lib) err(talker,"can't find symbol '%s' in library '%s'",name,lib);
    err(talker,"can't find symbol '%s' in dynamic symbol table of process",name);
  }
  if (lib) free(lib);
  install(f,gpname,code);
}
#else
#  ifdef _WIN32
#  include <windows.h>
void 
install0(char *name, char *code, char *gpname, char *lib)
{
  FARPROC f;
  HMODULE handle;
#ifdef WINCE
  short wlib[256], wname[256];

  MultiByteToWideChar(CP_ACP, 0, lib, strlen(lib)+1, wlib, 256);
  MultiByteToWideChar(CP_ACP, 0, name, strlen(name)+1, wname, 256);
  lib = wlib;
  name = wname;
#endif

#ifdef DL_DFLT_NAME
  if (! *lib) lib = DL_DFLT_NAME;
#endif
  if (! *gpname) gpname=name;
  if (lib) lib = expand_tilde(lib);
  
  handle = LoadLibrary(lib);
  if (!handle)
  {
    if (lib) err(talker,"couldn't open dynamic library '%s'",lib);
    err(talker,"couldn't open dynamic symbol table of process");
  }
  f = GetProcAddress(handle,name);
  if (!f)
  {
    if (lib) err(talker,"can't find symbol '%s' in library '%s'",name,lib);
    err(talker,"can't find symbol '%s' in dynamic symbol table of process",name);
  }
  if (lib) free(lib);
  install((void*)f,gpname,code);
}
#  else
void 
install0(char *name, char *code, char *gpname, char *lib) { err(archer); }
#endif
#endif

void 
gpinstall(char *s, char *code, char *gpname, char *lib)
{
  if (GP_DATA->flags & SECURE)
  {
    fprintferr("[secure mode]: about to install '%s'. OK ? (^C if not)\n",s);
    hit_return();
  }
  install0(s, code, gpname, lib);
}

void
addhelp(entree *ep, char *s)
{
  if (ep->help && ! EpSTATIC(ep)) free(ep->help);
  ep->help = pari_strdup(s);
}

static long
get_type_num(char *st)
{
  if (isdigit((int)*st))
  {
    char *s = st;
    while (*s && isdigit((int)*s)) s++;
    if (*s) err(talker,"Unknown type: %s",s);
    return atol(st);
  }
  if (!strncmp(st,"t_",2)) st += 2; /* skip initial part */

  switch(strlen(st))
  {
    case 3:
      if (!strcmp(st,"INT")) return t_INT;
      if (!strcmp(st,"POL")) return t_POL;
      if (!strcmp(st,"SER")) return t_SER;
      if (!strcmp(st,"QFR")) return t_QFR;
      if (!strcmp(st,"QFI")) return t_QFI;
      if (!strcmp(st,"VEC")) return t_VEC;
      if (!strcmp(st,"COL")) return t_COL;
      if (!strcmp(st,"MAT")) return t_MAT;
      if (!strcmp(st,"STR")) return t_STR;
      break;

    case 4:
      if (!strcmp(st,"REAL")) return t_REAL;
      if (!strcmp(st,"FRAC")) return t_FRAC;
      if (!strcmp(st,"QUAD")) return t_QUAD;
      if (!strcmp(st,"LIST")) return t_LIST;
      break;

    case 5:
      if (!strcmp(st,"FRACN")) return t_FRACN;
      if (!strcmp(st,"PADIC")) return t_PADIC;
      if (!strcmp(st,"RFRAC")) return t_RFRAC;
      if (!strcmp(st,"SMALL")) return t_SMALL;
      break;

    case 6:
      if (!strcmp(st,"INTMOD")) return t_INTMOD;
      if (!strcmp(st,"POLMOD")) return t_POLMOD;
      if (!strcmp(st,"RFRACN")) return t_RFRACN;
      break;

    case 7:
      if (!strcmp(st,"COMPLEX")) return t_COMPLEX;
      break;

    case 8:
      if (!strcmp(st,"VECSMALL")) return t_VECSMALL;
      break;
  }
  err(talker,"Unknown type: t_%s",st);
  return 0; /* not reached */
}

GEN
type0(GEN x, char *st)
{
  long t, tx;
  if (! *st) 
  {
    char *s = type_name(typ(x));
    return STRtoGENstr(s);
  }
  tx = typ(x);
  t = get_type_num(st);

  if (is_frac_t(tx))
  {
    if (!is_frac_t(t) && !is_rfrac_t(t))
      err(typeer, "type");
    x = gcopy(x);
  }
  else if (is_rfrac_t(tx))
  {
    if (is_frac_t(t))
    {
      x = simplify(gred(x)); tx = typ(x);
      if (!is_frac_t(tx)) err(typeer, "type");
    }
    else
    {
      if (!is_rfrac_t(t)) err(typeer, "type");
      x = gcopy(x);
    }
  }
  else if (is_vec_t(tx))
  {
    if (!is_vec_t(t)) err(typeer, "type");
    x = gcopy(x);
  }
  else if (tx != t) err(typeer, "type");
  settyp(x, t); return x;
}

#include "highlvl.h"
