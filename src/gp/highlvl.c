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
#include "paripriv.h"
#include "gp.h"
#include "../graph/rect.h"

#ifdef HAS_DLOPEN
#include <dlfcn.h>

void
install0(char *name, char *code, char *gpname, char *lib)
{
  void *f, *handle;

  if (! *lib) lib = DL_DFLT_NAME;
  if (! *gpname) gpname = name;
  if (lib) lib = path_expand(lib);

#ifndef RTLD_GLOBAL /* OSF1 has dlopen but not RTLD_GLOBAL*/
#  define RTLD_GLOBAL 0
#endif
  handle = dlopen(lib, RTLD_LAZY|RTLD_GLOBAL);

  if (!handle)
  {
    const char *s = dlerror(); if (s) err_printf("%s\n\n",s);
    if (lib) pari_err(e_MISC,"couldn't open dynamic library '%s'",lib);
    pari_err(e_MISC,"couldn't open dynamic symbol table of process");
  }
  f = dlsym(handle, name);
  if (!f)
  {
    if (lib) pari_err(e_MISC,"can't find symbol '%s' in library '%s'",name,lib);
    pari_err(e_MISC,"can't find symbol '%s' in dynamic symbol table of process",name);
  }
  if (lib) pari_free(lib);
  (void)install(f, gpname, code);
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
  if (lib) lib = path_expand(lib);

  handle = LoadLibrary(lib);
  if (!handle)
  {
    if (lib) pari_err(e_MISC,"couldn't open dynamic library '%s'",lib);
    pari_err(e_MISC,"couldn't open dynamic symbol table of process");
  }
  f = GetProcAddress(handle,name);
  if (!f)
  {
    if (lib) pari_err(e_MISC,"can't find symbol '%s' in library '%s'",name,lib);
    pari_err(e_MISC,"can't find symbol '%s' in dynamic symbol table of process",name);
  }
  if (lib) pari_free(lib);
  install((void*)f,gpname,code);
}
#  else
void
install0(char *name, char *code, char *gpname, char *lib)
{ pari_err(e_ARCH,"install"); }
#endif
#endif

void
gpinstall(char *s, char *code, char *gpname, char *lib)
{
  if (GP_DATA->secure)
  {
    char *msg = pari_sprintf("[secure mode]: about to install '%s'", s);
    pari_ask_confirm(msg);
    pari_free(msg);
  }
  install0(s, code, gpname, lib);
}

#include "highlvl.h"
