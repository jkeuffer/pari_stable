/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

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

/* see try_name() */
static void *
try_dlopen(const char *s, int flag)
{ void *h = dlopen(s, flag); pari_free((void*)s); return h; }

/* like dlopen, but using default(sopath) */
static void *
gp_dlopen(const char *name, int flag)
{
  void *handle;
  char *s;

  if (!name) return dlopen(NULL, flag);
  s = path_expand(name);

  /* if sopath empty or path is absolute, use dlopen */
  if (!GP_DATA || *(GP_DATA->sopath->PATH)==0 || path_is_absolute(s))
    return try_dlopen(s, flag);
  else
  {
    forpath_t T;
    char *t;
    forpath_init(&T, GP_DATA->sopath, s);
    while ( (t = forpath_next(&T)) )
    {
      if ( (handle = try_dlopen(t,flag)) ) return handle;
      (void)dlerror(); /* clear error message */
    }
  }
  return NULL;
}

static void *
install0(const char *name, const char *lib)
{
  void *handle;

  if (! *lib) lib = DL_DFLT_NAME;

#ifndef RTLD_GLOBAL /* OSF1 has dlopen but not RTLD_GLOBAL*/
#  define RTLD_GLOBAL 0
#endif
  handle = gp_dlopen(lib, RTLD_LAZY|RTLD_GLOBAL);

  if (!handle)
  {
    const char *s = dlerror(); if (s) err_printf("%s\n\n",s);
    if (lib) pari_err(e_MISC,"couldn't open dynamic library '%s'",lib);
    pari_err(e_MISC,"couldn't open dynamic symbol table of process");
  }
  return dlsym(handle, name);
}
#else
#  ifdef _WIN32
#  include <windows.h>
static HMODULE
try_LoadLibrary(const char *s)
{ void *h = LoadLibrary(s); pari_free((void*)s); return h; }

/* like LoadLibrary, but using default(sopath) */
static HMODULE
gp_LoadLibrary(const char *name)
{
  HMODULE handle;
  char *s = path_expand(name);

  /* if sopath empty or path is absolute, use LoadLibrary */
  if (!GP_DATA || *(GP_DATA->sopath->PATH)==0 || path_is_absolute(s))
    return try_LoadLibrary(s);
  else
  {
    forpath_t T;
    char *t;
    forpath_init(&T, GP_DATA->sopath, s);
    while ( (t = forpath_next(&T)) )
      if ( (handle = try_LoadLibrary(t)) ) return handle;
  }
  return NULL;
}
static void *
install0(const char *name, const char *lib)
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

  handle = gp_LoadLibrary(lib);
  if (!handle)
  {
    if (lib) pari_err(e_MISC,"couldn't open dynamic library '%s'",lib);
    pari_err(e_MISC,"couldn't open dynamic symbol table of process");
  }
  return GetProcAddress(handle,name);
}
#  else
static void *
install0(const char *name, const char *lib)
{ pari_err(e_ARCH,"install"); return NULL; }
#endif
#endif

static char *
dft_help(const char *gp, const char *s, const char *code)
{ return stack_sprintf("%s: installed function\nlibrary name: %s\nprototype: %s" , gp, s, code); }

void
gpinstall(const char *s, const char *code, const char *gpname, const char *lib)
{
  pari_sp av = avma;
  const char *gp = *gpname? gpname: s;
  void *f;
  entree *ep;
  if (GP_DATA->secure)
  {
    char *msg = pari_sprintf("[secure mode]: about to install '%s'", s);
    pari_ask_confirm(msg);
    pari_free(msg);
  }
  ep = is_entry(gp);
  if (ep && ep->valence == EpINSTALL
      && strcmp(ep->code, code)
      && !strcmp(ep->help, dft_help(gp,s,ep->code)))
  { /* help is the default AND prototype changes: delete help */
    pari_free((void*)ep->help); ep->help = NULL;
  }
  f = install0(s, lib);
  if (!f)
  {
    if (*lib) pari_err(e_MISC,"can't find symbol '%s' in library '%s'",s,lib);
    pari_err(e_MISC,"can't find symbol '%s' in dynamic symbol table of process",s);
  }
  ep = install(f,gp,code);
  if (ep && !ep->help) addhelp(gp, dft_help(gp,s,code));
  avma = av;
}

#include "highlvl.h"
