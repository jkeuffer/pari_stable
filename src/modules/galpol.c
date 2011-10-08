/* $Id$

Copyright (C) 2000-2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"

GEN
galoisnbpol(long a)
{
  GEN n;
  pariFILE *F;
  char *s = stackmalloc(strlen(pari_datadir) + 11 + 20 + 1);
  sprintf(s,"%s/galpol/%ld/nb", pari_datadir, a);
  F = pari_fopengz(s);
  if (!F) pari_err(e_MISC,"Missing galpol file %s\n",s);
  n = gp_read_stream(F->file);
  if (!n || typ(n)!=t_INT) pari_err(e_MISC,"Incompatible galpol file %s\n",s);
  pari_fclose(F); return n;
}

GEN
galoisgetpol(long a, long b, long sig)
{
  pariFILE *F;
  GEN V;
  const char *si;
  char *s;
  if (a<=0 || b<0) pari_err(e_MISC,"argument must be positive");
  if (!b) return galoisnbpol(a);
  switch(sig)
  {
    case 1: si="real"; break;
    case 2: if (a%2==0) { si="complex"; break; }
    default: /*FALL THROUGH*/
      pari_err(e_MISC,"invalid signature in galoisgetpol"); return NULL;
  }
  s = pari_sprintf("%s/galpol/%ld/%ld/%s", pari_datadir, a,b,si);
  F = pari_fopengz(s); free(s);
  if (!F)
  {
    long n = itos(galoisnbpol(a));
    if (b>n)
      pari_err(e_MISC,"Only %ld group%s of order %ld",n,n>2?"s":"",a);
    else pari_err(e_MISC,"Missing galpol file");
  }
  V = gp_read_stream(F->file);
  if (!V || typ(V)!=t_VEC ) pari_err(e_MISC,"Incompatible galpol file\n");
  pari_fclose(F); return V;
}

