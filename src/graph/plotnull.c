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

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free)
{
  (void)w;
  (void)x;
  (void)y;
  (void)lw;
  (void)do_free;
}

long
term_set(char *s) { (void)s; return 1; }

void
PARI_get_plot(long f)
{
  (void)f;
  err(talker,"high resolution graphics disabled");
}

long
plot_outfile_set(char *s) { (void)s; return 1; }

void
set_pointsize(double d) { (void)d; }
