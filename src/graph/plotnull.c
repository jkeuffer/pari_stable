/* $Id$ */
#include "pari.h"

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free) {}

long
term_set(char *s) {return 1;}

void
PARI_get_plot(long fatal) { err(talker,"high resolution graphics disabled"); }

long
plot_outfile_set(char *s) { return 1; }

void
set_pointsize(double d) {}
