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

/*************************************************************************/
/*                                                                       */
/*                      GP-SPECIFIC DECLARATIONS                         */
/*                                                                       */
/*************************************************************************/

void recover(int flag);
void pari_addfunctions(module **modlist_p, entree *func, char **help);
int term_height();
int term_width();
void hit_return();

extern ulong init_opts;
extern char *current_logfile;
extern jmp_buf environnement;

/* for do_time() */
enum { ti_NOPRINT, ti_REGULAR, ti_LAST, ti_INTERRUPT };

/* GP printing format */
typedef struct gp_format {
  char format; /* f, g or h */
  long field;  /* (0 = ignore) */
  long nb;     /* significant digits for reals (-1 = all) */
} gp_format;

/* default functions (i.e setd*) */
#define is_default(s) setdefault((s),"",d_EXISTS)==gun
enum { d_ACKNOWLEDGE, d_INITRC, d_SILENT, d_RETURN, d_EXISTS };

/* output format */
enum { f_RAW, f_PRETTYMAT, f_PRETTYOLD, f_PRETTY, f_TEX, NBFORMATS };

/* aide() */
#define h_REGULAR 0
#define h_LONG    1
#define h_APROPOS 2
#define h_RL      4
