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
#include "paripriv.h"
#include "../language/anal.h"
#include "gp.h"

typedef struct whatnow_t
{
  const char *name, *oldarg, *newarg;
} whatnow_t;

#define SAME NULL
#define REMOV (char *)1L
#define _REMOV {REMOV,NULL,NULL}
#define _SAME  {SAME,NULL,NULL}

#include "whatnow.h"

static int
is_identifier(const char *s)
{
  while (*s && is_keyword_char(*s)) s++;
  return *s? 0: 1;
}


static void
msg(const char *s)
{
  term_color(c_HELP);
  print_text(s); pari_putc('\n');
  term_color(c_NONE);
}
/* If flag = 0 (default): check if s existed in 1.39.15 and print verbosely
 * the answer.
 * If flag > 0: silently return n+1 if function changed, 0 otherwise.
 *   (where n is the index of s in whatnowlist).
 * If flag < 0: -flag-1 is the index in whatnowlist */
int
whatnow(const char *s, int flag)
{
  int n;
  const char *def;
  whatnow_t wp;
  entree *ep;

  if (flag < 0) { n = -flag; flag = 0; }
  else
  {
    if (flag && s[0] && !s[1]) return 0; /* special case "i" and "o" */
    if (!is_identifier(s) || !is_entry_intern(s,funct_old_hash,NULL))
    {
      if (!flag) msg("As far as I can recall, this function never existed");
      return 0;
    }
    n = 0;
    do
      def = (oldfonctions[n++]).name;
    while (def && strcmp(def,s));
    if (!def)
    {
      int m = 0;
      do
	def = (functions_oldgp[m++]).name;
      while (def && strcmp(def,s));
      n += m - 1;
    }
  }

  wp = whatnowlist[n-1]; def = wp.name;
  if (def == SAME)
  {
    if (!flag) msg("This function did not change");
    return 0;
  }
  if (flag) return n;

  if (def == REMOV)
  {
    msg("This function was suppressed");
    return 0;
  }
  if (!strcmp(def,"x*y")) ep = NULL;
  else {
    ep = is_entry(wp.name);
    if (!ep) pari_err(bugparier,"whatnow");
  }
  pari_puts("New syntax: "); term_color(c_ERR);
  pari_printf("%s%s ===> %s%s\n\n", s, wp.oldarg, wp.name, wp.newarg);
  if (ep) msg(ep->help);
  term_color(c_NONE); return 1;
}
