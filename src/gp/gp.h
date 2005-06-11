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

void aide(char *s, int flag);
int  get_line_from_readline(char *prompt, char *prompt_cont, filtre_t *F);
void gp_output(GEN z, gp_data *G);
void hit_return(void);
void init80col(long n);
void pari_addfunctions(module **modlist_p, entree *func, char **help);
void recover(int flag);
int  term_height(void);
int  term_width(void);

/* aide() */
#define h_REGULAR 0
#define h_LONG    1
#define h_APROPOS 2
#define h_RL      4

/* prompts */
#define DFT_PROMPT "? "
#define BREAK_LOOP_PROMPT "break> "
#define COMMENTPROMPT "comment> "
#define CONTPROMPT ""
#define DFT_INPROMPT ""

/* readline completions */
typedef struct default_type {
  char *name;
  void *fun;
} default_type;

extern default_type gp_default_list[];
extern char *keyword_list[];
