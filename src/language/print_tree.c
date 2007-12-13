
#ifndef __INTERNE__
#include "pari.h"
#include "paripriv.h"
#include "tree.h"
#endif

#define MYMIN(a,b) (((a)<(b))?(a):(b))

const char *CCs[] = {"CSTstr", "CSTquote", "CSTint", "CSTreal", "CSTmember", "CSTentry"};

static int indent = 0;
static const char *spaces = "                                                                      ";
/*
************************************************************************
                                                -- print_tree
************************************************************************
-- R.Butel   UMR 5251 IMB   C.N.R.S.  2007/12/04
-- Summary: print a (sub-)tree of the parse tree
-- Summary End
*/
void
print_tree(FILE *f_out, long root, int xml) /* Public, Recursive */
{
#undef mod_name
#define mod_name "print_tree"
  Ffunc f;
  long x, y;
  const char *str;
  int ii;
/*
------------------------------------------------------------------------
                                                -- print_tree.1
------------------------------------------------------------------------
*/
  for (ii = 0; ii < MYMIN(indent, strlen(spaces)); ii++) {
    fprintf(f_out, " ");
  };
  f = pari_tree[root].f;
  fprintf(f_out, "%ld:%s:", root, FFs[f]);

  str = pari_tree[root].str;
  if (str && *str) {
    fprintf(f_out, "`%.*s'", (int)pari_tree[root].len, str);
  };

/*
------------------------------------------------------------------------
                                                -- print_tree.2
------------------------------------------------------------ end of node
*/
  if (f == Fconst) {
    x = pari_tree[root].x;
    fprintf(f_out, "->%ld(%s)\n", x, CCs[x]);

  } else if (f == Fsmall) {
    x = pari_tree[root].x;
    fprintf(f_out, "->%ld\n", x);

  } else {
    x = pari_tree[root].x;
    y = pari_tree[root].y;

    if (x >= 0 && y >= 0) {
      fprintf(f_out, "[%ld,%ld]", x, y);
    } else if  (x >= 0) {
      fprintf(f_out, "[%ld]", x);
    };

    fprintf(f_out, "\n");
/*
------------------------------------------------------------------------
                                                -- print_tree.3
----------------------------------------------------------------- leaves
*/
    if (x == root) {
      fprintf(stderr, "recursion on x==root\n");
      abort();
    };

    if (y == root) {
      fprintf(stderr, "recursion on y==root\n");
      abort();
    };

    if (x >= 0) {
      indent += 2;
      print_tree(f_out, x, xml);
      if (y >= 0) {
        print_tree(f_out, y, xml);
      };
      indent -= 2;
    };

  };

} /* print_tree */

