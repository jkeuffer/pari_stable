/*************************************************************************/
/*                                                                       */
/*                 Declarations specifiques GP                           */
/*                                                                       */
/*************************************************************************/
/* $Id$ */

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
