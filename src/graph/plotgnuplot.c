/*******************************************************************/
/*                                                                 */
/*                  HI-RES PLOT. GNUPLOT INTERFACE                 */
/*                                                                 */
/*                       copyright Babe Cool                       */
/*                       (C) Ilya Zakharevich                      */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
# include "pari.h"
#include "rect.h"
#define croak(str) err(talker,str)
#define SET_OPTIONS_FROM_STRING
#define GNUPLOT_OUTLINE_STDOUT
#define DONT_POLLUTE_INIT
#include "Gnuplot.h"

#ifdef __EMX__
#  define DEF_TERM "pm"
#else
#  define DEF_TERM (getenv("DISPLAY") ? "X11" : "dumb")
#endif

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free)
{
  long *ptx,*pty;
  long i,j,x0,y0;
  long good;
  int point_type = -1, line_type = 0;
  PariRect *e;
  RectObj *p1;

  (void)do_free;
  PARI_get_plot(0);

#if 0
  graphics();				/* Switch on terminal. */
#else
  term_start_plot();			/* Switch on terminal. */
#endif
  linetype(line_type);			/* X does not work otherwise. */
  setpointsize(pointsize);
  for(i=0;i<lw;i++)
  {
    e=rectgraph[w[i]]; p1=RHead(e); x0=x[i]; y0=y[i];
    while(p1)
    {
      switch(RoType(p1))
      {
	case ROt_PT:
	  point(RoPTx(p1)+x0, w_height - 1 - RoPTy(p1) - y0, point_type);
	  break;
	case ROt_LN:
	  move(RoLNx1(p1)+x0, w_height - 1 - RoLNy1(p1) - y0);
	  vector(RoLNx2(p1)+x0, w_height - 1 - RoLNy2(p1) - y0);
	  break;
	case ROt_BX:
	  move(RoBXx1(p1)+x0, w_height - 1 - RoBXy1(p1) - y0);
	  vector(RoBXx2(p1)+x0, w_height - 1 - RoBXy1(p1) - y0);
	  vector(RoBXx2(p1)+x0, w_height - 1 - RoBXy2(p1) - y0);
	  vector(RoBXx1(p1)+x0, w_height - 1 - RoBXy2(p1) - y0);
	  vector(RoBXx1(p1)+x0, w_height - 1 - RoBXy1(p1) - y0);
	  break;
	case ROt_MP:
	  ptx=RoMPxs(p1);
	  pty=RoMPys(p1);
	  for(j=0;j<RoMPcnt(p1);j++)
	  {
	    point(ptx[j]+x0,  w_height - 1 - pty[j] - y0, point_type);
	  }
	  break;
	case ROt_ML:
	  ptx=RoMLxs(p1);
	  pty=RoMLys(p1);
	  j = 0;
	  if (ptx[j]+x0 < 0 || ptx[j]+x0 >= w_width
	      || pty[j] + y0 < 0 || pty[j] + y0 >= w_height) {
	    good = 0;
	  } else {
	    move(ptx[j]+x0, w_height - 1 - pty[j] - y0);
	    good = 1;
	  }
	  for(j=1;j<RoMLcnt(p1);j++)
	  {
	    if (good) {
	      if (ptx[j]+x0 < 0 || ptx[j]+x0 >= w_width
		  || pty[j] + y0 < 0 || pty[j] + y0 >= w_height) {
		good = 0;
	      } else {
		vector(ptx[j]+x0, w_height - 1 - pty[j] - y0);
	      }
	    } else {
	      if (ptx[j]+x0 < 0 || ptx[j]+x0 >= w_width
		  || pty[j] + y0 < 0 || pty[j] + y0 >= w_height) {
	      } else {
		move(ptx[j]+x0, w_height - 1 - pty[j] - y0);
		good = 1;
	      }
	    }
	  }
	  break;
	case ROt_ST:
	  if (RoSTx(p1)+x0 < 0 || RoSTx(p1)+x0+RoSTl(p1)-1 >= w_width
	      || RoSTy(p1) + y0 < 0 || RoSTy(p1) + y0 >= w_height) {
	  } else {
	    put_text(RoSTx(p1)+x0,
		     w_height - 1 - RoSTy(p1) - y0 + (f_height - 1)/2,
		     RoSTs(p1));
	  }
	  break;
	case ROt_PTT:
	  point_type = RoPTTpen(p1);
	  break;
	case ROt_PTS:
	  pointsize = RoPTSsize(p1);
	  setpointsize(pointsize);
	  break;
	case ROt_LNT:
	  linetype(RoLNTpen(p1));
	  break;
	default: break;
      }
      p1=RoNext(p1);
    }
  }
#if 0
  text();				/* Reset terminal */
#else
  term_end_plot();			/* Reset terminal. */
#endif
}

void
PARI_get_plot(long fatal)
{
  (void)fatal;
  if (pari_plot.init) {
    return;
  }
  setup_gpshim();
  term_set( DEF_TERM );
}


long
term_set(char *s)
{
  char *t, *size = NULL;
  double x, y;

  setup_gpshim();
  if (*s == 0)
      s = pari_plot.name;
  t = s;
  if (t[1] == '\0' && t[0] == '?') {
     list_terms();
     return 1;
  }
  while (*t && !(*t == ' ' || *t == '\t' || *t == '\n' || *t == '='))
	t++;
  if ((t-s) > PLOT_NAME_LEN)
      err(talker,"too long name \"%s\"for terminal", s);
  if (*pari_plot.name
      && (strlen(pari_plot.name) != t - s	/* Why this? */
	  || (strncmp(pari_plot.name, s, t-s) != 0)) )
	reset();
  strncpy(pari_plot.name,s,t-s);
  pari_plot.name[t-s] = '\0';

  if (!termset( pari_plot.name ))
      err(talker,"error setting terminal \"%s\"", pari_plot.name);

  if (*t == '=') {
    size = ++t;
    x = atof(size);
    while (*t && !(*t == ' ' || *t == '\t' || *t == '\n' || *t == ','))
  	t++;
    if (*t != ',')
      err(talker, "Terminal size directive without ','");
    y = atof(++t);
    while (*t && !(*t == ' ' || *t == '\t' || *t == '\n'))
  	t++;
    plotsizes_scale(x*(1 + 1e-6)/termprop(xmax),
		    y*(1 + 1e-6)/termprop(ymax)); /* Later - truncated! */
  } else {
    plotsizes_scale(1,1);
  }

  /* *Needed*, say, by gif output: */
  set_options_from(t);

#if 0
  gptable_init();			/* Init terminal. */
#else
  term_init();
#endif

  setpointsize(pointsize);

  w_width = scaled_xmax();
  w_height = scaled_ymax();
  f_height = termprop(v_char);
  f_width = termprop(h_char);
  h_unit = termprop(h_tic);
  v_unit = termprop(v_tic);
  pari_plot.init = 1;

  return 1;
}

long
plot_outfile_set(char *s) { 
    int normal = (strcmp(s,"-") == 0);

    setup_gpshim();
    /* Delegate all the hard work to term_set_output() */

    if (normal) 
	term_set_output(NULL);
    else {				/* term_set_output() needs
					   a malloced string */
	char *s1 = (char*) malloc(strlen(s) + 1);

	strcpy(s1,s);
	term_set_output(s1);
    }
    return 1; 
}

void
set_pointsize(double d) 
{
    pointsize = d;
    if (pari_plot.init)
	setpointsize(d);
}
