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

/*******************************************************************/
/*                                                                 */
/*                  HI-RES PLOT. GNUPLOT INTERFACE                 */
/*                   written by Ilya Zakharevich                   */
/*                                                                 */
/*******************************************************************/
# include "pari.h"
#include "rect.h"
#define croak(str) err(talker,str)
#define SET_OPTIONS_FROM_STRING
#define GNUPLOT_OUTLINE_STDOUT
#define DONT_POLLUTE_INIT

/* The gnuplot library may reference a function with *this* name */
#define mys_mouse_feedback_rectangle set_mouse_feedback_rectangle
#include "Gnuplot.h"

#ifdef __EMX__
#  define DEF_TERM "pm"
#else
#  define DEF_TERM (getenv("DISPLAY") ? "X11" : "dumb")
#endif

#ifdef BOTH_GNUPLOT_AND_X11
#  ifdef GNUPLOT_AND_X11_PREFER_GNUPLOT
#    define DEFAULT_IS_BUILTIN 0
#  else	/* !( defined GNUPLOT_AND_X11_PREFER_GNUPLOT ) */ 
#    define DEFAULT_IS_BUILTIN 1
#  endif	/* defined GNUPLOT_AND_X11_PREFER_GNUPLOT */ 
#endif
#ifndef BOTH_GNUPLOT_AND_X11             /* The switch support in plotgnuplot */
#  define X11_rectdraw0             rectdraw0
#  define X11_term_set              term_set
#  define X11_PARI_get_plot         PARI_get_plot
#  define X11_set_pointsize         set_pointsize
#endif

#  ifdef BOTH_GNUPLOT_AND_X11
int is_builtin = DEFAULT_IS_BUILTIN;
int X11_init;
static void my_rectdraw0(long *w, long *x, long *y, long lw, long do_free);
#  endif

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free)
#  ifdef BOTH_GNUPLOT_AND_X11
{
    if (is_builtin) {
	X11_rectdraw0(w, x, y, lw, do_free);
	return;
    }
    
    my_rectdraw0(w, x, y, lw, do_free);
    return;
}

static void
my_rectdraw0(long *w, long *x, long *y, long lw, long do_free)
#  endif	/* defined BOTH_GNUPLOT_AND_X11 */
{
  double *ptx,*pty;
  long i,j,x0,y0, hjust, vjust, hgap, vgap, hgapsize, vgapsize;
  long good, seen_graph = 0;
  int point_type = -1, line_type = 0;
  PariRect *e;
  RectObj *p1;
  int strdir = RoSTdirLEFT, can_justify = 1, shift = 0, xstart, xend;

  (void)do_free;
  PARI_get_plot(0);

  hgapsize = h_unit;  vgapsize = v_unit;
  if (hgapsize == 1)
    hgapsize = 2;	/* Vertical direction is subjectively different! */
  /* Find the info about the *actual* x and y-coords of the
     rectangles.  Use the first rectangle with has_graph attribute. */

  for(i=0;i<lw;i++) {
      e=rectgraph[w[i]];
      if (RHasGraph(e)) {
	  set_mouse_feedback_rectangle(
		x[i], x[i] + RXsize(e) - 1,
		w_height - 1 - y[i] - (RYsize(e) - 1), w_height - 1 - y[i],
		(0 - RXshift(e))/RXscale(e),
		(RXsize(e) - 1 - RXshift(e))/RXscale(e),
		(RYsize(e) - 1 - RYshift(e))/RYscale(e),
		(0 - RYshift(e))/RYscale(e)
	  );
	  seen_graph = 1;
	  break;
      }
  }
  if (!seen_graph)			/* Put some reasonable values */
	  set_mouse_feedback_rectangle(	0, w_width - 1,	0, w_height - 1,
					0, 0, 0, 0);

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
	  point(DTOL(RoPTx(p1)+x0), w_height - 1 - DTOL(RoPTy(p1) + y0),
		point_type);
	  break;
	case ROt_LN:
	  move(DTOL(RoLNx1(p1)+x0), w_height - 1 - DTOL(RoLNy1(p1) + y0));
	  vector(DTOL(RoLNx2(p1)+x0), w_height - 1 - DTOL(RoLNy2(p1) + y0));
	  break;
	case ROt_BX:
	  move(DTOL(RoBXx1(p1)+x0), w_height - 1 - DTOL(RoBXy1(p1) + y0));
	  vector(DTOL(RoBXx2(p1)+x0), w_height - 1 - DTOL(RoBXy1(p1) + y0));
	  vector(DTOL(RoBXx2(p1)+x0), w_height - 1 - DTOL(RoBXy2(p1) + y0));
	  vector(DTOL(RoBXx1(p1)+x0), w_height - 1 - DTOL(RoBXy2(p1) + y0));
	  vector(DTOL(RoBXx1(p1)+x0), w_height - 1 - DTOL(RoBXy1(p1) + y0));
	  break;
	case ROt_MP:
	  ptx=RoMPxs(p1);
	  pty=RoMPys(p1);
	  for(j=0;j<RoMPcnt(p1);j++)
	  {
	    point(DTOL(ptx[j] + x0),  w_height - 1 - DTOL(pty[j] + y0),
		  point_type);
	  }
	  break;
	case ROt_ML:
	  ptx=RoMLxs(p1);
	  pty=RoMLys(p1);
	  j = 0;
	  if (DTOL(ptx[j]+x0) < 0 || DTOL(ptx[j]+x0) >= w_width
	      || DTOL(pty[j] + y0) < 0 || DTOL(pty[j] + y0) >= w_height) {
	    good = 0;
	  } else {
	    move(DTOL(ptx[j]+x0), w_height - 1 - DTOL(pty[j] + y0));
	    good = 1;
	  }
	  for(j=1;j<RoMLcnt(p1);j++)
	  {
	    if (good) {
	      if (DTOL(ptx[j] + x0) < 0 || DTOL(ptx[j]+x0) >= w_width
		  || DTOL(pty[j] + y0) < 0 || DTOL(pty[j] + y0) >= w_height) {
		good = 0;
	      } else {
		vector(DTOL(ptx[j] + x0), w_height - 1 - DTOL(pty[j] + y0));
	      }
	    } else {
	      if (DTOL(ptx[j] + x0) < 0 || DTOL(ptx[j] + x0) >= w_width
		  || DTOL(pty[j] + y0) < 0 || DTOL(pty[j] + y0) >= w_height) {
	      } else {
		move(DTOL(ptx[j]+x0), w_height - 1 - DTOL(pty[j] + y0));
		good = 1;
	      }
	    }
	  }
	  break;
	case ROt_ST:
	  hjust = RoSTdir(p1) & RoSTdirHPOS_mask;
	  vjust = RoSTdir(p1) & RoSTdirVPOS_mask;
	  hgap = RoSTdir(p1) & RoSTdirHGAP;
	  if (hgap)
	    hgap = (hjust == RoSTdirLEFT) ? hgapsize : -hgapsize;
	  vgap = RoSTdir(p1) & RoSTdirVGAP;
	  if (vgap)
	    vgap = (vjust == RoSTdirBOTTOM) ? vgapsize : -vgapsize;
	  if (vjust != RoSTdirVCENTER)
	    vgap += ((vjust == RoSTdirTOP) ? -1 : 1) * (f_height - 1)/2;
	  if (strdir != hjust) {
	      shift = (hjust == RoSTdirLEFT ? 0 :
		       (hjust == RoSTdirRIGHT ? 2 : 1));
	      can_justify = justify_text(shift); /* 1 for LEFT */
	      strdir = RoSTdir(p1);
	  }
	  xstart = DTOL(RoSTx(p1) + x0) + hgap
	      - (can_justify ? 0 
		 : ((RoSTl(p1) * pari_plot.fwidth - 1) * shift / 2));
	  xend = xstart + (can_justify ? 0 : RoSTl(p1) * pari_plot.fwidth - 1);
	  if (xstart < 0 || xend >= w_width
	      || DTOL(RoSTy(p1) + y0) < 0 
	      || DTOL(RoSTy(p1) + y0) >= w_height) {
	  } else {
	      put_text(xstart,
		       w_height - 1 - DTOL(RoSTy(p1) + y0) + vgap,
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
#ifdef BOTH_GNUPLOT_AND_X11    
  if (is_builtin) {
      if (X11_init)
	  return;
      if (getenv("DISPLAY")) {
	  X11_PARI_get_plot(fatal);
	  X11_init = 1;
	  return;	  
      }
      is_builtin = 0;			/* Don't defaut to X11 if no DISPLAY */
  }
#endif	/* defined BOTH_GNUPLOT_AND_X11 */ 
  if (pari_plot.init)
    return;
  term_set( (char *) DEF_TERM );
  (void)fatal;
}


long
term_set(char *s)
{
  char *t, *size = NULL;
  double x, y;
  static int had_error;

#ifdef BOTH_GNUPLOT_AND_X11    
  if (is_builtin) {
      if (!strcmp(s,"builtin")) {
	  if (!getenv("DISPLAY"))
	      goto complain;
	  return X11_term_set(s);	  
      }
      is_builtin = 0;
      /* The following line may switch on Gnuplot's X11 term first: */
      /* PARI_get_plot(1); */
  } else if (!strcmp(s,"builtin")) {
/*      if (!X11_init) {*/
	  if (!getenv("DISPLAY")) {
	    complain:
	      croak("The builtin-X11 plotting requires DISPLAY environment variable set");
	  }	  
	  /* Restore the safe state by switching to a do-little terminal */
	  if (pari_plot.init && strcmp(pari_plot.name, "dumb"))
	      term_set("dumb");
	  is_builtin = 1;
	  X11_PARI_get_plot(1);
	  X11_init = 1;
/*      }*/
      return X11_term_set(s);
  }
#endif	/* defined BOTH_GNUPLOT_AND_X11     */ 
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
      err(talker,"name \"%s\" for terminal too long", s);
  if (*pari_plot.name && !had_error
      && (strlen(pari_plot.name) != t - s /* As strcmp() without \0 at end */
	  || (strncmp(pari_plot.name, s, t-s) != 0)) )
	reset();
  strncpy(pari_plot.name,s,t-s);
  pari_plot.name[t-s] = '\0';

  had_error = 1;
  if (!termset( pari_plot.name ))
      err(talker,"error setting terminal \"%s\"", pari_plot.name);
  had_error = 0;

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
plot_outfile_set(char *s)
{ 
    int normal = (strcmp(s,"-") == 0);

    /* Intentionally no check for is_builtin, let it always affect gnuplot:
       this way one can set the outfile before switching the terminal... */

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
#ifdef BOTH_GNUPLOT_AND_X11    
    if (is_builtin) {
	X11_set_pointsize(d);
	return;
    }
#endif	/* defined BOTH_GNUPLOT_AND_X11     */ 
    pointsize = d;
    if (pari_plot.init)
	setpointsize(d);
}

#ifdef HAS_DLOPEN
#include <dlfcn.h>

get_term_ftable_t *
get_term_ftable_get(void) /* Establish runtime link with gnuplot engine */
{
    char *s = getenv("GNUPLOT_DRAW_DLL"), *s1, buf[4096];
    void *h, *f;
    int mode = RTLD_LAZY;
    char fbuf[2048];

#ifdef RTLD_GLOBAL
	mode |= RTLD_GLOBAL;
#endif

#ifdef DYNAMIC_PLOTTING_RUNTIME_LINK
    if (!s)
	s = DYNAMIC_PLOTTING_RUNTIME_LINK;
#endif
#ifndef DYNAMIC_PLOTTING_RUNTIME_LINK_NO_PERL
    /* Allow user disabling by setting GNUPLOT_DRAW_DLL_NO_PERL=1 */
    if (!s && (!(s1 = getenv("GNUPLOT_DRAW_DLL_NO_PERL")) || !atoi(s1))) {
	char cmdbuf[256];
	FILE *p;
	char ext[256];
	char *sub;
	char name[256];
	char *n = "Gnuplot";

	/* Make 2 runs of Perl to shorten the command length */
	/* Find the directory of the Term::Gnuplot's PM and DLL extension */
	sprintf(cmdbuf, "perl -MTerm::Gnuplot -MConfig -wle %c"
		"print $INC{qq(Term/Gnuplot.pm)};print $Config{dlext}%c",
		SHELL_Q, SHELL_Q);
	p = popen(cmdbuf, "r");
	if (!p || !fgets(fbuf, sizeof(fbuf), p) || !fgets(ext, sizeof(ext), p))
	    goto end_find;
	pclose(p);
	/* Find the directory of the DLL file */
	sub = strrchr(fbuf,'/');
	if (!sub)
	    goto end_find;
	/* Do as XSLoader */
	sub[0] = 0;
	sub = strrchr(fbuf,'/');
	if (!sub)
	    goto end_find;
	if (sub - fbuf >= 9 && !strncmp(sub - 9, "/blib/lib",9)) {
	    strcpy(sub - 3,"arch/"); /* Uninstalled module */
	    sub++;
	}
	strcpy(sub + 1,"auto/Term/Gnuplot/");
	/* Find the name of the DLL file */
	sprintf(cmdbuf, "perl -MDynaLoader -we %c"
		"package DynaLoader; "
		"print mod2fname([qw(Term Gnuplot)]) if defined &mod2fname%c",
		SHELL_Q, SHELL_Q);
	p = popen(cmdbuf, "r");
	if (p) {
	    if (fgets(name, sizeof(name), p))
		n = name;
	    pclose(p);
	}
	if (strlen(fbuf) + 10 + strlen(n) + strlen(ext) > sizeof(fbuf))
	    croak("Buffer overflow finding gnuplot DLL");
	strcpy(sub + strlen(sub), n);
	strcpy(sub + strlen(sub), ".");
	strcpy(sub + strlen(sub), ext);
	sub[strlen(sub)-1] = 0;	/* Trailing \n of ext */
	s = fbuf;
    }
  end_find:
#endif
    if (!s)    /* The trailing \n is important: one may put . to the command */
	croak("Can't find Gnuplot drawing engine DLL,\n\t"
	      "set GNUPLOT_DRAW_DLL environment variable"
	      " to the name of the DLL,\n\t"
	      "or install Perl module Term::Gnuplot, e.g., by running\n\t\t"
	      "perl -MCPAN -e \"install Term::Gnuplot\"\n");
    h = dlopen(s, mode);
    if (!h) {
	sprintf(buf,"Can't load Gnuplot drawing engine from '%s': %s", s, dlerror());
	croak(buf);
	return 0;
    }
    f = dlsym(h, "get_term_ftable");
    if (f)
	return (get_term_ftable_t *)f;
    sprintf(buf, "Can't resolve 'get_term_ftable' function from Gnuplot drawing engine '%s': %s", s, dlerror());
    croak(buf);
    return 0;
}
#else	/* !( defined HAS_DLOPEN ) */

get_term_ftable_t *
get_term_ftable_get(void) /* Establish runtime link with gnuplot engine */
{
    croak("No dlopen() support present, required for dynamic gnuplot-DLL link");
    return NULL;
}

#endif	/* defined HAS_DLOPEN */ 
