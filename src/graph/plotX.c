/*******************************************************************/
/*                                                                 */
/*                       HIGH RESOLUTION PLOT                      */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "rect.h"
#include "../language/anal.h"

void  free_graph(void);

#ifdef HPPA
#  ifndef __GNUC__
     typedef char *caddr_t;
#  endif
#endif

BEGINEXTERN
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xos.h>
ENDEXTERN

static Colormap PARI_Colormap;
static XColor  *PARI_Colors;
static XColor  *PARI_ExactColors;

static char *PARI_DefaultColors[MAX_COLORS] =
{
  " ",
  "black",    /* Default */
  "blue",     /* Axes */
  "sienna",   /* Odd numbered curves in ploth */
  "red",      /* Curves, or Even numbered curves in ploth */
  "cornsilk",
  "grey",
  "gainsboro",
};

static void
PARI_ColorSetUp(Display *display, char **Colors, int n)
{
  static int init_done = 0;
  int i;

  if (init_done) return;
  init_done=1;

  PARI_Colormap = DefaultColormap(display, 0);
  PARI_Colors = (XColor *) gpmalloc((n+1) * sizeof(XColor));
  PARI_ExactColors = (XColor *) gpmalloc((n+1) * sizeof(XColor));
  for (i=1; i<n; i++)
    XAllocNamedColor(display, PARI_Colormap, Colors[i],
		     &PARI_ExactColors[i], &PARI_Colors[i]);
}

#ifdef SONY
typedef int (*XErrorHandler) (
#  if NeedFunctionPrototypes
  Display*,
  XErrorEvent*
#  endif
  );

extern XErrorHandler XSetErrorHandler (
#  if NeedFunctionPrototypes
  XErrorHandler	
#  endif
  );

typedef int (*XIOErrorHandler) (
#  if NeedFunctionPrototypes
  Display*	
#  endif
  );

extern XIOErrorHandler XSetIOErrorHandler (
#  if NeedFunctionPrototypes
  XIOErrorHandler
#  endif
  );
#endif

/* after fork(), we don't want the child to recover but to exit */
static void
exiterr(char *str)
{
  term_color(c_ERR);
  fprintferr("\n  *** X fatal error: %s\n",str);
  term_color(c_NONE); exit(1);
}

#define MAX_BUF 256

static int
Xerror(Display *d, XErrorEvent *err) {
  char buf[MAX_BUF];
  XGetErrorText(d,err->error_code,buf,MAX_BUF);
  exiterr(buf); return 0;
}

static int
IOerror(Display *d) {
  char buf[MAX_BUF];
  sprintf(buf, "lost display on %s", DisplayString(d));
  exiterr(buf); return 0;
}

static char*
zmalloc(size_t x)
{
  return x? gpmalloc(x): NULL;
}

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free)
{
  long *ptx,*pty,*c;
  long *numpoints[MAX_COLORS],*numtexts[MAX_COLORS];
  long *xtexts[MAX_COLORS],*ytexts[MAX_COLORS];
  long rcolcnt[MAX_COLORS][ROt_MAX];
  long col,i,j,x0,y0,a,b,oldwidth,oldheight,force;
  long rcnt[ROt_MAX+1];
  char **texts[MAX_COLORS];
  PariRect *e;
  RectObj *p1;
  double xs=1,ys=1;

  int screen;
  Display *display;
  GC gc;
  Window win;
  XEvent event;
  XSizeHints size_hints;
  XFontStruct *font_info;
  XSetWindowAttributes attrib;
  XPoint *points[MAX_COLORS],**lines[MAX_COLORS];
  XSegment *seg[MAX_COLORS];
  XRectangle *rec[MAX_COLORS];
  Atom wm_delete_window, wm_protocols;

  if (fork()) return;  /* parent process returns */

  /* child process goes on */
  freeall();  /* PARI stack isn't needed anymore, keep rectgraph */
  PARI_get_plot(1);
  display = XOpenDisplay(NULL);
  font_info = XLoadQueryFont(display, "9x15");
  if (!font_info) exiterr("cannot open 9x15 font");

  XSetErrorHandler(Xerror);
  XSetIOErrorHandler(IOerror);
  PARI_ColorSetUp(display,PARI_DefaultColors,MAX_COLORS);

  for(col=1;col<MAX_COLORS;col++)
  {
    rcolcnt[col][ROt_MV]=rcolcnt[col][ROt_PT]=rcolcnt[col][ROt_LN]=0;
    rcolcnt[col][ROt_BX]=rcolcnt[col][ROt_MP]=rcolcnt[col][ROt_ML]=0;
    rcolcnt[col][ROt_ST]=rcolcnt[col][ROt_PTT]=rcolcnt[col][ROt_PTS]=rcolcnt[col][ROt_LNT]=0;
  }

  for(i=0;i<lw;i++)
  {
    e=rectgraph[w[i]]; p1=RHead(e);
    while(p1)
    {
      switch(RoType(p1))
      {
	case ROt_MP : rcolcnt[RoCol(p1)][ROt_PT] += RoMPcnt(p1);
	              break;                 /* Multiple Point */
	case ROt_PT :                        /* Point */
	case ROt_LN :                        /* Line */
	case ROt_BX :                        /* Box */
	case ROt_ML :                        /* Multiple lines */
	case ROt_ST : rcolcnt[RoCol(p1)][RoType(p1)]++;
	              break;                 /* String */
	case ROt_MV :                        /* Move */
	case ROt_PTT:                        /* Point type change */
	case ROt_PTS:                        /* Point size change */
	case ROt_LNT: rcnt[RoType(p1)]++;    /* Line type change */
      }
      p1=RoNext(p1);
    }
  }
  for (col=1; col<MAX_COLORS; col++)
  {
    char *m;
    c = rcolcnt[col];
    points[col]=(XPoint*)zmalloc(c[ROt_PT]*sizeof(XPoint));
    seg[col]=(XSegment*)zmalloc(c[ROt_LN]*sizeof(XSegment));
    rec[col]=(XRectangle*)zmalloc(c[ROt_BX]*sizeof(XRectangle));

    i = c[ROt_ML]; m = zmalloc(i * (sizeof(long) + sizeof(XPoint*)));
    numpoints[col]=(long*)m; i *= sizeof(XPoint*);
    m += i; lines[col]=(XPoint**)m;

    i = c[ROt_ST]; m = zmalloc(i * (sizeof(char*) + 3*sizeof(long)));
    texts[col]=(char**)m; i *= sizeof(long);
    m += i; numtexts[col]=(long*)m;
    m += i; xtexts[col]=(long*)m;
    m += i; ytexts[col]=(long*)m;

    c[ROt_PT]=c[ROt_LN]=c[ROt_BX]=c[ROt_ML]=c[ROt_ST]=0;
  }

  screen = DefaultScreen(display);
  win = XCreateSimpleWindow
    (display, RootWindow(display, screen), 0, 0, w_width, w_height,
     4, BlackPixel(display, screen), WhitePixel(display, screen));

  size_hints.flags = PPosition | PSize;
  size_hints.x = 0;
  size_hints.y = 0;
  size_hints.width  = w_width;
  size_hints.height = w_height;
  XSetStandardProperties
    (display, win, "rectplot", NULL, None, NULL, 0, &size_hints);

  wm_delete_window = XInternAtom(display, "WM_DELETE_WINDOW", False);
  wm_protocols = XInternAtom(display, "WM_PROTOCOLS", False);
  XSetWMProtocols(display,win,&wm_delete_window, 1);

  XSelectInput (display, win,
    ExposureMask | ButtonPressMask | StructureNotifyMask);

  /* enable backing-store */
  attrib.backing_store = Always;
  attrib.backing_planes = AllPlanes;
  XChangeWindowAttributes(display,win,CWBackingStore|CWBackingPlanes,&attrib);

  gc = XCreateGC(display, win, 0, NULL);
  XSetFont(display, gc, font_info->fid);

  XMapWindow(display, win);
  oldwidth  = w_width;
  oldheight = w_height; force = 1;

  for(;;)
  {
    XNextEvent(display, &event);
    switch(event.type)
    {
      case ClientMessage:
        if (event.xclient.message_type != wm_protocols ||
            event.xclient.data.l[0] != wm_delete_window) break;
      case ButtonPress:
      case DestroyNotify:
	XUnloadFont(display,font_info->fid); XFreeGC(display,gc);
#define myfree(x) if (x) free(x)
	for(col=1;col<MAX_COLORS;col++)
	{
	  myfree(points[col]); myfree(seg[col]); myfree(rec[col]);
	  for(i=0;i<rcolcnt[col][ROt_ML];i++) myfree(lines[col][i]);
	  myfree(numpoints[col]); myfree(texts[col]);
        }
#undef myfree
	free_graph(); if (do_free) { free(w); free(x); free(y); }
	XCloseDisplay(display); exit(0);

      case ConfigureNotify:
      {
        int width  = event.xconfigure.width;
        int height = event.xconfigure.height;

        if (width == oldwidth && height == oldheight) break;
        oldwidth  = width;
        oldheight = height; force = 1;

        /* recompute scale */
	xs=((double)width)/w_width; ys=((double)height)/w_height;
      }
      case Expose: if (!force) break;
        force = 0;
	for(i=0; i<lw; i++)
	{
	  e=rectgraph[w[i]];p1=RHead(e);x0=x[i];y0=y[i];
	  while(p1)
	  {
	    col=RoCol(p1); c=rcolcnt[col];
	    switch(RoType(p1))
	    {
	      case ROt_PT:
		points[col][c[ROt_PT]].x=(long)((RoPTx(p1)+x0)*xs);
		points[col][c[ROt_PT]].y=(long)((RoPTy(p1)+y0)*ys);
		c[ROt_PT]++;break;
	      case ROt_LN:
		seg[col][c[ROt_LN]].x1= (long)((RoLNx1(p1)+x0)*xs);
		seg[col][c[ROt_LN]].y1= (long)((RoLNy1(p1)+y0)*ys);
		seg[col][c[ROt_LN]].x2= (long)((RoLNx2(p1)+x0)*xs);
		seg[col][c[ROt_LN]].y2= (long)((RoLNy2(p1)+y0)*ys);
		c[ROt_LN]++;break;
	      case ROt_BX:
		a=rec[col][c[ROt_BX]].x = (long)((RoBXx1(p1)+x0)*xs);
		b=rec[col][c[ROt_BX]].y = (long)((RoBXy1(p1)+y0)*ys);
		rec[col][c[ROt_BX]].width = (long)((RoBXx2(p1)+x0-a)*xs);
		rec[col][c[ROt_BX]].height = (long)((RoBXy2(p1)+y0-b)*ys);
		c[ROt_BX]++;break;
	      case ROt_MP:
		ptx=RoMPxs(p1); pty=RoMPys(p1);
		for(j=0;j<RoMPcnt(p1);j++)
		{
		  points[col][c[ROt_PT]+j].x= (long)((ptx[j]+x0)*xs);
		  points[col][c[ROt_PT]+j].y= (long)((pty[j]+y0)*ys);
		}
		c[ROt_PT]+=RoMPcnt(p1);break;
	      case ROt_ML:
		ptx=RoMLxs(p1); pty=RoMLys(p1);
		numpoints[col][c[ROt_ML]] = RoMLcnt(p1);
		lines[col][c[ROt_ML]] =
		  (XPoint*)zmalloc(RoMLcnt(p1)*sizeof(XPoint));
		for(j=0;j<RoMLcnt(p1);j++)
		{
		  lines[col][c[ROt_ML]][j].x= (long)((ptx[j]+x0)*xs);
		  lines[col][c[ROt_ML]][j].y= (long)((pty[j]+y0)*ys);
		}
		c[ROt_ML]++;break;
	      case ROt_ST:
		texts[col][c[ROt_ST]]=RoSTs(p1);
		numtexts[col][c[ROt_ST]]=RoSTl(p1);
		xtexts[col][c[ROt_ST]]= (long)((RoSTx(p1)+x0)*xs);
		ytexts[col][c[ROt_ST]]= (long)((RoSTy(p1)+y0)*ys);
		c[ROt_ST]++;break;
	      default: break;
	    }
	    p1=RoNext(p1);
	  }
	}
	for(col=1; col<MAX_COLORS; col++)
	{
          c = rcolcnt[col];
	  XSetForeground(display, gc, PARI_Colors[col].pixel);
	  if(c[ROt_PT]) XDrawPoints(display,win,gc,points[col],c[ROt_PT],0);
	  if(c[ROt_LN]) XDrawSegments(display,win,gc,seg[col],c[ROt_LN]);
	  if(c[ROt_BX]) XDrawRectangles(display,win,gc,rec[col],c[ROt_BX]);
	  for(i=0;i<c[ROt_ML];i++)
	    XDrawLines(display,win,gc,lines[col][i],numpoints[col][i],0);
	  for(i=0;i<c[ROt_ST];i++)
	    XDrawString(display,win,gc, xtexts[col][i],ytexts[col][i],
              texts[col][i],numtexts[col][i]);

	  c[ROt_PT]=c[ROt_LN]=c[ROt_BX]=c[ROt_ML]=c[ROt_ST]=0;
        }
    }
  }
}

void
PARI_get_plot(long fatal)
{
  Display *display;
  int screen;

  if (pari_plot.init) return;
  if (!(display = XOpenDisplay(NULL)))
  {
    if (fatal) exiterr("no X server");
    err(talker, "no X server");
  }
  screen = DefaultScreen(display);
  w_width = DisplayWidth(display, screen) - 40;
  w_height = DisplayHeight(display, screen) - 60;
  f_height = 15; f_width = 9;
  h_unit = 5; v_unit = 5;
  pari_plot.init = 1;
  XCloseDisplay(display);
}

long
term_set(char *s) { return 1; }

long
plot_outfile_set(char *s) { return 1; }

void
set_pointsize(double d) 
{
}
