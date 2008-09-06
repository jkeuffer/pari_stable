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
/*                         PLOT ROUTINES                           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
#include "rect.h"

void postdraw0(long *w, long *x, long *y, long lw, long scale);
static void PARI_get_psplot(void);

#define NUMRECT 18

/* no need for THREAD: OK to share this */
static hashtable *rgb_colors = NULL;
PariRect *rectgraph[NUMRECT];

/* no need for THREAD: gp-specific */
static long current_color[NUMRECT];

PARI_plot pari_plot, pari_psplot;
PARI_plot *pari_plot_engine = &pari_plot;
long rectpoint_itype = 0, rectline_itype  = 0;

const long STRINGRECT = NUMRECT-2, DRAWRECT = NUMRECT-1;

const long PLOTH_NUMPOINTS = 1000, PARAM_NUMPOINTS = 1500, RECUR_NUMPOINTS = 8;
const long RECUR_MAXDEPTH = 10, PARAMR_MAXDEPTH = 10;
const double RECUR_PREC = 0.001;

const long DEFAULT_COLOR = 1, AXIS_COLOR = 2;

INLINE long
DTOL(double t) { return (long)(t + 0.5); }

/********************************************************************/
/**                                                                **/
/**                         LOW-RES PLOT                           **/
/**                                                                **/
/********************************************************************/
#define ISCR 64
#define JSCR 22
const char BLANK = ' ', YY = '|', XX_UPPER = '\'', XX_LOWER = '.';
static char
PICT(long j) {
  switch(j%3) {
    case 0:  return '_';
    case 1:  return 'x';
    default: return '"';
  }
}
static char
PICTZERO(long j) {
  switch(j%3) {
    case 0:  return ',';
    case 1:  return '-';
    default: return '`';
  }
}

static char *
dsprintf9(double d, char *buf)
{
  int i = 10;

  while (--i >= 0) {
    sprintf(buf, "%9.*g", i, d);
    if (strlen(buf) <= 9) return buf;
  }
  return buf; /* Should not happen? */
}

typedef unsigned char screen[ISCR+1][JSCR+1];

static void
fill_gap(screen scr, long i, int jnew, int jpre)
{
  int mid, i_up, i_lo, up, lo;

  if (jpre < jnew - 2) {
    up = jnew - 1; i_up = i;
    lo = jpre + 1; i_lo = i - 1;
  } else if (jnew < jpre - 2) {
    up = jpre - 1; i_up = i - 1;
    lo = jnew + 1; i_lo = i;
  } else return; /* if gap < 2, leave it as it is. */

  mid = (jpre+jnew)/2;
  if (mid>JSCR) mid=JSCR; else if (mid<0) mid=0;
  if (lo<0) lo=0;
  if (lo<=JSCR) while (lo <= mid) scr[i_lo][lo++] = ':';
  if (up>JSCR) up=JSCR;
  if (up>=0) while (up > mid) scr[i_up][up--] = ':';
}

static double
todbl(GEN x) { return rtodbl(gtofp(x, 3)); }

static GEN
READ_EXPR(GEN code, GEN x) {
  if (typ(code)!=t_CLOSURE) return gsubst(code,0,x);
  set_lex(-1, x); return closure_evalgen(code);
}

void
plot(GEN a, GEN b, GEN code, GEN ysmlu,GEN ybigu, long prec)
{
  long jz, j, i, sig;
  pari_sp av = avma, av2, limite;
  int jnew, jpre = 0; /* for lint */
  GEN x, dx;
  double diff, dyj, ysml, ybig, y[ISCR+1];
  screen scr;
  char buf[80], z;

  sig=gcmp(b,a); if (!sig) return;
  if (sig<0) { x=a; a=b; b=x; }
  x = gtofp(a, prec); push_lex(x);
  dx = divru(gtofp(gsub(b,a),prec), ISCR-1);
  ysml = ybig = 0.;
  for (j=1; j<=JSCR; j++) scr[1][j]=scr[ISCR][j]=YY;
  for (i=2; i<ISCR; i++)
  {
    scr[i][1]   = XX_LOWER;
    scr[i][JSCR]= XX_UPPER;
    for (j=2; j<JSCR; j++) scr[i][j] = BLANK;
  }
  av2 = avma; limite=stack_lim(av2,1);
  for (i=1; i<=ISCR; i++)
  {
    y[i] = gtodouble( READ_EXPR(code,x) );
    if (y[i] < ysml) ysml = y[i];
    if (y[i] > ybig) ybig = y[i];
    x = addrr(x,dx);
    if (low_stack(limite, stack_lim(av2,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"plot");
      x = gerepileuptoleaf(av2, x);
    }
  }
  avma = av;
  if (ysmlu) ysml = gtodouble(ysmlu);
  if (ybigu) ybig = gtodouble(ybigu);
  diff = ybig - ysml;
  if (!diff) { ybig += 1; diff= 1.; }
  dyj = ((JSCR-1)*3+2) / diff;
  jz = 3 - DTOL(ysml*dyj);
  z = PICTZERO(jz); jz = jz/3;
  for (i=1; i<=ISCR; i++, avma = av2)
  {
    if (0<=jz && jz<=JSCR) scr[i][jz]=z;
    j = 3 + DTOL((y[i]-ysml)*dyj);
    jnew = j/3;
    if (i > 1) fill_gap(scr, i, jnew, jpre);
    if (0<=jnew && jnew<=JSCR) scr[i][jnew] = PICT(j);
    jpre = jnew;
  }
  pari_putc('\n');
  pari_printf("%s ", dsprintf9(ybig, buf));
  for (i=1; i<=ISCR; i++) pari_putc(scr[i][JSCR]);
  pari_putc('\n');
  for (j=(JSCR-1); j>=2; j--)
  {
    pari_puts("          ");
    for (i=1; i<=ISCR; i++) pari_putc(scr[i][j]);
    pari_putc('\n');
  }
  pari_printf("%s ", dsprintf9(ysml, buf));
  for (i=1; i<=ISCR; i++)  pari_putc(scr[i][1]);
  pari_putc('\n');
  {
    char line[10 + 32 + 32 + ISCR - 9];
    sprintf(line, "%10s%-9.7g%*.7g\n"," ",todbl(a),ISCR-9,todbl(b));
    pari_printf(line);
  }
  pop_lex();
}

/********************************************************************/
/**                                                                **/
/**                      RECTPLOT FUNCTIONS                        **/
/**                                                                **/
/********************************************************************/
void
init_graph(void)
{
  long n;
  for (n=0; n<NUMRECT; n++)
  {
    PariRect *e = (PariRect*) pari_malloc(sizeof(PariRect));
    e->head = e->tail = NULL;
    e->sizex = e->sizey = 0;
    current_color[n] = DEFAULT_COLOR;
    rectgraph[n] = e;
  }
}

void
free_graph(void)
{
  int i;
  for (i=0; i<NUMRECT; i++)
  {
    PariRect *e = rectgraph[i];
    if (RHead(e)) killrect(i);
    pari_free((void *)e);
  }
  if (rgb_colors)
  {
    free((void*)rgb_colors->table);
    free((void*)rgb_colors);
  }
  if (pari_colormap) free(pari_colormap);
  if (pari_graphcolors) free(pari_graphcolors);
}

static PariRect *
check_rect(long ne)
{
  if (ne >= 0 && ne < NUMRECT) return rectgraph[ne];
  pari_err(talker,
           "incorrect rectwindow number in graphic function (%ld not in [0, %ld])",
           ne, NUMRECT-1);
  return NULL; /*not reached*/
}

static PariRect *
check_rect_init(long ne)
{
  PariRect *e = check_rect(ne);
  if (!RHead(e)) pari_err(talker,"you must initialize the rectwindow first");
  return e;
}

static long
initrect_get_arg(GEN x, long flag, long *dft)
{ /* FIXME: gcmp0(x) undocumented backward compatibility hack */
  if (!x || gcmp0(x) || flag) { PARI_get_plot(0); return *dft - 1; }
  if (typ(x) != t_INT) pari_err(typeer, "initrect");
  return itos(x);
}
void
initrect_gen(long ne, GEN x, GEN y, long flag)
{
  long xi, yi;

  xi = initrect_get_arg(x, flag, &pari_plot.width);
  yi = initrect_get_arg(y, flag, &pari_plot.height);
  if (flag) {
    if (x) xi = DTOL(xi * gtodouble(x));
    if (y) yi = DTOL(yi * gtodouble(y));
  }
  initrect(ne, xi, yi);
}

static void
Rchain(PariRect *e, RectObj *z)
{
  if (!RHead(e)) RHead(e) = z; else RoNext(RTail(e)) = z;
  RTail(e) = z;
  RoNext(z) = 0;
}

void
initrect(long ne, long x, long y)
{
  PariRect *e;
  RectObj *z;

  if (x<=1 || y<=1) pari_err(talker,"incorrect dimensions in initrect");
  e = check_rect(ne); if (RHead(e)) killrect(ne);

  z = (RectObj*) pari_malloc(sizeof(RectObj));
  RoType(z) = ROt_NULL;
  Rchain(e, z);
  RXsize(e) = x; RXcursor(e) = 0;
  RYsize(e) = y; RYcursor(e) = 0;
  RXscale(e) = 1; RXshift(e) = 0;
  RYscale(e) = 1; RYshift(e) = 0;
  RHasGraph(e) = 0;
}

GEN
rectcursor(long ne)
{
  PariRect *e = check_rect_init(ne);
  return mkvec2s((long)RXcursor(e), (long)RYcursor(e));
}

static void
rectscale0(long ne, double x1, double x2, double y1, double y2)
{
  PariRect *e = check_rect_init(ne);
  double x, y;

  x = RXshift(e) + RXscale(e) * RXcursor(e);
  y = RYshift(e) + RYscale(e) * RYcursor(e);
  RXscale(e) = RXsize(e)/(x2-x1); RXshift(e) = -x1*RXscale(e);
  RYscale(e) = RYsize(e)/(y1-y2); RYshift(e) = -y2*RYscale(e);
  RXcursor(e) = (x - RXshift(e)) / RXscale(e);
  RYcursor(e) = (y - RYshift(e)) / RYscale(e);
}

void
rectscale(long ne, GEN x1, GEN x2, GEN y1, GEN y2)
{
  rectscale0(ne, gtodouble(x1), gtodouble(x2), gtodouble(y1), gtodouble(y2));
}

static void
rectmove0(long ne, double x, double y, long relative)
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj1P));

  if (relative) { RXcursor(e) += x; RYcursor(e) += y; }
  else          { RXcursor(e) = x; RYcursor(e) = y; }
  RoType(z) = ROt_MV;
  RoMVx(z) = RXcursor(e) * RXscale(e) + RXshift(e);
  RoMVy(z) = RYcursor(e) * RYscale(e) + RYshift(e);
  Rchain(e, z);
}

void
rectmove(long ne, GEN x, GEN y)
{
  rectmove0(ne,gtodouble(x),gtodouble(y),0);
}

void
rectrmove(long ne, GEN x, GEN y)
{
  rectmove0(ne,gtodouble(x),gtodouble(y),1);
}

void
rectpoint0(long ne, double x, double y,long relative) /* code = ROt_MV/ROt_PT */
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj1P));

  if (relative) { RXcursor(e) += x; RYcursor(e) += y; }
  else          { RXcursor(e) = x; RYcursor(e) = y; }
  RoPTx(z) = RXcursor(e)*RXscale(e) + RXshift(e);
  RoPTy(z) = RYcursor(e)*RYscale(e) + RYshift(e);
  RoType(z) = ( DTOL(RoPTx(z)) < 0
		|| DTOL(RoPTy(z)) < 0 || DTOL(RoPTx(z)) > RXsize(e)
		|| DTOL(RoPTy(z)) > RYsize(e) ) ? ROt_MV : ROt_PT;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectpoint(long ne, GEN x, GEN y)
{
  rectpoint0(ne,gtodouble(x),gtodouble(y),0);
}

void
rectrpoint(long ne, GEN x, GEN y)
{
  rectpoint0(ne,gtodouble(x),gtodouble(y),1);
}

void
rectcolor(long ne, long c)
{
  check_rect(ne);
  if (c < 1 || c >= lg(pari_colormap)-1)
    pari_err(talker,"This is not a valid color");
  current_color[ne] = c;
}

void
rectline0(long ne, double gx2, double gy2, long relative) /* code = ROt_MV/ROt_LN */
{
  double dx,dy,dxy,xmin,xmax,ymin,ymax,x1,y1,x2,y2;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));
  const double c = 1 + 1e-10;

  x1 = RXcursor(e)*RXscale(e) + RXshift(e);
  y1 = RYcursor(e)*RYscale(e) + RYshift(e);
  if (relative)
    { RXcursor(e)+=gx2; RYcursor(e)+=gy2; }
  else
    { RXcursor(e)=gx2; RYcursor(e)=gy2; }
  x2 = RXcursor(e)*RXscale(e) + RXshift(e);
  y2 = RYcursor(e)*RYscale(e) + RYshift(e);
  xmin = maxdd(mindd(x1,x2),0); xmax = mindd(maxdd(x1,x2),RXsize(e));
  ymin = maxdd(mindd(y1,y2),0); ymax = mindd(maxdd(y1,y2),RYsize(e));
  dxy = x1*y2 - y1*x2; dx = x2-x1; dy = y2-y1;
  if (dy)
  {
    if (dx*dy<0)
      { xmin = maxdd(xmin,(dxy+RYsize(e)*dx)/dy); xmax=mindd(xmax,dxy/dy); }
    else
      { xmin=maxdd(xmin,dxy/dy); xmax=mindd(xmax,(dxy+RYsize(e)*dx)/dy); }
  }
  if (dx)
  {
    if (dx*dy<0)
      { ymin=maxdd(ymin,(RXsize(e)*dy-dxy)/dx); ymax=mindd(ymax,-dxy/dx); }
    else
      { ymin=maxdd(ymin,-dxy/dx); ymax=mindd(ymax,(RXsize(e)*dy-dxy)/dx); }
  }
  RoLNx1(z) = xmin; RoLNx2(z) = xmax;
  if (dx*dy<0) { RoLNy1(z) = ymax; RoLNy2(z) = ymin; }
  else         { RoLNy1(z) = ymin; RoLNy2(z) = ymax; }
  RoType(z) = (xmin>xmax*c || ymin>ymax*c) ? ROt_MV : ROt_LN;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

/* Given coordinates of ends of a line, and labels l1 l2 attached to the
   ends, plot ticks where the label coordinate takes "round" values */

static void
rectticks(PARI_plot *WW, long ne,
	  double dx1, double dy1, double dx2, double dy2,
	  double l1, double l2, long flags)
{
  long dx,dy,dxy,dxy1,x1,y1,x2,y2,nticks,n,n1,dn;
  double minstep, maxstep, step, l_min, l_max, minl, maxl, dl, dtx, dty, x, y;
  double ddx, ddy;
  const double mult[3] = { 2./1., 5./2., 10./5. };
  PariRect *e = check_rect_init(ne);
  int do_double = !(flags & TICKS_NODOUBLE);

  x1 = DTOL(dx1*RXscale(e) + RXshift(e));
  y1 = DTOL(dy1*RYscale(e) + RYshift(e));
  x2 = DTOL(dx2*RXscale(e) + RXshift(e));
  y2 = DTOL(dy2*RYscale(e) + RYshift(e));
  dx = x2 - x1;
  dy = y2 - y1;
  if (dx < 0) dx = -dx;
  if (dy < 0) dy = -dy;
  dxy1 = maxss(dx, dy);
  dx /= WW->hunit;
  dy /= WW->vunit;
  if (dx > 1000 || dy > 1000)
    dxy = 1000; /* avoid overflow */
  else
    dxy = (long)sqrt(dx*dx + dy*dy);
  nticks = (long) ((dxy + 2.5)/4);
  if (!nticks) return;

  /* Now we want to find nticks (or less) "round" numbers between l1 and l2.
     For our purpose round numbers have "last significant" digit either
	*) any;
	*) even;
	*) divisible by 5.
     We need to choose which alternative is better.
   */
  if (l1 < l2)
    l_min = l1, l_max = l2;
  else
    l_min = l2, l_max = l1;
  minstep = (l_max - l_min)/(nticks + 1);
  maxstep = 2.5*(l_max - l_min);
  step = exp(log(10) * floor(log10(minstep)));
  if (!(flags & TICKS_ENDSTOO)) {
    double d = 2*(l_max - l_min)/dxy1;	/* Two pixels off */

    l_min += d;
    l_max -= d;
  }
  for (n = 0; ; n++) {
    if (step >= maxstep) return;

    if (step >= minstep) {
      minl = ceil(l_min/step);
      maxl = floor(l_max/step);
      if (minl <= maxl && maxl - minl + 1 <= nticks) {
	nticks = (long) (maxl - minl + 1);
	l_min = minl * step;
	l_max = maxl * step; break;
      }
    }
    step *= mult[ n % 3 ];
  }
  /* Where to position doubleticks, variants:
     small: each 5, double: each 10	(n===2 mod 3)
     small: each 2, double: each 10	(n===1 mod 3)
     small: each 1, double: each  5 */
  dn = (n % 3 == 2)? 2: 5;
  n1 = ((long)minl) % dn; /* unused if do_double = FALSE */

  /* now l_min and l_max keep min/max values of l with ticks, and nticks is
     the number of ticks to draw. */
  if (nticks == 1) ddx = ddy = 0; /* unused: for lint */
  else {
    dl = (l_max - l_min)/(nticks - 1);
    ddx = (dx2 - dx1) * dl / (l2 - l1);
    ddy = (dy2 - dy1) * dl / (l2 - l1);
  }
  x = dx1 + (dx2 - dx1) * (l_min - l1) / (l2 - l1);
  y = dy1 + (dy2 - dy1) * (l_min - l1) / (l2 - l1);
  /* assume hunit and vunit form a square.  For clockwise ticks: */
  dtx = WW->hunit * dy/dxy * (y2 > y1 ? 1 : -1);	/* y-coord runs down */
  dty = WW->vunit * dx/dxy * (x2 > x1 ? 1 : -1);
  for (n = 0; n < nticks; n++) {
    RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));
    double lunit = WW->hunit > 1 ? 1.5 : 2;
    double l = (do_double && (n + n1) % dn == 0) ? lunit: 1;

    RoLNx1(z) = RoLNx2(z) = x*RXscale(e) + RXshift(e);
    RoLNy1(z) = RoLNy2(z) = y*RYscale(e) + RYshift(e);

    if (flags & TICKS_CLOCKW) {
      RoLNx1(z) += dtx*l;
      RoLNy1(z) -= dty*l; /* y-coord runs down */
    }
    if (flags & TICKS_ACLOCKW) {
      RoLNx2(z) -= dtx*l;
      RoLNy2(z) += dty*l; /* y-coord runs down */
    }
    RoType(z) = ROt_LN;

    Rchain(e, z);
    RoCol(z) = current_color[ne];
    x += ddx;
    y += ddy;
  }
}

void
rectline(long ne, GEN gx2, GEN gy2)
{
  rectline0(ne, gtodouble(gx2), gtodouble(gy2),0);
}

void
rectrline(long ne, GEN gx2, GEN gy2)
{
  rectline0(ne, gtodouble(gx2), gtodouble(gy2),1);
}

void
rectbox0(long ne, double gx2, double gy2, long relative)
{
  double x1,y1,x2,y2,xmin,ymin,xmax,ymax;
  double xx,yy;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));

  x1 = RXcursor(e)*RXscale(e) + RXshift(e);
  y1 = RYcursor(e)*RYscale(e) + RYshift(e);
  if (relative)
  { xx = RXcursor(e)+gx2; yy = RYcursor(e)+gy2; }
  else
  {  xx = gx2; yy = gy2; }
  x2 = xx*RXscale(e) + RXshift(e);
  y2 = yy*RYscale(e) + RYshift(e);
  xmin = maxdd(mindd(x1,x2),0); xmax = mindd(maxdd(x1,x2),RXsize(e));
  ymin = maxdd(mindd(y1,y2),0); ymax = mindd(maxdd(y1,y2),RYsize(e));

  RoType(z) = ROt_BX;
  RoBXx1(z) = xmin; RoBXy1(z) = ymin;
  RoBXx2(z) = xmax; RoBXy2(z) = ymax;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectbox(long ne, GEN gx2, GEN gy2)
{
  rectbox0(ne, gtodouble(gx2), gtodouble(gy2), 0);
}

void
rectrbox(long ne, GEN gx2, GEN gy2)
{
  rectbox0(ne, gtodouble(gx2), gtodouble(gy2), 1);
}

static void
freeobj(RectObj *z) {
  switch(RoType(z)) {
    case ROt_MP: case ROt_ML:
      pari_free(RoMPxs(z));
      pari_free(RoMPys(z)); break;
    case ROt_ST:
      pari_free(RoSTs(z)); break;
  }
  pari_free(z);
}


void
killrect(long ne)
{
  RectObj *z, *t;
  PariRect *e = check_rect_init(ne);

  current_color[ne]=DEFAULT_COLOR;
  z=RHead(e);
  RHead(e) = RTail(e) = NULL;
  RXsize(e) = RYsize(e) = 0;
  RXcursor(e) = RYcursor(e) = 0;
  RXscale(e) = RYscale(e) = 1;
  RXshift(e) = RYshift(e) = 0;
  while (z) { t = RoNext(z); freeobj(z); z = t; }
}

void
rectpoints0(long ne, double *listx, double *listy, long lx) /* code = ROt_MP */
{
  double *ptx, *pty, x, y;
  long i, cp=0;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjMP));

  RoMPxs(z) = ptx = (double*) pari_malloc(lx*sizeof(double));
  RoMPys(z) = pty = (double*) pari_malloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    x = RXscale(e)*listx[i] + RXshift(e);
    y = RYscale(e)*listy[i] + RYshift(e);
    if (x>=0 && y>=0 && x<=RXsize(e) && y<=RYsize(e))
    {
      ptx[cp]=x; pty[cp]=y; cp++;
    }
  }
  RoType(z) = ROt_MP;
  RoMPcnt(z) = cp;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectpoints(long ne, GEN listx, GEN listy)
{
  long i,lx, tx=typ(listx), ty=typ(listy);
  double *px,*py;

  if (!is_matvec_t(tx) || !is_matvec_t(ty)) {
    rectpoint(ne, listx, listy); return;
  }
  lx = lg(listx);
  if (tx == t_MAT || ty == t_MAT || lg(listy) != lx) pari_err(typeer,"rectpoints");
  lx--; if (!lx) return;

  px = (double*) pari_malloc(lx*sizeof(double)); listx++;
  py = (double*) pari_malloc(lx*sizeof(double)); listy++;
  for (i=0; i<lx; i++)
  {
    px[i] = gtodouble(gel(listx,i));
    py[i] = gtodouble(gel(listy,i));
  }
  rectpoints0(ne,px,py,lx);
  pari_free(px); pari_free(py);
}

void
rectlines0(long ne, double *x, double *y, long lx, long flag) /* code = ROt_ML */
{
  long i,I;
  double *ptx,*pty;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));

  I = flag ? lx+1 : lx;
  ptx = (double*) pari_malloc(I*sizeof(double));
  pty = (double*) pari_malloc(I*sizeof(double));
  for (i=0; i<lx; i++)
  {
    ptx[i] = RXscale(e)*x[i] + RXshift(e);
    pty[i] = RYscale(e)*y[i] + RYshift(e);
  }
  if (flag)
  {
    ptx[i] = RXscale(e)*x[0] + RXshift(e);
    pty[i] = RYscale(e)*y[0] + RYshift(e);
  }
  Rchain(e, z);
  RoType(z) = ROt_ML;
  RoMLcnt(z) = lx;
  RoMLxs(z) = ptx;
  RoMLys(z) = pty;
  RoCol(z) = current_color[ne];
}

void
rectlines(long ne, GEN listx, GEN listy, long flag)
{
  long tx=typ(listx), ty=typ(listy), lx=lg(listx), i;
  double *x, *y;

  if (!is_matvec_t(tx) || !is_matvec_t(ty))
  {
    rectline(ne, listx, listy); return;
  }
  if (tx == t_MAT || ty == t_MAT || lg(listy) != lx) pari_err(typeer,"rectlines");
  lx--; if (!lx) return;

  x = (double*) pari_malloc(lx*sizeof(double));
  y = (double*) pari_malloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    x[i] = gtodouble(gel(listx,i+1));
    y[i] = gtodouble(gel(listy,i+1));
  }
  rectlines0(ne,x,y,lx,flag);
  pari_free(x); pari_free(y);
}

static void
put_string(long win, long x, long y, char *str, long dir)
{
  rectmove0(win,(double)x,(double)y,0); rectstring3(win,str,dir);
}

void
rectstring(long ne, char *str)
{
  rectstring3(ne,str,RoSTdirLEFT);
}

/* Allocate memory, then put string */
void
rectstring3(long ne, char *str, long dir) /* code = ROt_ST */
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjST));
  long l = strlen(str);
  char *s = (char *) pari_malloc(l+1);

  strcpy(s,str);
  RoType(z) = ROt_ST;
  RoSTl(z) = l;
  RoSTs(z) = s;
  RoSTx(z) = RXscale(e)*RXcursor(e)+RXshift(e);
  RoSTy(z) = RYscale(e)*RYcursor(e)+RYshift(e);
  RoSTdir(z) = dir;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectpointtype(long ne, long type) /* code = ROt_PTT */
{
 if (ne == -1) {
   rectpoint_itype = type;
 } else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPN));

   RoType(z) = ROt_PTT;
   RoPTTpen(z) = type;
   Rchain(e, z);
 }
}

/*FIXME: this function is a noop, since no graphic driver implement
 * the ROt_PTS code. ne==-1 is a legacy, meaningless value. */
void
rectpointsize(long ne, GEN size) /* code = ROt_PTS */
{
 if (ne == -1) { /*do nothing*/ }
 else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPS));

   RoType(z) = ROt_PTS;
   RoPTSsize(z) = gtodouble(size);
   Rchain(e, z);
 }
}

void
rectlinetype(long ne, long type)
{
 if (ne == -1) {
   rectline_itype = type;
 } else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPN));

   RoType(z) = ROt_LNT;
   RoLNTpen(z) = type;
   Rchain(e, z);
 }
}

void
rectcopy_gen(long source, long dest, GEN xoff, GEN yoff, long flag)
{
  long xi, yi;
  if (flag & RECT_CP_RELATIVE) {
    double xd = gtodouble(xoff), yd = gtodouble(yoff);

    PARI_get_plot(0);
    xi = pari_plot.width - 1;
    yi = pari_plot.height - 1;
    xi = DTOL(xd*xi);
    yi = DTOL(yd*yi);
  } else {
    xi = itos(xoff);
    yi = itos(yoff);
  }
  if (flag & ~RECT_CP_RELATIVE) {
    PariRect *s = check_rect_init(source), *d = check_rect_init(dest);

    switch (flag & ~RECT_CP_RELATIVE) {
      case RECT_CP_NW:
	break;
      case RECT_CP_SW:
	yi = RYsize(d) - RYsize(s) - yi;
	break;
      case RECT_CP_SE:
	yi = RYsize(d) - RYsize(s) - yi;
	/* FALL THROUGH */
      case RECT_CP_NE:
	xi = RXsize(d) - RXsize(s) - xi;
	break;
    }
  }
  rectcopy(source, dest, xi, yi);
}

void
rectcopy(long source, long dest, long xoff, long yoff)
{
  PariRect *s = check_rect_init(source), *d = check_rect_init(dest);
  RectObj *R = RHead(s);
  RectObj *tail = RTail(d);
  RectObj *next;
  int i;

  while (R)
  {
    switch(RoType(R))
    {
      case ROt_PT:
	next = (RectObj*) pari_malloc(sizeof(RectObj1P));
	memcpy(next,R,sizeof(RectObj1P));
	RoPTx(next) += xoff; RoPTy(next) += yoff;
	RoNext(tail) = next; tail = next;
	break;
      case ROt_LN: case ROt_BX:
	next = (RectObj*) pari_malloc(sizeof(RectObj2P));
	memcpy(next,R,sizeof(RectObj2P));
	RoLNx1(next) += xoff; RoLNy1(next) += yoff;
	RoLNx2(next) += xoff; RoLNy2(next) += yoff;
	RoNext(tail) = next; tail = next;
	break;
      case ROt_MP: case ROt_ML:
	next = (RectObj*) pari_malloc(sizeof(RectObjMP));
	memcpy(next,R,sizeof(RectObjMP));
	RoMPxs(next) = (double*) pari_malloc(sizeof(double)*RoMPcnt(next));
	RoMPys(next) = (double*) pari_malloc(sizeof(double)*RoMPcnt(next));
	memcpy(RoMPxs(next),RoMPxs(R),sizeof(double)*RoMPcnt(next));
	memcpy(RoMPys(next),RoMPys(R),sizeof(double)*RoMPcnt(next));
	for (i=0; i<RoMPcnt(next); i++)
	{
	  RoMPxs(next)[i] += xoff; RoMPys(next)[i] += yoff;
	 }
	RoNext(tail) = next; tail = next;
	break;
      case ROt_ST:
	next = (RectObj*) pari_malloc(sizeof(RectObjST));
	memcpy(next,R,sizeof(RectObjMP));
	RoSTs(next) = (char*) pari_malloc(RoSTl(R)+1);
	memcpy(RoSTs(next),RoSTs(R),RoSTl(R)+1);
	RoSTx(next) += xoff; RoSTy(next) += yoff;
	RoNext(tail) = next; tail = next;
	break;
      case ROt_PTT: case ROt_LNT: case ROt_PTS:
	next = (RectObj*) pari_malloc(sizeof(RectObjPN));
	memcpy(next,R,sizeof(RectObjPN));
	RoNext(tail) = next; tail = next;
	break;
    }
    R=RoNext(R);
  }
  RoNext(tail) = NULL; RTail(d) = tail;
}

enum {CLIPLINE_NONEMPTY = 1, CLIPLINE_CLIP_1 = 2, CLIPLINE_CLIP_2 = 4};
/* A simpler way is to clip by 4 half-planes */
static int
clipline(double xmin, double xmax, double ymin, double ymax,
	 double *x1p, double *y1p, double *x2p, double *y2p)
{
  int xy_exch = 0, rc = CLIPLINE_NONEMPTY;
  double t, sl;
  double xi, xmn, xmx;
  double yi, ymn, ymx;
  int x1_is_ymn, x1_is_xmn;
  double x1 = *x1p, x2 = *x2p, y1 = *y1p, y2 = *y2p;

  if ((x1 < xmin &&  x2 < xmin) || (x1 > xmax && x2 > xmax))
    return 0;
  if (fabs(x1 - x2) < fabs(y1 - y2)) { /* Exchange x and y */
    xy_exch = 1;
    dswap(xmin, ymin); dswap(x1, y1);
    dswap(xmax, ymax); dswap(x2, y2);
  }

  /* Build y as a function of x */
  xi = x1;
  yi = y1;
  sl = x1==x2? 0: (y2 - yi)/(x2 - xi);

  if (x1 > x2) {
    x1_is_xmn = 0;
    xmn = x2;
    xmx = x1;
  } else {
    x1_is_xmn = 1;
    xmn = x1;
    xmx = x2;
  }

  if (xmn < xmin) {
    xmn = xmin;
    rc |= x1_is_xmn? CLIPLINE_CLIP_1: CLIPLINE_CLIP_2;
  }
  if (xmx > xmax) {
    xmx = xmax;
    rc |= x1_is_xmn? CLIPLINE_CLIP_2: CLIPLINE_CLIP_1;
  }
  if (xmn > xmx) return 0;

  ymn = yi + (xmn - xi)*sl;
  ymx = yi + (xmx - xi)*sl;

  if (sl < 0) t = ymn, ymn = ymx, ymx = t;
  if (ymn > ymax || ymx < ymin) return 0;

  if (rc & CLIPLINE_CLIP_1) x1 = x1_is_xmn? xmn: xmx;
  if (rc & CLIPLINE_CLIP_2) x2 = x1_is_xmn? xmx: xmn;

  /* Now we know there is an intersection, need to move x1 and x2 */
  x1_is_ymn = ((sl >= 0) == (x1 < x2));
  if (ymn < ymin) {
    double x = (ymin - yi)/sl + xi; /* slope != 0  ! */
    if (x1_is_ymn) x1 = x, rc |= CLIPLINE_CLIP_1;
    else           x2 = x, rc |= CLIPLINE_CLIP_2;
  }
  if (ymx > ymax) {
    double x = (ymax - yi)/sl + xi; /* slope != 0  ! */
    if (x1_is_ymn) x2 = x, rc |= CLIPLINE_CLIP_2;
    else           x1 = x, rc |= CLIPLINE_CLIP_1;
  }
  if (rc & CLIPLINE_CLIP_1) y1 = yi + (x1 - xi)*sl;
  if (rc & CLIPLINE_CLIP_2) y2 = yi + (x2 - xi)*sl;
  if (xy_exch) /* Exchange x and y */
    *x1p = y1, *x2p = y2, *y1p = x1, *y2p = x2;
  else
    *x1p = x1, *x2p = x2, *y1p = y1, *y2p = y2;
  return rc;
}

void
rectclip(long rect)
{
  PariRect *s = check_rect_init(rect);
  RectObj *next, *R = RHead(s), **prevp = &RHead(s);
  double xmin = 0, xmax = RXsize(s);
  double ymin = 0, ymax = RYsize(s);

  for (; R; R = next) {
    int did_clip = 0;
#define REMOVE() { *prevp = next; freeobj(R); break; }
#define NEXT() { prevp = &RoNext(R); break; }

    next = RoNext(R);
    switch(RoType(R)) {
      case ROt_PT:
	if ( DTOL(RoPTx(R)) < xmin || DTOL(RoPTx(R)) > xmax
	  || DTOL(RoPTy(R)) < ymin || DTOL(RoPTy(R)) > ymax) REMOVE();
	NEXT();
      case ROt_BX:
	if (RoLNx1(R) < xmin) RoLNx1(R) = xmin, did_clip = 1;
	if (RoLNx2(R) < xmin) RoLNx2(R) = xmin, did_clip = 1;
	if (RoLNy1(R) < ymin) RoLNy1(R) = ymin, did_clip = 1;
	if (RoLNy2(R) < ymin) RoLNy2(R) = ymin, did_clip = 1;
	if (RoLNx1(R) > xmax) RoLNx1(R) = xmax, did_clip = 1;
	if (RoLNx2(R) > xmax) RoLNx2(R) = xmax, did_clip = 1;
	if (RoLNy1(R) > ymax) RoLNy1(R) = ymax, did_clip = 1;
	if (RoLNy2(R) > ymax) RoLNy2(R) = ymax, did_clip = 1;
	/* Remove zero-size clipped boxes */
	if (did_clip && RoLNx1(R) == RoLNx2(R)
		     && RoLNy1(R) == RoLNy2(R)) REMOVE();
	NEXT();
      case ROt_LN:
	if (!clipline(xmin, xmax, ymin, ymax,
		      &RoLNx1(R), &RoLNy1(R),
		      &RoLNx2(R), &RoLNy2(R))) REMOVE();
	NEXT();
      case ROt_MP: {
	int c = RoMPcnt(R), f = 0, t = 0;

	while (f < c) {
	  if ( DTOL(RoMPxs(R)[f]) >= xmin && DTOL(RoMPxs(R)[f]) <= xmax
	    && DTOL(RoMPys(R)[f]) >= ymin && DTOL(RoMPys(R)[f]) <= ymax) {
	    if (t != f) {
	      RoMPxs(R)[t] = RoMPxs(R)[f];
	      RoMPys(R)[t] = RoMPys(R)[f];
	    }
	    t++;
	  }
	  f++;
	}
	if (t == 0) REMOVE();
	RoMPcnt(R) = t;
	NEXT();
      }
      case ROt_ML: {
	/* Hard case. Break a multiline into several pieces
	 * if some part is clipped. */
	int c = RoMPcnt(R) - 1;
	int f = 0, t = 0, had_lines = 0, had_hole = 0, rc;
	double ox = RoMLxs(R)[0], oy = RoMLys(R)[0], oxn, oyn;

	while (f < c) {
	/* Endpoint of this segment is startpoint of next one: need to
	 * preserve it if it is clipped. */
	  oxn = RoMLxs(R)[f+1];
	  oyn = RoMLys(R)[f+1];
	  rc = clipline(xmin, xmax, ymin, ymax,
		  &ox, &oy, /* &RoMLxs(R)[f], &RoMLys(R)[f], */
		  &RoMLxs(R)[f+1], &RoMLys(R)[f+1]);
	  RoMLxs(R)[f] = ox; ox = oxn;
	  RoMLys(R)[f] = oy; oy = oyn;
	  if (!rc) {
	    if (had_lines) had_hole = 1;
	    f++; continue;
	  }

	  if (!had_lines || (!(rc & CLIPLINE_CLIP_1) && !had_hole) ) {
	    /* Continuous */
	    had_lines = 1;
	    if (t != f) {
	      if (t == 0) {
		RoMPxs(R)[t] = RoMPxs(R)[f];
		RoMPys(R)[t] = RoMPys(R)[f];
	      }
	      RoMPxs(R)[t+1] = RoMPxs(R)[f+1];
	      RoMPys(R)[t+1] = RoMPys(R)[f+1];
	    }
	    t++;
	    f++;
	    if (rc & CLIPLINE_CLIP_2) had_hole = 1, RoMLcnt(R) = t+1;
	    continue;
	  }
	  /* Is not continuous, automatically R is not pari_free()ed.  */
	  t++;
	  RoMLcnt(R) = t;
	  if (rc & CLIPLINE_CLIP_2) { /* Needs separate entry */
	    RectObj *n = (RectObj*) pari_malloc(sizeof(RectObj2P));

	    RoType(n) = ROt_LN;
	    RoCol(n) = RoCol(R);
	    RoLNx1(n) = RoMLxs(R)[f];	RoLNy1(n) = RoMLys(R)[f];
	    RoLNx2(n) = RoMLxs(R)[f+1];	RoLNy2(n) = RoMLys(R)[f+1];
	    RoNext(n) = next;
	    RoNext(R) = n;
	    /* Restore the unclipped value: */
	    RoMLxs(R)[f+1] = oxn;	RoMLys(R)[f+1] = oyn;
	    f++;
	    prevp = &RoNext(n);
	  }
	  if (f + 1 < c) {		/* Are other lines */
	    RectObj *n = (RectObj*) pari_malloc(sizeof(RectObjMP));
	    RoType(n) = ROt_ML;
	    RoCol(n) = RoCol(R);
	    RoMLcnt(n) = c - f;
	    RoMLxs(n) = (double*) pari_malloc(sizeof(double)*(c - f));
	    RoMLys(n) = (double*) pari_malloc(sizeof(double)*(c - f));
	    memcpy(RoMPxs(n),RoMPxs(R) + f, sizeof(double)*(c - f));
	    memcpy(RoMPys(n),RoMPys(R) + f, sizeof(double)*(c - f));
	    RoMPxs(n)[0] = oxn;
	    RoMPys(n)[0] = oyn;
	    RoNext(n) = next;
	    RoNext(R) = n;
	    next = n;
	  }
	  break;
	}
	if (t == 0) REMOVE();
	NEXT();
      }
    }
#undef REMOVE
#undef NEXT
  }
}

/********************************************************************/
/**                                                                **/
/**                        HI-RES PLOT                             **/
/**                                                                **/
/********************************************************************/
void
Printx(dblPointList *f)
{
  long i;
  printf("x: [%0.5g,%0.5g], y: [%0.5g,%0.5g]\n",
         f->xsml, f->xbig, f->ysml, f->ybig);
  for (i = 0; i < f->nb; i++) printf("%0.5g ", f->d[i]);
  printf("\n");
}

static void
Appendx(dblPointList *f, dblPointList *l,double x)
{
  (l->d)[l->nb++]=x;
  if (x < f->xsml) f->xsml=x;
  else if (x > f->xbig) f->xbig=x;
}

static void
Appendy(dblPointList *f, dblPointList *l,double y)
{
  (l->d)[l->nb++]=y;
  if (y < f->ysml) f->ysml=y;
  else if (y > f->ybig) f->ybig=y;
}

/* Convert data from GEN to double before we call rectplothrawin */
static dblPointList*
gtodblList(GEN data, long flags)
{
  dblPointList *l;
  double xsml,xbig,ysml,ybig;
  long tx=typ(data), ty, nl=lg(data)-1, lx1,lx;
  register long i,j,u,v;
  long param=(flags & (PLOT_PARAMETRIC|PLOT_COMPLEX));
  long cplx=(flags & PLOT_COMPLEX);
  GEN x,y;

  if (! is_vec_t(tx)) pari_err(typeer,"gtodblList");
  if (!nl) return NULL;
  lx1 = lg(data[1]);

  if (nl == 1 && !cplx) pari_err(talker,"single vector in gtodblList");
  /* Allocate memory, then convert coord. to double */
  l = (dblPointList*) pari_malloc((cplx ? 2*nl:nl)*sizeof(dblPointList));
  for (i=0; i<nl-1; i+=2)
  {
    u = i+1;
    x = gel(data,u);   tx = typ(x); lx = lg(x);
    if (cplx)
    {
      if (!is_vec_t(tx)) pari_err(typeer,"gtodblList");
      y=NULL;
    }
    else
    {
      y = gel(data,u+1); ty = typ(y);
      if (!is_vec_t(tx) || !is_vec_t(ty) || lg(y) != lx
	  || (!param && lx != lx1)) pari_err(typeer,"gtodblList");
    }

    lx--;
    l[i].d = (double*) pari_malloc(lx*sizeof(double));
    l[u].d = (double*) pari_malloc(lx*sizeof(double));
    for (j=0; j<lx; j=v)
    {
      v = j+1;
      if (cplx)
      {
	GEN z = gel(x,v);
	l[i].d[j] = gtodouble(greal(z));
	l[u].d[j] = gtodouble(gimag(z));
      }
      else
      {
	l[i].d[j] = gtodouble(gel(x,v));
	l[u].d[j] = gtodouble(gel(y,v));
      }
    }
    l[i].nb = l[u].nb = lx;
  }

  /* Now compute extremas */
  if (param)
  {
    l[0].nb = nl/2;
    for (i=0; i < l[0].nb; i+=2)
      if (l[i+1].nb) break;
    if (i >= l[0].nb) { pari_free(l); return NULL; }
    xsml = xbig = l[i  ].d[0];
    ysml = ybig = l[i+1].d[0];

    for (i=0; i < l[0].nb; i+=2)
    {
      u = i+1;
      for (j=0; j < l[u].nb; j++)
      {
	if      (l[i].d[j] < xsml) xsml = l[i].d[j];
	else if (l[i].d[j] > xbig) xbig = l[i].d[j];

	if      (l[u].d[j] < ysml) ysml = l[u].d[j];
	else if (l[u].d[j] > ybig) ybig = l[u].d[j];
      }
    }
  }
  else
  {
    if (!l[0].nb) { pari_free(l); return NULL; }
    l[0].nb = nl-1;

    xsml = xbig = l[0].d[0];
    ysml = ybig = l[1].d[0];

    for (j=0; j < l[1].nb; j++)
    {
      if      (l[0].d[j] < xsml) xsml = l[0].d[j];
      else if (l[0].d[j] > xbig) xbig = l[0].d[j];
    }
    for (i=1; i <= l[0].nb; i++)
      for (j=0; j < l[i].nb; j++)
      {
	if      (l[i].d[j] < ysml) ysml = l[i].d[j];
	else if (l[i].d[j] > ybig) ybig = l[i].d[j];
      }
  }
  l[0].xsml = xsml; l[0].xbig = xbig;
  l[0].ysml = ysml; l[0].ybig = ybig;
  return l;
}

static void
single_recursion(dblPointList *pl,GEN code,GEN xleft,double yleft,
  GEN xright,double yright,long depth)
{
  GEN xx;
  pari_sp av = avma;
  double yy, dy=pl[0].ybig - pl[0].ysml;

  if (depth==RECUR_MAXDEPTH) return;

  xx = addrr(xleft,xright); setexpo(xx, expo(xx)-1);
  yy = gtodouble(READ_EXPR(code,xx));

  if (dy && fabs(yleft+yright-2*yy)< dy*RECUR_PREC) return;
  single_recursion(pl,code, xleft,yleft, xx,yy, depth+1);

  Appendx(&pl[0],&pl[0],rtodbl(xx));
  Appendy(&pl[0],&pl[1],yy);

  single_recursion(pl,code, xx,yy, xright,yright, depth+1);
  avma = av;
}

static void
param_recursion(dblPointList *pl,GEN code,GEN tleft,double xleft,
  double yleft, GEN tright,double xright,double yright, long depth)
{
  GEN tt, p1;
  pari_sp av=avma;
  double xx, dy=pl[0].ybig - pl[0].ysml;
  double yy, dx=pl[0].xbig - pl[0].xsml;

  if (depth==PARAMR_MAXDEPTH) return;

  tt = addrr(tleft,tright); setexpo(tt, expo(tt)-1);
  p1 = READ_EXPR(code,tt);
  if (typ(p1)==t_VEC)
  {
    if (lg(p1) == 2)
    { /* cplx */
      p1 = gel(p1,1);
      xx = gtodouble(real_i(p1));
      yy = gtodouble(imag_i(p1));
    }
    else
    {
      xx = gtodouble(gel(p1,1));
      yy = gtodouble(gel(p1,2));
    }
  }
  else
  {
    xx = gtodouble(gel(p1,1));
    yy = gtodouble(gel(p1,2));
  }

  if (dx && dy && fabs(xleft+xright-2*xx) < dx*RECUR_PREC
	       && fabs(yleft+yright-2*yy) < dy*RECUR_PREC) return;
  param_recursion(pl,code, tleft,xleft,yleft, tt,xx,yy, depth+1);

  Appendx(&pl[0],&pl[0],xx);
  Appendy(&pl[0],&pl[1],yy);

  param_recursion(pl,code, tt,xx,yy, tright,xright,yright, depth+1);
  avma = av;
}

/*  Pure graphing. If testpoints is 0, it is set to the default.
 *  Returns a dblPointList of (absolute) coordinates. */
static dblPointList *
rectplothin(GEN a, GEN b, GEN code, long prec, ulong flags,
	    long testpoints)
{
  long single_c;
  long param=flags & (PLOT_PARAMETRIC|PLOT_COMPLEX);
  long recur=flags & PLOT_RECURSIVE;
  long cplx=flags & PLOT_COMPLEX;
  GEN t,dx,x;
  dblPointList *pl;
  long tx, i, j, sig, nc, nl, nbpoints;
  pari_sp av = avma, av2;
  double xsml,xbig,ysml,ybig,fx,fy;

  if (!testpoints)
  {
    if (recur) testpoints = RECUR_NUMPOINTS;
    else       testpoints = param? PARAM_NUMPOINTS : PLOTH_NUMPOINTS;
  }
  if (recur)
    nbpoints = testpoints << (param? PARAMR_MAXDEPTH : RECUR_MAXDEPTH);
  else
    nbpoints = testpoints;

  sig = gcmp(b,a); if (!sig) return 0;
  if (sig<0) swap(a, b);
  dx = divru(gtofp(gsub(b,a),prec), testpoints-1);

  x = gtofp(a, prec);
  if (typ(code) == t_CLOSURE) push_lex(x);
  av2=avma; t=READ_EXPR(code,x); tx=typ(t);
  if (!is_matvec_t(tx) && !cplx)
  {
    xsml = gtodouble(a);
    xbig = gtodouble(b);
    ysml = ybig = gtodouble(t);
    nc=1; nl=2; /* nc = nb of curves; nl = nb of coord. lists */
    if (param) pari_warn(warner,"flag PLOT_PARAMETRIC ignored");
    single_c=1; param=0;
  }
  else
  {
    if (tx != t_VEC) {
      if (!cplx) pari_err(talker,"not a row vector in ploth");
      nc = nl = 1;
    } else {
      nl = lg(t)-1;
      if (!nl) { avma=av; return 0; }
      if (param && !cplx) nc=nl/2; else { nc=nl; if (!cplx) nl++; }
    }
    if (recur && nc > 1) pari_err(talker,"multi-curves cannot be plot recursively");
    single_c=0;

    if (param)
    {
      if (cplx)
      {
	GEN z = (typ(t) == t_VEC)? gel(t,1): t;
	xbig = xsml = gtodouble(real_i(z));
	ybig = ysml = gtodouble(imag_i(z));
      }
      else
      {
	xbig = xsml = gtodouble(gel(t,1));
	ybig = ysml = gtodouble(gel(t,2));
      }
      for (i=2+!cplx; i<=nl; i++)
      {
	if (cplx)
	{
	  GEN z = gel(t,i);
	  fx = gtodouble(real_i(z));
	  fy = gtodouble(imag_i(z));
	}
	else
	{
	  fx = gtodouble(gel(t,i)); i++;
	  fy = gtodouble(gel(t,i));
	}
	if (xsml>fx) xsml=fx; else if (xbig<fx) xbig=fx;
	if (ysml>fy) ysml=fy; else if (ybig<fy) ybig=fy;
      }
    }
    else
    {
      xsml = gtodouble(a); ysml = gtodouble(vecmin(t));
      xbig = gtodouble(b); ybig = gtodouble(vecmax(t));
    }
  }

  pl=(dblPointList*) pari_malloc((cplx?2*nl:nl)*sizeof(dblPointList));
  for (i = 0; i < nl; i++)
  {
    pl[i].d = (double*) pari_malloc((nbpoints+1)*sizeof(double));
    pl[i].nb=0;
    if (cplx)
    {
      pl[i+nl].d = (double*) pari_malloc((nbpoints+1)*sizeof(double));
      pl[i+nl].nb=0;
    }
  }
  pl[0].xsml=xsml; pl[0].ysml=ysml; pl[0].xbig=xbig; pl[0].ybig=ybig;

  if (recur) /* recursive plot */
  {
    double yleft, yright = 0;
    if (param)
    {
      GEN tleft = cgetr(prec), tright = cgetr(prec);
      double xleft, xright = 0;
      av2 = avma;
      affgr(a,tleft); t=READ_EXPR(code,tleft);
      if (cplx)
      {
	if (typ(t)==t_VEC) t = gel(t, 1);
	xleft = gtodouble(real_i(t));
	yleft = gtodouble(imag_i(t));
      }
      else
      {
	xleft = gtodouble(gel(t,1));
	yleft = gtodouble(gel(t,2));
      }
      for (i=0; i<testpoints-1; i++)
      {
	if (i) { affrr(tright,tleft); xleft = xright; yleft = yright; }
	addrrz(tleft,dx,tright);
	t = READ_EXPR(code,tright);
	if (cplx)
	{
	  if (typ(t) == t_VEC)
	  {
	    if (lg(t) != 2) pari_err(talker,"inconsistent data in rectplothin");
	    t = gel(t, 1);
	  }
	  switch(typ(t)) {
	    case t_INT: case t_REAL: case t_FRAC:
              xright = gtodouble(t);
              yright = 0.; break;
            case t_COMPLEX:
              xright = gtodouble(gel(t,1));
              yright = gtodouble(gel(t,2)); break;
	    default: pari_err(talker,"inconsistent data in rectplothin");
	  }
	}
	else
	{
	  if (lg(t) != 3) pari_err(talker,"inconsistent data in rectplothin");
	  xright = gtodouble(gel(t,1));
	  yright = gtodouble(gel(t,2));
	}

	Appendx(&pl[0],&pl[0],xleft);
	Appendy(&pl[0],&pl[1],yleft);

	param_recursion(pl,code, tleft,xleft,yleft, tright,xright,yright, 0);
	avma = av2;
      }
      Appendx(&pl[0],&pl[0],xright);
      Appendy(&pl[0],&pl[1],yright);
    }
    else /* single_c */
    {
      GEN xleft = cgetr(prec), xright = cgetr(prec);
      av2 = avma;
      affgr(a,xleft);
      yleft = gtodouble(READ_EXPR(code,xleft));
      for (i=0; i<testpoints-1; i++)
      {
	addrrz(xleft,dx,xright);
	yright = gtodouble(READ_EXPR(code,xright));

	Appendx(&pl[0],&pl[0],rtodbl(xleft));
	Appendy(&pl[0],&pl[1],yleft);

	single_recursion(pl,code,xleft,yleft,xright,yright,0);
	avma = av2;
	affrr(xright,xleft); yleft = yright;
      }
      Appendx(&pl[0],&pl[0],rtodbl(xright));
      Appendy(&pl[0],&pl[1],yright);
    }
  }
  else /* non-recursive plot */
  {
    if (single_c)
      for (i=0; i<testpoints; i++, affrr(addrr(x,dx), x), avma = av2)
      {
	t = READ_EXPR(code,x);
	pl[0].d[i] = gtodouble(x);
	Appendy(&pl[0],&pl[1], gtodouble(t));
      }
    else if (param)
    {
      for (i=0; i<testpoints; i++, affrr(addrr(x,dx), x), avma = av2)
      {
        long k;
	t = READ_EXPR(code,x);
	if (typ(t) != t_VEC)
	{ /* cplx */
	  switch(typ(t)) {
	    case t_INT:	case t_REAL: case t_FRAC:
              Appendx(&pl[0], &pl[0], gtodouble(t));
              Appendy(&pl[0], &pl[1], 0.);
              continue;

            case t_COMPLEX:
              Appendx(&pl[0], &pl[0], gtodouble(gel(t,1)));
              Appendy(&pl[0], &pl[1], gtodouble(gel(t,2)));
              continue;
	  }
          pari_err(talker,"inconsistent data in rectplothin");
          return NULL; /* not reached */
	}
        if (lg(t)!=nl+1) pari_err(talker,"inconsistent data in rectplothin");
	k = 0;
        if (cplx)
          for (j=1; j<=nl; j++)
          {
            GEN z = gel(t,j);
            Appendx(&pl[0], &pl[k++], gtodouble(real_i(z)));
            Appendy(&pl[0], &pl[k++], gtodouble(imag_i(z)));
          }
        else
          for (j=1; j<=nl; j++)
          {
            Appendx(&pl[0], &pl[k++], gtodouble(gel(t,j))); j++;
            Appendy(&pl[0], &pl[k++], gtodouble(gel(t,j)));
          }
      }
    }
    else /* plothmult */
      for (i=0; i<testpoints; i++, affrr(addrr(x,dx), x), avma = av2)
      {
	t = READ_EXPR(code,x);
	if (lg(t) != nl) pari_err(talker,"inconsistent data in rectplothin");
	pl[0].d[i] = gtodouble(x);
	for (j=1; j<nl; j++) Appendy(&pl[0],&pl[j], gtodouble(gel(t,j)));
      }
  }
  pl[0].nb = nc;
  if (typ(code) == t_CLOSURE) pop_lex();
  avma = av; return pl;
}

/* Uses highlevel plotting functions to implement splines as
   a low-level plotting function. */
static void
rectsplines(long ne, double *x, double *y, long lx, long flag)
{
  long i, j;
  pari_sp av0 = avma;
  GEN X = pol_x(0), xa = cgetg(lx+1, t_VEC), ya = cgetg(lx+1, t_VEC);
  GEN tas, pol3;
  long param = flag & PLOT_PARAMETRIC;

  if (lx < 4) pari_err(talker, "Too few points (%ld) for spline plot", lx);
  for (i = 1; i <= lx; i++) {
    gel(xa,i) = dbltor(x[i-1]);
    gel(ya,i) = dbltor(y[i-1]);
  }
  if (param) {
    tas = new_chunk(4);
    for (j = 1; j <= 4; j++) gel(tas,j-1) = utoipos(j);
    pol3 = cgetg(3, t_VEC);
  }
  else
    tas = pol3 = NULL; /* gcc -Wall */
  for (i = 0; i <= lx - 4; i++) {
    pari_sp av = avma;

    xa++; ya++;
    if (param) {
      gel(pol3,1) = polint_i(tas, xa, X, 4, NULL);
      gel(pol3,2) = polint_i(tas, ya, X, 4, NULL);
    } else {
      pol3 = polint_i(xa, ya, X, 4, NULL);
      tas = xa;
    }
    /* Start with 3 points */
    rectploth(ne, i==   0 ? gel(tas,0) : gel(tas,1),
	          i==lx-4 ? gel(tas,3) : gel(tas,2), pol3,
                  DEFAULTPREC, PLOT_RECURSIVE | PLOT_NO_RESCALE
                  | PLOT_NO_FRAME | PLOT_NO_AXE_Y | PLOT_NO_AXE_X | param, 2);
    avma = av;
  }
  avma = av0;
}

/* Plot a dblPointList. Complete with axes, bounding box, etc.
 * We use two drawing rectangles: one for strings, another for graphs.
 *
 * data is an array of structs. Its meaning depends on flags :
 *
 * + data[0] contains global extremas, the number of curves to plot
 *   (data[0].nb) and a list of doubles (first set of x-coordinates).
 *
 * + data[i].nb (i>0) contains the number of points in the list
 *   data[i].d (hopefully, data[2i].nb=data[2i+1].nb when i>0...)
 *
 * + If flags contain PLOT_PARAMETRIC, the array length should be
 *   even, and successive pairs (data[2i].d, data[2i+1].d) represent
 *   curves to plot.
 *
 * + If there is no such flag, the first element is an array with
 *   x-coordinates and the following ones contain y-coordinates.
 *
 * Additional flags: PLOT_NO_AXE_X, PLOT_NO_AXE_Y, PLOT_NO_FRAME. */
static GEN
rectplothrawin(long stringrect, long drawrect, dblPointList *data,
	       long flags, PARI_plot *WW)
{
  GEN res;
  dblPointList y,x;
  double xsml,xbig,ysml,ybig,tmp;
  long ltype, max_graphcolors;
  long param = flags & (PLOT_PARAMETRIC|PLOT_COMPLEX);
  pari_sp ltop = avma;
  long i,nc,nbpoints, w[2], wx[2], wy[2];

  if (!data) return cgetg(1,t_VEC);

  w[0] = stringrect;
  w[1] = drawrect;
  x = data[0]; nc = x.nb;
  xsml = x.xsml; xbig = x.xbig;
  ysml = x.ysml; ybig = x.ybig;
  if (xbig-xsml < 1.e-9)
  {
    tmp=fabs(xsml)/10; if (!tmp) tmp=0.1;
    xbig+=tmp; xsml-=tmp;
  }
  if (ybig-ysml < 1.e-9)
  {
    tmp=fabs(ysml)/10; if (!tmp) tmp=0.1;
    ybig+=tmp; ysml-=tmp;
  }

  if (WW)
  { /* no rectwindow supplied ==> ps or screen output */
    char c1[16],c2[16],c3[16],c4[16];
    PARI_plot W = *WW;
    long lm = W.fwidth*10; /* left margin   */
    long rm = W.hunit-1; /* right margin  */
    long tm = W.vunit-1; /* top margin    */
    long bm = W.vunit+W.fheight-1; /* bottom margin */
    long is = W.width - (lm+rm);
    long js = W.height - (tm+bm);

    wx[0]=wy[0]=0; wx[1]=lm; wy[1]=tm;
   /* Window size (W.width x W.height) is given in pixels, and
    * correct pixels are 0..W.width-1.
    * On the other hand, rect functions work with windows whose pixel
    * range is [0,width]. */
    initrect(stringrect, W.width-1, W.height-1);
    if (drawrect != stringrect) initrect(drawrect, is-1, js-1);

    /* draw labels on stringrect */
    sprintf(c1,"%.5g",ybig); sprintf(c2,"%.5g",ysml);
    sprintf(c3,"%.5g",xsml); sprintf(c4,"%.5g",xbig);

    rectlinetype(stringrect,-2); /* Frame */
    current_color[(ulong)stringrect] = DEFAULT_COLOR;
    put_string(stringrect, lm, 0, c1,
		RoSTdirRIGHT | RoSTdirHGAP | RoSTdirTOP);
    put_string(stringrect, lm, W.height - bm, c2,
		RoSTdirRIGHT | RoSTdirHGAP | RoSTdirVGAP);
    put_string(stringrect, lm, W.height - bm, c3,
		RoSTdirLEFT | RoSTdirTOP);
    put_string(stringrect, W.width - rm - 1, W.height - bm, c4,
		RoSTdirRIGHT | RoSTdirTOP);
  }
  RHasGraph(check_rect(drawrect)) = 1;

  if (!(flags & PLOT_NO_RESCALE))
    rectscale0(drawrect, xsml, xbig, ysml, ybig);

  if (!(flags & PLOT_NO_FRAME))
  {
    int do_double = (flags & PLOT_NODOUBLETICK) ? TICKS_NODOUBLE : 0;
    PARI_plot *pl = WW;
    if (!pl) { PARI_get_plot(0); pl = &pari_plot; }

    rectlinetype(drawrect, -2); /* Frame. */
    current_color[drawrect] = DEFAULT_COLOR;
    rectmove0(drawrect,xsml,ysml,0);
    rectbox0(drawrect,xbig,ybig,0);
    if (!(flags & PLOT_NO_TICK_X)) {
      rectticks(pl, drawrect, xsml, ysml, xbig, ysml, xsml, xbig,
	TICKS_CLOCKW | do_double);
      rectticks(pl, drawrect, xbig, ybig, xsml, ybig, xbig, xsml,
	TICKS_CLOCKW | do_double);
    }
    if (!(flags & PLOT_NO_TICK_Y)) {
      rectticks(pl, drawrect, xbig, ysml, xbig, ybig, ysml, ybig,
	TICKS_CLOCKW | do_double);
      rectticks(pl, drawrect, xsml, ybig, xsml, ysml, ybig, ysml,
	TICKS_CLOCKW | do_double);
    }
  }

  if (!(flags & PLOT_NO_AXE_Y) && (xsml<=0 && xbig >=0))
  {
    rectlinetype(drawrect, -1); /* Axes. */
    current_color[drawrect] = AXIS_COLOR;
    rectmove0(drawrect,0.0,ysml,0);
    rectline0(drawrect,0.0,ybig,0);
  }

  if (!(flags & PLOT_NO_AXE_X) && (ysml<=0 && ybig >=0))
  {
    rectlinetype(drawrect, -1); /* Axes. */
    current_color[drawrect] = AXIS_COLOR;
    rectmove0(drawrect,xsml,0.0,0);
    rectline0(drawrect,xbig,0.0,0);
  }

  if (param) {
    i = 0;
    flags |= PLOT_PARAMETRIC;
    flags &= (~PLOT_COMPLEX); /* turn COMPLEX to PARAMETRIC*/
  } else i = 1;
  max_graphcolors = lg(pari_graphcolors)-1;
  for (ltype = 0; ltype < nc; ltype++)
  {
    current_color[drawrect] = pari_graphcolors[1+(ltype%max_graphcolors)];
    if (param) x = data[i++];

    y = data[i++]; nbpoints = y.nb;
    if (flags & (PLOT_POINTS_LINES|PLOT_POINTS)) {
      rectlinetype(drawrect, rectpoint_itype + ltype); /* Graphs */
      rectpointtype(drawrect,rectpoint_itype + ltype); /* Graphs */
      rectpoints0(drawrect,x.d,y.d,nbpoints);
      if (!(flags & PLOT_POINTS_LINES)) continue;
    }

    if (flags & PLOT_SPLINES) {
      /* rectsplines will call us back with ltype == 0 */
      int old = rectline_itype;

      rectline_itype = rectline_itype + ltype;
      rectsplines(drawrect,x.d,y.d,nbpoints,flags);
      rectline_itype = old;
    } else {
      rectlinetype(drawrect, rectline_itype + ltype); /* Graphs */
      rectlines0(drawrect,x.d,y.d,nbpoints,0);
    }
  }
  for (i--; i>=0; i--) pari_free(data[i].d);
  pari_free(data);

  if (WW)
  {
    if (flags & PLOT_POSTSCRIPT)
      postdraw0(w,wx,wy,2, 0);
    else
      rectdraw0(w,wx,wy,2);

    killrect(drawrect); if (stringrect != drawrect) killrect(stringrect);
  }

  avma=ltop;
  res = cgetg(5,t_VEC);
  gel(res,1) = dbltor(xsml); gel(res,2) = dbltor(xbig);
  gel(res,3) = dbltor(ysml); gel(res,4) = dbltor(ybig);
  return res;
}

/*************************************************************************/
/*                                                                       */
/*                          HI-RES FUNCTIONS                             */
/*                                                                       */
/*************************************************************************/

GEN
rectploth(long drawrect,GEN a,GEN b,GEN code,
	  long prec,ulong flags,long testpoints)
{
  dblPointList *pl=rectplothin(a,b, code, prec, flags,testpoints);
  return rectplothrawin(0,drawrect, pl, flags,NULL);
}

GEN
rectplothraw(long drawrect, GEN data, long flags)
{
  dblPointList *pl=gtodblList(data,flags);
  return rectplothrawin(0,drawrect,pl,flags,NULL);
}

static PARI_plot*
init_output(long flags)
{
  if (flags & PLOT_POSTSCRIPT)
    { PARI_get_psplot(); return &pari_psplot; }
  else
    { PARI_get_plot(0); return &pari_plot; }
}

static GEN
ploth0(GEN a,GEN b,GEN code, long prec,ulong flags,long testpoints)
{
  PARI_plot *output = init_output(flags);
  dblPointList *pl=rectplothin(a,b, code, prec, flags,testpoints);
  return rectplothrawin(STRINGRECT,DRAWRECT, pl, flags, output);
}

static GEN
plothraw0(GEN listx, GEN listy, long flags)
{
  PARI_plot *output = init_output(flags);
  long data[] = {evaltyp(t_VEC) | _evallg(3), 0, 0};
  dblPointList *pl;

  gel(data,1) = listx;
  gel(data,2) = listy;
  pl=gtodblList(data,PLOT_PARAMETRIC|(flags&PLOT_COMPLEX));
  if (!pl) return cgetg(1,t_VEC);
  return rectplothrawin(STRINGRECT,DRAWRECT,pl,flags | PLOT_PARAMETRIC,output);
}

GEN
plothraw(GEN listx, GEN listy, long flags)
{
  if (flags <= 1) flags = flags? 0: PLOT_POINTS;
  return plothraw0(listx, listy, flags);
}

GEN
ploth(GEN a, GEN b, GEN code, long prec,long flags,long numpoints)
{ return ploth0(a,b,code,prec,flags,numpoints); }
GEN
ploth2(GEN a, GEN b, GEN code, long prec)
{ return ploth0(a,b,code,prec,PLOT_PARAMETRIC,0); }
GEN
plothmult(GEN a, GEN b, GEN code, long prec)
{ return ploth0(a,b,code,prec,0,0); }

GEN
postplothraw(GEN listx, GEN listy, long flags)
{ return plothraw0(listx, listy, flags? PLOT_POSTSCRIPT
                                      : PLOT_POINTS|PLOT_POSTSCRIPT); }
GEN
postploth(GEN a, GEN b, GEN code, long prec,long flags, long numpoints)
{ return ploth0(a,b,code,prec,flags|PLOT_POSTSCRIPT, numpoints); }
GEN
postploth2(GEN a, GEN b, GEN code, long prec, long numpoints)
{ return ploth0(a,b,code,prec, PLOT_PARAMETRIC|PLOT_POSTSCRIPT,numpoints); }

GEN
plothsizes(void) { return plothsizes_flag(0); }
GEN
plothsizes_flag(long flag)
{
  GEN vect = cgetg(1+6,t_VEC);

  PARI_get_plot(0);
  gel(vect,1) = stoi(pari_plot.width);
  gel(vect,2) = stoi(pari_plot.height);
  if (flag) {
    gel(vect,3) = dbltor(pari_plot.hunit*1.0/pari_plot.width);
    gel(vect,4) = dbltor(pari_plot.vunit*1.0/pari_plot.height);
    gel(vect,5) = dbltor(pari_plot.fwidth*1.0/pari_plot.width);
    gel(vect,6) = dbltor(pari_plot.fheight*1.0/pari_plot.height);
  } else {
    gel(vect,3) = stoi(pari_plot.hunit);
    gel(vect,4) = stoi(pari_plot.vunit);
    gel(vect,5) = stoi(pari_plot.fwidth);
    gel(vect,6) = stoi(pari_plot.fheight);
  }
  return vect;
}

void
plot_count(long *w, long lw, col_counter rcolcnt)
{
  RectObj *O;
  long col, i;

  for (col = 1; col < lg(pari_colormap)-1; col++)
    for (i = 0; i < ROt_MAX; i++) rcolcnt[col][i] = 0;
  for (i = 0; i < lw; i++)
  {
    PariRect *e = rectgraph[w[i]];
    for (O = RHead(e); O; O=RoNext(O))
      switch(RoType(O))
      {
	case ROt_MP : rcolcnt[RoCol(O)][ROt_PT] += RoMPcnt(O);
		      break;                 /* Multiple Point */
	case ROt_PT :                        /* Point */
	case ROt_LN :                        /* Line */
	case ROt_BX :                        /* Box */
	case ROt_ML :                        /* Multiple lines */
	case ROt_ST : rcolcnt[RoCol(O)][RoType(O)]++;
		      break;                 /* String */
      }
  }
}
/*************************************************************************/
/*                                                                       */
/*                         POSTSCRIPT OUTPUT                             */
/*                                                                       */
/*************************************************************************/

static void
PARI_get_psplot(void)
{
  if (pari_psplot.init) return;
  pari_psplot.init = 1;

  pari_psplot.width = 1120 - 60; /* 1400 - 60 for hi-res */
  pari_psplot.height=  800 - 40; /* 1120 - 60 for hi-res */
  pari_psplot.fheight= 15;
  pari_psplot.fwidth = 6;
  pari_psplot.hunit = 5;
  pari_psplot.vunit = 5;
}

static void
gendraw(GEN list, long ps, long flag)
{
  long i,n,ne,*w,*x,*y;

  if (typ(list) != t_VEC) pari_err(talker,"not a vector in rectdraw");
  n = lg(list)-1; if (!n) return;
  if (n%3) pari_err(talker,"incorrect number of components in rectdraw");
  n = n/3;
  w = (long*)pari_malloc(n*sizeof(long));
  x = (long*)pari_malloc(n*sizeof(long));
  y = (long*)pari_malloc(n*sizeof(long));
  if (flag)
    PARI_get_plot(0);
  for (i=0; i<n; i++)
  {
    GEN win = gel(list,3*i+1), x0 = gel(list,3*i+2), y0 = gel(list,3*i+3);
    long xi, yi;
    if (typ(win)!=t_INT) pari_err(typeer,"rectdraw");
    if (flag) {
      xi = DTOL(gtodouble(x0)*(pari_plot.width - 1));
      yi = DTOL(gtodouble(y0)*(pari_plot.height - 1));
    } else {
      if (typ(x0)!=t_INT || typ(y0)!= t_INT) pari_err(typeer,"rectdraw");
      xi = itos(x0);
      yi = itos(y0);
    }
    x[i] = xi;
    y[i] = yi;
    ne = itos(win); check_rect(ne);
    w[i] = ne;
  }
  if (ps) postdraw0(w,x,y,n,flag); else rectdraw0(w,x,y,n);
  pari_free(x); pari_free(y); pari_free(w);
}

void
postdraw(GEN list) { gendraw(list, 1, 0); }

void
rectdraw(GEN list) { gendraw(list, 0, 0); }

void
postdraw_flag(GEN list, long flag) { gendraw(list, 1, flag); }

void
rectdraw_flag(GEN list, long flag) { gendraw(list, 0, flag); }

static void
ps_sc(void *data, long col) { (void)data; (void)col; }

static void
ps_point(void *data, long x, long y)
{
  fprintf((FILE*)data,"%ld %ld p\n",y,x);
}

static void
ps_line(void *data, long x1, long y1, long x2, long y2)
{
  fprintf((FILE*)data,"%ld %ld m %ld %ld l\n",y1,x1,y2,x2);
  fprintf((FILE*)data,"stroke\n");
}

static void
ps_rect(void *data, long x, long y, long w, long h)
{
  fprintf((FILE*)data,"%ld %ld m %ld %ld l %ld %ld l %ld %ld l closepath\n",y,x, y,x+w, y+h,x+w, y+h,x);
}

static void
ps_points(void *data, long nb, struct plot_points *p)
{
  long i;
  for (i=0; i<nb; i++) ps_point(data, p[i].x, p[i].y);
}

static void
ps_lines(void *data, long nb, struct plot_points *p)
{
  FILE *psfile = (FILE*)data;
  long i;
  fprintf(psfile,"%ld %ld m\n",p[0].y,p[0].x);
  for (i=1; i<nb; i++) fprintf(psfile, "%ld %ld l\n", p[i].y, p[i].x);
  fprintf(psfile,"stroke\n");
}

static void
ps_string(void *data, long x, long y, char *s, long length)
{
  FILE *psfile = (FILE*)data;
  (void)length;
  if (strpbrk(s, "(\\)")) {
    fprintf(psfile,"(");
    while (*s) {
      if ( *s=='(' || *s==')' || *s=='\\' ) fputc('\\', psfile);
      fputc(*s, psfile);
      s++;
    }
  } else
    fprintf(psfile,"(%s", s);
  fprintf(psfile,") %ld %ld m 90 rotate show -90 rotate\n", y, x);
}

void
postdraw0(long *w, long *x, long *y, long lw, long scale)
{
  struct plot_eng plot;
  FILE *psfile;
  double xscale = 0.65, yscale = 0.65;
  long fontsize = 16;

  PARI_get_psplot();
  if (scale) {
    double psxscale, psyscale;

    PARI_get_plot(0);
    psxscale = pari_psplot.width * 1.0/pari_plot.width ;
    psyscale = pari_psplot.height* 1.0/pari_plot.height;
    fontsize = (long) (fontsize/psxscale);
    xscale *= psxscale;
    yscale *= psyscale;
  }
  psfile = fopen(current_psfile, "a");
  if (!psfile)
    pari_err(openfiler,"postscript",current_psfile);

  /* Definitions taken from post terminal of Gnuplot. */
  fprintf(psfile,"%%!\n\
50 50 translate\n\
/p {moveto 0 2 rlineto 2 0 rlineto 0 -2 rlineto closepath fill} def\n\
/l {lineto} def\n\
/m {moveto} def\n\
/Times-Roman findfont %ld scalefont setfont\n\
%g %g scale\n", fontsize, yscale, xscale);

  plot.sc = &ps_sc;
  plot.pt = &ps_point;
  plot.ln = &ps_line;
  plot.bx = &ps_rect;
  plot.mp = &ps_points;
  plot.ml = &ps_lines;
  plot.st = &ps_string;
  plot.pl = &pari_psplot;

  gen_rectdraw0(&plot, (void*)psfile, w, x, y, lw, 1, 1);
  fprintf(psfile,"stroke showpage\n"); fclose(psfile);
}

void
gen_rectdraw0(struct plot_eng *eng, void *data, long *w, long *x, long *y, long lw, double xs, double ys)
{
  long i, j;
  long hgapsize = eng->pl->hunit, fheight = eng->pl->fheight;
  long vgapsize = eng->pl->vunit,  fwidth = eng->pl->fwidth;
  for(i=0; i<lw; i++)
  {
    PariRect *e = rectgraph[w[i]];
    RectObj *R;
    long x0 = x[i], y0 = y[i];
    for (R = RHead(e); R; R = RoNext(R))
    {
      switch(RoType(R))
      {
      case ROt_PT:
	eng->sc(data,RoCol(R));
	eng->pt(data, DTOL((RoPTx(R)+x0)*xs), DTOL((RoPTy(R)+y0)*ys));
	break;
      case ROt_LN:
	eng->sc(data,RoCol(R));
	eng->ln(data, DTOL((RoLNx1(R)+x0)*xs),
		      DTOL((RoLNy1(R)+y0)*ys),
		      DTOL((RoLNx2(R)+x0)*xs),
		      DTOL((RoLNy2(R)+y0)*ys));
	break;
      case ROt_BX:
	eng->sc(data,RoCol(R));
	eng->bx(data,
		DTOL((RoBXx1(R)+x0)*xs),
		DTOL((RoBXy1(R)+y0)*ys),
		DTOL((RoBXx2(R)-RoBXx1(R))*xs),
		DTOL((RoBXy2(R)-RoBXy1(R))*ys));
	break;
      case ROt_MP:
	{
	  double *ptx = RoMPxs(R);
	  double *pty = RoMPys(R);
	  long     nb = RoMPcnt(R);
	  struct plot_points *points =
	    (struct plot_points *) pari_malloc(sizeof(*points)*nb);
	  for(j=0;j<nb;j++)
	  {
	    points[j].x = DTOL((ptx[j]+x0)*xs);
	    points[j].y = DTOL((pty[j]+y0)*ys);
	  }
	  eng->sc(data,RoCol(R));
	  eng->mp(data, nb, points);
	  pari_free(points);
	  break;
	}
      case ROt_ML:
	{
	  double *ptx = RoMLxs(R);
	  double *pty = RoMLys(R);
	  long     nb = RoMLcnt(R);
	  struct plot_points *points =
	    (struct plot_points *) pari_malloc(sizeof(*points)*nb);
	  for(j=0;j<nb;j++)
	  {
	    points[j].x = DTOL((ptx[j]+x0)*xs);
	    points[j].y = DTOL((pty[j]+y0)*ys);
	  }
	  eng->sc(data,RoCol(R));
	  eng->ml(data, nb, points);
	  pari_free(points);
	  break;
	}
      case ROt_ST:
	{
	  long dir = RoSTdir(R);
	  long hjust = dir & RoSTdirHPOS_mask, hgap  = dir & RoSTdirHGAP;
	  long vjust = dir & RoSTdirVPOS_mask, vgap  = dir & RoSTdirVGAP;
	  char *text = RoSTs(R);
	  long l     = RoSTl(R);
	  long x, y;
	  long shift = (hjust == RoSTdirLEFT ? 0 :
	      (hjust == RoSTdirRIGHT ? 2 : 1));
	  if (hgap)
	    hgap = (hjust == RoSTdirLEFT) ? hgapsize : -hgapsize;
	  if (vgap)
	    vgap = (vjust == RoSTdirBOTTOM) ? 2*vgapsize : -2*vgapsize;
	  if (vjust != RoSTdirBOTTOM)
	    vgap -= ((vjust == RoSTdirTOP) ? 2 : 1)*(fheight - 1);
	  x = DTOL((RoSTx(R) + x0 + hgap - (l * fwidth * shift)/2)*xs);
	  y = DTOL((RoSTy(R) + y0 - vgap/2)*ys);
	  eng->sc(data,RoCol(R));
	  eng->st(data, x, y, text, l);
	  break;
	}
      default:
	break;
      }
    }
  }
}

/*************************************************************************/
/*                                                                       */
/*                           RGB COLORS                                  */
/*                                                                       */
/*************************************************************************/
#if 0
/* generated from /etc/X11/rgb.txt by the following perl script */
#!/usr/bin/perl
while(<>)
{
  ($hex, $name) = split(/\t\t/, $_);
  $hex =~ s/^ +//; chomp($name); $name =~ s/ *//g;
  $hex = sprintf("(void*)0x%02x%02x%02x", split(/\s+/, $hex));
  $name = lc($name); next if ($done{$name});
  $done{$name} = 1;
  print "{(void*)\"$name\", $hex},\n";
}
#endif

static hashentry col_list[] = {
{(void*)"snow", (void*)0xfffafa},
{(void*)"ghostwhite", (void*)0xf8f8ff},
{(void*)"whitesmoke", (void*)0xf5f5f5},
{(void*)"gainsboro", (void*)0xdcdcdc},
{(void*)"floralwhite", (void*)0xfffaf0},
{(void*)"oldlace", (void*)0xfdf5e6},
{(void*)"linen", (void*)0xfaf0e6},
{(void*)"antiquewhite", (void*)0xfaebd7},
{(void*)"papayawhip", (void*)0xffefd5},
{(void*)"blanchedalmond", (void*)0xffebcd},
{(void*)"bisque", (void*)0xffe4c4},
{(void*)"peachpuff", (void*)0xffdab9},
{(void*)"navajowhite", (void*)0xffdead},
{(void*)"moccasin", (void*)0xffe4b5},
{(void*)"cornsilk", (void*)0xfff8dc},
{(void*)"ivory", (void*)0xfffff0},
{(void*)"lemonchiffon", (void*)0xfffacd},
{(void*)"seashell", (void*)0xfff5ee},
{(void*)"honeydew", (void*)0xf0fff0},
{(void*)"mintcream", (void*)0xf5fffa},
{(void*)"azure", (void*)0xf0ffff},
{(void*)"aliceblue", (void*)0xf0f8ff},
{(void*)"lavender", (void*)0xe6e6fa},
{(void*)"lavenderblush", (void*)0xfff0f5},
{(void*)"mistyrose", (void*)0xffe4e1},
{(void*)"white", (void*)0xffffff},
{(void*)"black", (void*)0x000000},
{(void*)"darkslategray", (void*)0x2f4f4f},
{(void*)"darkslategrey", (void*)0x2f4f4f},
{(void*)"dimgray", (void*)0x696969},
{(void*)"dimgrey", (void*)0x696969},
{(void*)"slategray", (void*)0x708090},
{(void*)"slategrey", (void*)0x708090},
{(void*)"lightslategray", (void*)0x778899},
{(void*)"lightslategrey", (void*)0x778899},
{(void*)"gray", (void*)0xbebebe},
{(void*)"grey", (void*)0xbebebe},
{(void*)"lightgrey", (void*)0xd3d3d3},
{(void*)"lightgray", (void*)0xd3d3d3},
{(void*)"midnightblue", (void*)0x191970},
{(void*)"navy", (void*)0x000080},
{(void*)"navyblue", (void*)0x000080},
{(void*)"cornflowerblue", (void*)0x6495ed},
{(void*)"darkslateblue", (void*)0x483d8b},
{(void*)"slateblue", (void*)0x6a5acd},
{(void*)"mediumslateblue", (void*)0x7b68ee},
{(void*)"lightslateblue", (void*)0x8470ff},
{(void*)"mediumblue", (void*)0x0000cd},
{(void*)"royalblue", (void*)0x4169e1},
{(void*)"blue", (void*)0x0000ff},
{(void*)"dodgerblue", (void*)0x1e90ff},
{(void*)"deepskyblue", (void*)0x00bfff},
{(void*)"skyblue", (void*)0x87ceeb},
{(void*)"lightskyblue", (void*)0x87cefa},
{(void*)"steelblue", (void*)0x4682b4},
{(void*)"lightsteelblue", (void*)0xb0c4de},
{(void*)"lightblue", (void*)0xadd8e6},
{(void*)"powderblue", (void*)0xb0e0e6},
{(void*)"paleturquoise", (void*)0xafeeee},
{(void*)"darkturquoise", (void*)0x00ced1},
{(void*)"mediumturquoise", (void*)0x48d1cc},
{(void*)"turquoise", (void*)0x40e0d0},
{(void*)"cyan", (void*)0x00ffff},
{(void*)"lightcyan", (void*)0xe0ffff},
{(void*)"cadetblue", (void*)0x5f9ea0},
{(void*)"mediumaquamarine", (void*)0x66cdaa},
{(void*)"aquamarine", (void*)0x7fffd4},
{(void*)"darkgreen", (void*)0x006400},
{(void*)"darkolivegreen", (void*)0x556b2f},
{(void*)"darkseagreen", (void*)0x8fbc8f},
{(void*)"seagreen", (void*)0x2e8b57},
{(void*)"mediumseagreen", (void*)0x3cb371},
{(void*)"lightseagreen", (void*)0x20b2aa},
{(void*)"palegreen", (void*)0x98fb98},
{(void*)"springgreen", (void*)0x00ff7f},
{(void*)"lawngreen", (void*)0x7cfc00},
{(void*)"green", (void*)0x00ff00},
{(void*)"chartreuse", (void*)0x7fff00},
{(void*)"mediumspringgreen", (void*)0x00fa9a},
{(void*)"greenyellow", (void*)0xadff2f},
{(void*)"limegreen", (void*)0x32cd32},
{(void*)"yellowgreen", (void*)0x9acd32},
{(void*)"forestgreen", (void*)0x228b22},
{(void*)"olivedrab", (void*)0x6b8e23},
{(void*)"darkkhaki", (void*)0xbdb76b},
{(void*)"khaki", (void*)0xf0e68c},
{(void*)"palegoldenrod", (void*)0xeee8aa},
{(void*)"lightgoldenrodyellow", (void*)0xfafad2},
{(void*)"lightyellow", (void*)0xffffe0},
{(void*)"yellow", (void*)0xffff00},
{(void*)"gold", (void*)0xffd700},
{(void*)"lightgoldenrod", (void*)0xeedd82},
{(void*)"goldenrod", (void*)0xdaa520},
{(void*)"darkgoldenrod", (void*)0xb8860b},
{(void*)"rosybrown", (void*)0xbc8f8f},
{(void*)"indianred", (void*)0xcd5c5c},
{(void*)"saddlebrown", (void*)0x8b4513},
{(void*)"sienna", (void*)0xa0522d},
{(void*)"peru", (void*)0xcd853f},
{(void*)"burlywood", (void*)0xdeb887},
{(void*)"beige", (void*)0xf5f5dc},
{(void*)"wheat", (void*)0xf5deb3},
{(void*)"sandybrown", (void*)0xf4a460},
{(void*)"tan", (void*)0xd2b48c},
{(void*)"chocolate", (void*)0xd2691e},
{(void*)"firebrick", (void*)0xb22222},
{(void*)"brown", (void*)0xa52a2a},
{(void*)"darksalmon", (void*)0xe9967a},
{(void*)"salmon", (void*)0xfa8072},
{(void*)"lightsalmon", (void*)0xffa07a},
{(void*)"orange", (void*)0xffa500},
{(void*)"darkorange", (void*)0xff8c00},
{(void*)"coral", (void*)0xff7f50},
{(void*)"lightcoral", (void*)0xf08080},
{(void*)"tomato", (void*)0xff6347},
{(void*)"orangered", (void*)0xff4500},
{(void*)"red", (void*)0xff0000},
{(void*)"hotpink", (void*)0xff69b4},
{(void*)"deeppink", (void*)0xff1493},
{(void*)"pink", (void*)0xffc0cb},
{(void*)"lightpink", (void*)0xffb6c1},
{(void*)"palevioletred", (void*)0xdb7093},
{(void*)"maroon", (void*)0xb03060},
{(void*)"mediumvioletred", (void*)0xc71585},
{(void*)"violetred", (void*)0xd02090},
{(void*)"magenta", (void*)0xff00ff},
{(void*)"violet", (void*)0xee82ee},
{(void*)"plum", (void*)0xdda0dd},
{(void*)"orchid", (void*)0xda70d6},
{(void*)"mediumorchid", (void*)0xba55d3},
{(void*)"darkorchid", (void*)0x9932cc},
{(void*)"darkviolet", (void*)0x9400d3},
{(void*)"blueviolet", (void*)0x8a2be2},
{(void*)"purple", (void*)0xa020f0},
{(void*)"mediumpurple", (void*)0x9370db},
{(void*)"thistle", (void*)0xd8bfd8},
{(void*)"snow1", (void*)0xfffafa},
{(void*)"snow2", (void*)0xeee9e9},
{(void*)"snow3", (void*)0xcdc9c9},
{(void*)"snow4", (void*)0x8b8989},
{(void*)"seashell1", (void*)0xfff5ee},
{(void*)"seashell2", (void*)0xeee5de},
{(void*)"seashell3", (void*)0xcdc5bf},
{(void*)"seashell4", (void*)0x8b8682},
{(void*)"antiquewhite1", (void*)0xffefdb},
{(void*)"antiquewhite2", (void*)0xeedfcc},
{(void*)"antiquewhite3", (void*)0xcdc0b0},
{(void*)"antiquewhite4", (void*)0x8b8378},
{(void*)"bisque1", (void*)0xffe4c4},
{(void*)"bisque2", (void*)0xeed5b7},
{(void*)"bisque3", (void*)0xcdb79e},
{(void*)"bisque4", (void*)0x8b7d6b},
{(void*)"peachpuff1", (void*)0xffdab9},
{(void*)"peachpuff2", (void*)0xeecbad},
{(void*)"peachpuff3", (void*)0xcdaf95},
{(void*)"peachpuff4", (void*)0x8b7765},
{(void*)"navajowhite1", (void*)0xffdead},
{(void*)"navajowhite2", (void*)0xeecfa1},
{(void*)"navajowhite3", (void*)0xcdb38b},
{(void*)"navajowhite4", (void*)0x8b795e},
{(void*)"lemonchiffon1", (void*)0xfffacd},
{(void*)"lemonchiffon2", (void*)0xeee9bf},
{(void*)"lemonchiffon3", (void*)0xcdc9a5},
{(void*)"lemonchiffon4", (void*)0x8b8970},
{(void*)"cornsilk1", (void*)0xfff8dc},
{(void*)"cornsilk2", (void*)0xeee8cd},
{(void*)"cornsilk3", (void*)0xcdc8b1},
{(void*)"cornsilk4", (void*)0x8b8878},
{(void*)"ivory1", (void*)0xfffff0},
{(void*)"ivory2", (void*)0xeeeee0},
{(void*)"ivory3", (void*)0xcdcdc1},
{(void*)"ivory4", (void*)0x8b8b83},
{(void*)"honeydew1", (void*)0xf0fff0},
{(void*)"honeydew2", (void*)0xe0eee0},
{(void*)"honeydew3", (void*)0xc1cdc1},
{(void*)"honeydew4", (void*)0x838b83},
{(void*)"lavenderblush1", (void*)0xfff0f5},
{(void*)"lavenderblush2", (void*)0xeee0e5},
{(void*)"lavenderblush3", (void*)0xcdc1c5},
{(void*)"lavenderblush4", (void*)0x8b8386},
{(void*)"mistyrose1", (void*)0xffe4e1},
{(void*)"mistyrose2", (void*)0xeed5d2},
{(void*)"mistyrose3", (void*)0xcdb7b5},
{(void*)"mistyrose4", (void*)0x8b7d7b},
{(void*)"azure1", (void*)0xf0ffff},
{(void*)"azure2", (void*)0xe0eeee},
{(void*)"azure3", (void*)0xc1cdcd},
{(void*)"azure4", (void*)0x838b8b},
{(void*)"slateblue1", (void*)0x836fff},
{(void*)"slateblue2", (void*)0x7a67ee},
{(void*)"slateblue3", (void*)0x6959cd},
{(void*)"slateblue4", (void*)0x473c8b},
{(void*)"royalblue1", (void*)0x4876ff},
{(void*)"royalblue2", (void*)0x436eee},
{(void*)"royalblue3", (void*)0x3a5fcd},
{(void*)"royalblue4", (void*)0x27408b},
{(void*)"blue1", (void*)0x0000ff},
{(void*)"blue2", (void*)0x0000ee},
{(void*)"blue3", (void*)0x0000cd},
{(void*)"blue4", (void*)0x00008b},
{(void*)"dodgerblue1", (void*)0x1e90ff},
{(void*)"dodgerblue2", (void*)0x1c86ee},
{(void*)"dodgerblue3", (void*)0x1874cd},
{(void*)"dodgerblue4", (void*)0x104e8b},
{(void*)"steelblue1", (void*)0x63b8ff},
{(void*)"steelblue2", (void*)0x5cacee},
{(void*)"steelblue3", (void*)0x4f94cd},
{(void*)"steelblue4", (void*)0x36648b},
{(void*)"deepskyblue1", (void*)0x00bfff},
{(void*)"deepskyblue2", (void*)0x00b2ee},
{(void*)"deepskyblue3", (void*)0x009acd},
{(void*)"deepskyblue4", (void*)0x00688b},
{(void*)"skyblue1", (void*)0x87ceff},
{(void*)"skyblue2", (void*)0x7ec0ee},
{(void*)"skyblue3", (void*)0x6ca6cd},
{(void*)"skyblue4", (void*)0x4a708b},
{(void*)"lightskyblue1", (void*)0xb0e2ff},
{(void*)"lightskyblue2", (void*)0xa4d3ee},
{(void*)"lightskyblue3", (void*)0x8db6cd},
{(void*)"lightskyblue4", (void*)0x607b8b},
{(void*)"slategray1", (void*)0xc6e2ff},
{(void*)"slategray2", (void*)0xb9d3ee},
{(void*)"slategray3", (void*)0x9fb6cd},
{(void*)"slategray4", (void*)0x6c7b8b},
{(void*)"lightsteelblue1", (void*)0xcae1ff},
{(void*)"lightsteelblue2", (void*)0xbcd2ee},
{(void*)"lightsteelblue3", (void*)0xa2b5cd},
{(void*)"lightsteelblue4", (void*)0x6e7b8b},
{(void*)"lightblue1", (void*)0xbfefff},
{(void*)"lightblue2", (void*)0xb2dfee},
{(void*)"lightblue3", (void*)0x9ac0cd},
{(void*)"lightblue4", (void*)0x68838b},
{(void*)"lightcyan1", (void*)0xe0ffff},
{(void*)"lightcyan2", (void*)0xd1eeee},
{(void*)"lightcyan3", (void*)0xb4cdcd},
{(void*)"lightcyan4", (void*)0x7a8b8b},
{(void*)"paleturquoise1", (void*)0xbbffff},
{(void*)"paleturquoise2", (void*)0xaeeeee},
{(void*)"paleturquoise3", (void*)0x96cdcd},
{(void*)"paleturquoise4", (void*)0x668b8b},
{(void*)"cadetblue1", (void*)0x98f5ff},
{(void*)"cadetblue2", (void*)0x8ee5ee},
{(void*)"cadetblue3", (void*)0x7ac5cd},
{(void*)"cadetblue4", (void*)0x53868b},
{(void*)"turquoise1", (void*)0x00f5ff},
{(void*)"turquoise2", (void*)0x00e5ee},
{(void*)"turquoise3", (void*)0x00c5cd},
{(void*)"turquoise4", (void*)0x00868b},
{(void*)"cyan1", (void*)0x00ffff},
{(void*)"cyan2", (void*)0x00eeee},
{(void*)"cyan3", (void*)0x00cdcd},
{(void*)"cyan4", (void*)0x008b8b},
{(void*)"darkslategray1", (void*)0x97ffff},
{(void*)"darkslategray2", (void*)0x8deeee},
{(void*)"darkslategray3", (void*)0x79cdcd},
{(void*)"darkslategray4", (void*)0x528b8b},
{(void*)"aquamarine1", (void*)0x7fffd4},
{(void*)"aquamarine2", (void*)0x76eec6},
{(void*)"aquamarine3", (void*)0x66cdaa},
{(void*)"aquamarine4", (void*)0x458b74},
{(void*)"darkseagreen1", (void*)0xc1ffc1},
{(void*)"darkseagreen2", (void*)0xb4eeb4},
{(void*)"darkseagreen3", (void*)0x9bcd9b},
{(void*)"darkseagreen4", (void*)0x698b69},
{(void*)"seagreen1", (void*)0x54ff9f},
{(void*)"seagreen2", (void*)0x4eee94},
{(void*)"seagreen3", (void*)0x43cd80},
{(void*)"seagreen4", (void*)0x2e8b57},
{(void*)"palegreen1", (void*)0x9aff9a},
{(void*)"palegreen2", (void*)0x90ee90},
{(void*)"palegreen3", (void*)0x7ccd7c},
{(void*)"palegreen4", (void*)0x548b54},
{(void*)"springgreen1", (void*)0x00ff7f},
{(void*)"springgreen2", (void*)0x00ee76},
{(void*)"springgreen3", (void*)0x00cd66},
{(void*)"springgreen4", (void*)0x008b45},
{(void*)"green1", (void*)0x00ff00},
{(void*)"green2", (void*)0x00ee00},
{(void*)"green3", (void*)0x00cd00},
{(void*)"green4", (void*)0x008b00},
{(void*)"chartreuse1", (void*)0x7fff00},
{(void*)"chartreuse2", (void*)0x76ee00},
{(void*)"chartreuse3", (void*)0x66cd00},
{(void*)"chartreuse4", (void*)0x458b00},
{(void*)"olivedrab1", (void*)0xc0ff3e},
{(void*)"olivedrab2", (void*)0xb3ee3a},
{(void*)"olivedrab3", (void*)0x9acd32},
{(void*)"olivedrab4", (void*)0x698b22},
{(void*)"darkolivegreen1", (void*)0xcaff70},
{(void*)"darkolivegreen2", (void*)0xbcee68},
{(void*)"darkolivegreen3", (void*)0xa2cd5a},
{(void*)"darkolivegreen4", (void*)0x6e8b3d},
{(void*)"khaki1", (void*)0xfff68f},
{(void*)"khaki2", (void*)0xeee685},
{(void*)"khaki3", (void*)0xcdc673},
{(void*)"khaki4", (void*)0x8b864e},
{(void*)"lightgoldenrod1", (void*)0xffec8b},
{(void*)"lightgoldenrod2", (void*)0xeedc82},
{(void*)"lightgoldenrod3", (void*)0xcdbe70},
{(void*)"lightgoldenrod4", (void*)0x8b814c},
{(void*)"lightyellow1", (void*)0xffffe0},
{(void*)"lightyellow2", (void*)0xeeeed1},
{(void*)"lightyellow3", (void*)0xcdcdb4},
{(void*)"lightyellow4", (void*)0x8b8b7a},
{(void*)"yellow1", (void*)0xffff00},
{(void*)"yellow2", (void*)0xeeee00},
{(void*)"yellow3", (void*)0xcdcd00},
{(void*)"yellow4", (void*)0x8b8b00},
{(void*)"gold1", (void*)0xffd700},
{(void*)"gold2", (void*)0xeec900},
{(void*)"gold3", (void*)0xcdad00},
{(void*)"gold4", (void*)0x8b7500},
{(void*)"goldenrod1", (void*)0xffc125},
{(void*)"goldenrod2", (void*)0xeeb422},
{(void*)"goldenrod3", (void*)0xcd9b1d},
{(void*)"goldenrod4", (void*)0x8b6914},
{(void*)"darkgoldenrod1", (void*)0xffb90f},
{(void*)"darkgoldenrod2", (void*)0xeead0e},
{(void*)"darkgoldenrod3", (void*)0xcd950c},
{(void*)"darkgoldenrod4", (void*)0x8b6508},
{(void*)"rosybrown1", (void*)0xffc1c1},
{(void*)"rosybrown2", (void*)0xeeb4b4},
{(void*)"rosybrown3", (void*)0xcd9b9b},
{(void*)"rosybrown4", (void*)0x8b6969},
{(void*)"indianred1", (void*)0xff6a6a},
{(void*)"indianred2", (void*)0xee6363},
{(void*)"indianred3", (void*)0xcd5555},
{(void*)"indianred4", (void*)0x8b3a3a},
{(void*)"sienna1", (void*)0xff8247},
{(void*)"sienna2", (void*)0xee7942},
{(void*)"sienna3", (void*)0xcd6839},
{(void*)"sienna4", (void*)0x8b4726},
{(void*)"burlywood1", (void*)0xffd39b},
{(void*)"burlywood2", (void*)0xeec591},
{(void*)"burlywood3", (void*)0xcdaa7d},
{(void*)"burlywood4", (void*)0x8b7355},
{(void*)"wheat1", (void*)0xffe7ba},
{(void*)"wheat2", (void*)0xeed8ae},
{(void*)"wheat3", (void*)0xcdba96},
{(void*)"wheat4", (void*)0x8b7e66},
{(void*)"tan1", (void*)0xffa54f},
{(void*)"tan2", (void*)0xee9a49},
{(void*)"tan3", (void*)0xcd853f},
{(void*)"tan4", (void*)0x8b5a2b},
{(void*)"chocolate1", (void*)0xff7f24},
{(void*)"chocolate2", (void*)0xee7621},
{(void*)"chocolate3", (void*)0xcd661d},
{(void*)"chocolate4", (void*)0x8b4513},
{(void*)"firebrick1", (void*)0xff3030},
{(void*)"firebrick2", (void*)0xee2c2c},
{(void*)"firebrick3", (void*)0xcd2626},
{(void*)"firebrick4", (void*)0x8b1a1a},
{(void*)"brown1", (void*)0xff4040},
{(void*)"brown2", (void*)0xee3b3b},
{(void*)"brown3", (void*)0xcd3333},
{(void*)"brown4", (void*)0x8b2323},
{(void*)"salmon1", (void*)0xff8c69},
{(void*)"salmon2", (void*)0xee8262},
{(void*)"salmon3", (void*)0xcd7054},
{(void*)"salmon4", (void*)0x8b4c39},
{(void*)"lightsalmon1", (void*)0xffa07a},
{(void*)"lightsalmon2", (void*)0xee9572},
{(void*)"lightsalmon3", (void*)0xcd8162},
{(void*)"lightsalmon4", (void*)0x8b5742},
{(void*)"orange1", (void*)0xffa500},
{(void*)"orange2", (void*)0xee9a00},
{(void*)"orange3", (void*)0xcd8500},
{(void*)"orange4", (void*)0x8b5a00},
{(void*)"darkorange1", (void*)0xff7f00},
{(void*)"darkorange2", (void*)0xee7600},
{(void*)"darkorange3", (void*)0xcd6600},
{(void*)"darkorange4", (void*)0x8b4500},
{(void*)"coral1", (void*)0xff7256},
{(void*)"coral2", (void*)0xee6a50},
{(void*)"coral3", (void*)0xcd5b45},
{(void*)"coral4", (void*)0x8b3e2f},
{(void*)"tomato1", (void*)0xff6347},
{(void*)"tomato2", (void*)0xee5c42},
{(void*)"tomato3", (void*)0xcd4f39},
{(void*)"tomato4", (void*)0x8b3626},
{(void*)"orangered1", (void*)0xff4500},
{(void*)"orangered2", (void*)0xee4000},
{(void*)"orangered3", (void*)0xcd3700},
{(void*)"orangered4", (void*)0x8b2500},
{(void*)"red1", (void*)0xff0000},
{(void*)"red2", (void*)0xee0000},
{(void*)"red3", (void*)0xcd0000},
{(void*)"red4", (void*)0x8b0000},
{(void*)"debianred", (void*)0xd70751},
{(void*)"deeppink1", (void*)0xff1493},
{(void*)"deeppink2", (void*)0xee1289},
{(void*)"deeppink3", (void*)0xcd1076},
{(void*)"deeppink4", (void*)0x8b0a50},
{(void*)"hotpink1", (void*)0xff6eb4},
{(void*)"hotpink2", (void*)0xee6aa7},
{(void*)"hotpink3", (void*)0xcd6090},
{(void*)"hotpink4", (void*)0x8b3a62},
{(void*)"pink1", (void*)0xffb5c5},
{(void*)"pink2", (void*)0xeea9b8},
{(void*)"pink3", (void*)0xcd919e},
{(void*)"pink4", (void*)0x8b636c},
{(void*)"lightpink1", (void*)0xffaeb9},
{(void*)"lightpink2", (void*)0xeea2ad},
{(void*)"lightpink3", (void*)0xcd8c95},
{(void*)"lightpink4", (void*)0x8b5f65},
{(void*)"palevioletred1", (void*)0xff82ab},
{(void*)"palevioletred2", (void*)0xee799f},
{(void*)"palevioletred3", (void*)0xcd6889},
{(void*)"palevioletred4", (void*)0x8b475d},
{(void*)"maroon1", (void*)0xff34b3},
{(void*)"maroon2", (void*)0xee30a7},
{(void*)"maroon3", (void*)0xcd2990},
{(void*)"maroon4", (void*)0x8b1c62},
{(void*)"violetred1", (void*)0xff3e96},
{(void*)"violetred2", (void*)0xee3a8c},
{(void*)"violetred3", (void*)0xcd3278},
{(void*)"violetred4", (void*)0x8b2252},
{(void*)"magenta1", (void*)0xff00ff},
{(void*)"magenta2", (void*)0xee00ee},
{(void*)"magenta3", (void*)0xcd00cd},
{(void*)"magenta4", (void*)0x8b008b},
{(void*)"orchid1", (void*)0xff83fa},
{(void*)"orchid2", (void*)0xee7ae9},
{(void*)"orchid3", (void*)0xcd69c9},
{(void*)"orchid4", (void*)0x8b4789},
{(void*)"plum1", (void*)0xffbbff},
{(void*)"plum2", (void*)0xeeaeee},
{(void*)"plum3", (void*)0xcd96cd},
{(void*)"plum4", (void*)0x8b668b},
{(void*)"mediumorchid1", (void*)0xe066ff},
{(void*)"mediumorchid2", (void*)0xd15fee},
{(void*)"mediumorchid3", (void*)0xb452cd},
{(void*)"mediumorchid4", (void*)0x7a378b},
{(void*)"darkorchid1", (void*)0xbf3eff},
{(void*)"darkorchid2", (void*)0xb23aee},
{(void*)"darkorchid3", (void*)0x9a32cd},
{(void*)"darkorchid4", (void*)0x68228b},
{(void*)"purple1", (void*)0x9b30ff},
{(void*)"purple2", (void*)0x912cee},
{(void*)"purple3", (void*)0x7d26cd},
{(void*)"purple4", (void*)0x551a8b},
{(void*)"mediumpurple1", (void*)0xab82ff},
{(void*)"mediumpurple2", (void*)0x9f79ee},
{(void*)"mediumpurple3", (void*)0x8968cd},
{(void*)"mediumpurple4", (void*)0x5d478b},
{(void*)"thistle1", (void*)0xffe1ff},
{(void*)"thistle2", (void*)0xeed2ee},
{(void*)"thistle3", (void*)0xcdb5cd},
{(void*)"thistle4", (void*)0x8b7b8b},
{(void*)"gray0", (void*)0x000000},
{(void*)"grey0", (void*)0x000000},
{(void*)"gray1", (void*)0x030303},
{(void*)"grey1", (void*)0x030303},
{(void*)"gray2", (void*)0x050505},
{(void*)"grey2", (void*)0x050505},
{(void*)"gray3", (void*)0x080808},
{(void*)"grey3", (void*)0x080808},
{(void*)"gray4", (void*)0x0a0a0a},
{(void*)"grey4", (void*)0x0a0a0a},
{(void*)"gray5", (void*)0x0d0d0d},
{(void*)"grey5", (void*)0x0d0d0d},
{(void*)"gray6", (void*)0x0f0f0f},
{(void*)"grey6", (void*)0x0f0f0f},
{(void*)"gray7", (void*)0x121212},
{(void*)"grey7", (void*)0x121212},
{(void*)"gray8", (void*)0x141414},
{(void*)"grey8", (void*)0x141414},
{(void*)"gray9", (void*)0x171717},
{(void*)"grey9", (void*)0x171717},
{(void*)"gray10", (void*)0x1a1a1a},
{(void*)"grey10", (void*)0x1a1a1a},
{(void*)"gray11", (void*)0x1c1c1c},
{(void*)"grey11", (void*)0x1c1c1c},
{(void*)"gray12", (void*)0x1f1f1f},
{(void*)"grey12", (void*)0x1f1f1f},
{(void*)"gray13", (void*)0x212121},
{(void*)"grey13", (void*)0x212121},
{(void*)"gray14", (void*)0x242424},
{(void*)"grey14", (void*)0x242424},
{(void*)"gray15", (void*)0x262626},
{(void*)"grey15", (void*)0x262626},
{(void*)"gray16", (void*)0x292929},
{(void*)"grey16", (void*)0x292929},
{(void*)"gray17", (void*)0x2b2b2b},
{(void*)"grey17", (void*)0x2b2b2b},
{(void*)"gray18", (void*)0x2e2e2e},
{(void*)"grey18", (void*)0x2e2e2e},
{(void*)"gray19", (void*)0x303030},
{(void*)"grey19", (void*)0x303030},
{(void*)"gray20", (void*)0x333333},
{(void*)"grey20", (void*)0x333333},
{(void*)"gray21", (void*)0x363636},
{(void*)"grey21", (void*)0x363636},
{(void*)"gray22", (void*)0x383838},
{(void*)"grey22", (void*)0x383838},
{(void*)"gray23", (void*)0x3b3b3b},
{(void*)"grey23", (void*)0x3b3b3b},
{(void*)"gray24", (void*)0x3d3d3d},
{(void*)"grey24", (void*)0x3d3d3d},
{(void*)"gray25", (void*)0x404040},
{(void*)"grey25", (void*)0x404040},
{(void*)"gray26", (void*)0x424242},
{(void*)"grey26", (void*)0x424242},
{(void*)"gray27", (void*)0x454545},
{(void*)"grey27", (void*)0x454545},
{(void*)"gray28", (void*)0x474747},
{(void*)"grey28", (void*)0x474747},
{(void*)"gray29", (void*)0x4a4a4a},
{(void*)"grey29", (void*)0x4a4a4a},
{(void*)"gray30", (void*)0x4d4d4d},
{(void*)"grey30", (void*)0x4d4d4d},
{(void*)"gray31", (void*)0x4f4f4f},
{(void*)"grey31", (void*)0x4f4f4f},
{(void*)"gray32", (void*)0x525252},
{(void*)"grey32", (void*)0x525252},
{(void*)"gray33", (void*)0x545454},
{(void*)"grey33", (void*)0x545454},
{(void*)"gray34", (void*)0x575757},
{(void*)"grey34", (void*)0x575757},
{(void*)"gray35", (void*)0x595959},
{(void*)"grey35", (void*)0x595959},
{(void*)"gray36", (void*)0x5c5c5c},
{(void*)"grey36", (void*)0x5c5c5c},
{(void*)"gray37", (void*)0x5e5e5e},
{(void*)"grey37", (void*)0x5e5e5e},
{(void*)"gray38", (void*)0x616161},
{(void*)"grey38", (void*)0x616161},
{(void*)"gray39", (void*)0x636363},
{(void*)"grey39", (void*)0x636363},
{(void*)"gray40", (void*)0x666666},
{(void*)"grey40", (void*)0x666666},
{(void*)"gray41", (void*)0x696969},
{(void*)"grey41", (void*)0x696969},
{(void*)"gray42", (void*)0x6b6b6b},
{(void*)"grey42", (void*)0x6b6b6b},
{(void*)"gray43", (void*)0x6e6e6e},
{(void*)"grey43", (void*)0x6e6e6e},
{(void*)"gray44", (void*)0x707070},
{(void*)"grey44", (void*)0x707070},
{(void*)"gray45", (void*)0x737373},
{(void*)"grey45", (void*)0x737373},
{(void*)"gray46", (void*)0x757575},
{(void*)"grey46", (void*)0x757575},
{(void*)"gray47", (void*)0x787878},
{(void*)"grey47", (void*)0x787878},
{(void*)"gray48", (void*)0x7a7a7a},
{(void*)"grey48", (void*)0x7a7a7a},
{(void*)"gray49", (void*)0x7d7d7d},
{(void*)"grey49", (void*)0x7d7d7d},
{(void*)"gray50", (void*)0x7f7f7f},
{(void*)"grey50", (void*)0x7f7f7f},
{(void*)"gray51", (void*)0x828282},
{(void*)"grey51", (void*)0x828282},
{(void*)"gray52", (void*)0x858585},
{(void*)"grey52", (void*)0x858585},
{(void*)"gray53", (void*)0x878787},
{(void*)"grey53", (void*)0x878787},
{(void*)"gray54", (void*)0x8a8a8a},
{(void*)"grey54", (void*)0x8a8a8a},
{(void*)"gray55", (void*)0x8c8c8c},
{(void*)"grey55", (void*)0x8c8c8c},
{(void*)"gray56", (void*)0x8f8f8f},
{(void*)"grey56", (void*)0x8f8f8f},
{(void*)"gray57", (void*)0x919191},
{(void*)"grey57", (void*)0x919191},
{(void*)"gray58", (void*)0x949494},
{(void*)"grey58", (void*)0x949494},
{(void*)"gray59", (void*)0x969696},
{(void*)"grey59", (void*)0x969696},
{(void*)"gray60", (void*)0x999999},
{(void*)"grey60", (void*)0x999999},
{(void*)"gray61", (void*)0x9c9c9c},
{(void*)"grey61", (void*)0x9c9c9c},
{(void*)"gray62", (void*)0x9e9e9e},
{(void*)"grey62", (void*)0x9e9e9e},
{(void*)"gray63", (void*)0xa1a1a1},
{(void*)"grey63", (void*)0xa1a1a1},
{(void*)"gray64", (void*)0xa3a3a3},
{(void*)"grey64", (void*)0xa3a3a3},
{(void*)"gray65", (void*)0xa6a6a6},
{(void*)"grey65", (void*)0xa6a6a6},
{(void*)"gray66", (void*)0xa8a8a8},
{(void*)"grey66", (void*)0xa8a8a8},
{(void*)"gray67", (void*)0xababab},
{(void*)"grey67", (void*)0xababab},
{(void*)"gray68", (void*)0xadadad},
{(void*)"grey68", (void*)0xadadad},
{(void*)"gray69", (void*)0xb0b0b0},
{(void*)"grey69", (void*)0xb0b0b0},
{(void*)"gray70", (void*)0xb3b3b3},
{(void*)"grey70", (void*)0xb3b3b3},
{(void*)"gray71", (void*)0xb5b5b5},
{(void*)"grey71", (void*)0xb5b5b5},
{(void*)"gray72", (void*)0xb8b8b8},
{(void*)"grey72", (void*)0xb8b8b8},
{(void*)"gray73", (void*)0xbababa},
{(void*)"grey73", (void*)0xbababa},
{(void*)"gray74", (void*)0xbdbdbd},
{(void*)"grey74", (void*)0xbdbdbd},
{(void*)"gray75", (void*)0xbfbfbf},
{(void*)"grey75", (void*)0xbfbfbf},
{(void*)"gray76", (void*)0xc2c2c2},
{(void*)"grey76", (void*)0xc2c2c2},
{(void*)"gray77", (void*)0xc4c4c4},
{(void*)"grey77", (void*)0xc4c4c4},
{(void*)"gray78", (void*)0xc7c7c7},
{(void*)"grey78", (void*)0xc7c7c7},
{(void*)"gray79", (void*)0xc9c9c9},
{(void*)"grey79", (void*)0xc9c9c9},
{(void*)"gray80", (void*)0xcccccc},
{(void*)"grey80", (void*)0xcccccc},
{(void*)"gray81", (void*)0xcfcfcf},
{(void*)"grey81", (void*)0xcfcfcf},
{(void*)"gray82", (void*)0xd1d1d1},
{(void*)"grey82", (void*)0xd1d1d1},
{(void*)"gray83", (void*)0xd4d4d4},
{(void*)"grey83", (void*)0xd4d4d4},
{(void*)"gray84", (void*)0xd6d6d6},
{(void*)"grey84", (void*)0xd6d6d6},
{(void*)"gray85", (void*)0xd9d9d9},
{(void*)"grey85", (void*)0xd9d9d9},
{(void*)"gray86", (void*)0xdbdbdb},
{(void*)"grey86", (void*)0xdbdbdb},
{(void*)"gray87", (void*)0xdedede},
{(void*)"grey87", (void*)0xdedede},
{(void*)"gray88", (void*)0xe0e0e0},
{(void*)"grey88", (void*)0xe0e0e0},
{(void*)"gray89", (void*)0xe3e3e3},
{(void*)"grey89", (void*)0xe3e3e3},
{(void*)"gray90", (void*)0xe5e5e5},
{(void*)"grey90", (void*)0xe5e5e5},
{(void*)"gray91", (void*)0xe8e8e8},
{(void*)"grey91", (void*)0xe8e8e8},
{(void*)"gray92", (void*)0xebebeb},
{(void*)"grey92", (void*)0xebebeb},
{(void*)"gray93", (void*)0xededed},
{(void*)"grey93", (void*)0xededed},
{(void*)"gray94", (void*)0xf0f0f0},
{(void*)"grey94", (void*)0xf0f0f0},
{(void*)"gray95", (void*)0xf2f2f2},
{(void*)"grey95", (void*)0xf2f2f2},
{(void*)"gray96", (void*)0xf5f5f5},
{(void*)"grey96", (void*)0xf5f5f5},
{(void*)"gray97", (void*)0xf7f7f7},
{(void*)"grey97", (void*)0xf7f7f7},
{(void*)"gray98", (void*)0xfafafa},
{(void*)"grey98", (void*)0xfafafa},
{(void*)"gray99", (void*)0xfcfcfc},
{(void*)"grey99", (void*)0xfcfcfc},
{(void*)"gray100", (void*)0xffffff},
{(void*)"grey100", (void*)0xffffff},
{(void*)"darkgrey", (void*)0xa9a9a9},
{(void*)"darkgray", (void*)0xa9a9a9},
{(void*)"darkblue", (void*)0x00008b},
{(void*)"darkcyan", (void*)0x008b8b},
{(void*)"darkmagenta", (void*)0x8b008b},
{(void*)"darkred", (void*)0x8b0000},
{(void*)"lightgreen", (void*)0x90ee90},
{NULL} /* sentinel */
};

static void
colorname_to_rgb(const char *s, int *r, int *g, int *b)
{
  hashentry *ep;
  long rgb;

  if (!rgb_colors) rgb_colors = hashstr_import_static(col_list, 1000);
  ep = hash_search(rgb_colors, (void*)s);
  if (!ep) pari_err(talker, "unknown color %s", s);
  rgb = (long)ep->val;
  *b = rgb & 0xff; rgb >>= 8;
  *g = rgb & 0xff; rgb >>= 8;
  *r = rgb;
}

void
color_to_rgb(GEN c, int *r, int *g, int *b)
{
  switch(typ(c))
  {
    case t_STR:
      colorname_to_rgb(GSTR(c), r,g,b);
      break;
    case t_VECSMALL:
      *r = c[1]; *g = c[2]; *b = c[3];
      break;
  }
}
