/*******************************************************************/
/*                                                                 */
/*                         PLOT ROUTINES                           */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "rect.h"

void push_val(entree *ep, GEN a);
void pop_val(entree *ep);
void postdraw0(long *w, long *x, long *y, long lw);
void postdraw00(long *w, long *x, long *y, long lw, long scale);
void rectdraw0(long *w, long *x, long *y, long lw, long do_free);
static void PARI_get_psplot();

static long current_color[NUMRECT];
PariRect **rectgraph = NULL;
PARI_plot pari_plot, pari_psplot;
long  rectpoint_itype = 0;
long  rectline_itype  = 0;

#define STRINGRECT (NUMRECT-2)
#define DRAWRECT (NUMRECT-1)

#define PLOTH_NUMPOINTS 1000
#define PARAM_NUMPOINTS 1500
#define RECUR_NUMPOINTS 8

#define RECUR_MAXDEPTH 10
#define RECUR_PREC 0.001
#define PARAMR_MAXDEPTH 10

/********************************************************************/
/**                                                                **/
/**                         LOW-RES PLOT                           **/
/**                                                                **/
/********************************************************************/
#define ISCR 64
#define JSCR 22
#define BLANK ' '
#define ZERO1 ','
#define ZERO2 '-'
#define ZERO3 '`'
#define PICTZERO(j) ((j) % 3 ? ((j) % 3 == 2 ? ZERO3 : ZERO2) : ZERO1)
#define YY '|'
#define XX_UPPER '\''
#define XX_LOWER '.'
#define FF1 '_'
#define FF2 'x'
#define FF3 '"'
#define PICT(j) ((j) % 3 ? ((j) % 3 == 2 ? FF3 : FF2) : FF1)

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

#define QUARK  ((char*)NULL) /* Used as a special-case */
static GEN quark_gen;

#define READ_EXPR(s)	((s)==QUARK? quark_gen : lisexpr(s))

void
plot(entree *ep, GEN a, GEN b, char *ch,GEN ysmlu,GEN ybigu, long prec)
{
  long av = avma, av2,limite,jz,j,i,sig;
  int jnew, jpre = 0; /* for lint */
  GEN p1,p2,ysml,ybig,x,diff,dyj,dx,y[ISCR+1];
  unsigned char scr[ISCR+1][JSCR+1];
  char buf[80], z;

  sig=gcmp(b,a); if (!sig) return;
  if (sig<0) { x=a; a=b; b=x; }
  x = cgetr(prec); gaffect(a,x); push_val(ep, x);
  for (i=1; i<=ISCR; i++) y[i]=cgetr(3);
  p1 = gdivgs(gsub(b,a), ISCR-1);
  dx = cgetr(prec); gaffect(p1, dx);
  ysml=gzero; ybig=gzero;
  for (j=1; j<=JSCR; j++) scr[1][j]=scr[ISCR][j]=YY;
  for (i=2; i<ISCR; i++)
  {
    scr[i][1] = XX_LOWER;
    scr[i][JSCR]=XX_UPPER;
    for (j=2; j<JSCR; j++) scr[i][j]=BLANK;
  }
  av2=avma; limite=stack_lim(av2,1);
  for (i=1; i<=ISCR; i++)
  {
    gaffect(READ_EXPR(ch),y[i]);
    if (gcmp(y[i],ysml)<0) ysml=y[i];
    if (gcmp(y[i],ybig)>0) ybig=y[i];
    x = addrr(x,dx);
    if (low_stack(limite, stack_lim(av2,1)))
    {
      long tetpil=avma;
      if (DEBUGMEM>1) err(warnmem,"plot");
      x = gerepile(av2,tetpil,rcopy(x));
    }
    ep->value = (void*)x;
  }
  if (ysmlu) ysml=ysmlu;
  if (ybigu) ybig=ybigu;
  avma=av2; diff=gsub(ybig,ysml);
  if (gcmp0(diff)) { ybig=gaddsg(1,ybig); diff=gun; }
  dyj = gdivsg((JSCR-1)*3+2,diff);
  jz = 3-gtolong(gmul(ysml,dyj));
  av2=avma; z = PICTZERO(jz); jz = jz/3;
  for (i=1; i<=ISCR; i++)
  {
    if (0<=jz && jz<=JSCR) scr[i][jz]=z; 
    j=3+gtolong(gmul(gsub(y[i],ysml),dyj));
    jnew = j/3;
    if (i > 1)
    {
      int i_up, i_lo,  mid = (jpre+jnew)/2, up, lo;
      int domid = 0;

      /* If the gap is 1, leave it as it is. */
      if (jpre < jnew - 2) {
        up = jnew - 1; i_up = i;
        lo = jpre + 1; i_lo = i - 1;
        domid = 1;
      } else if (jnew < jpre - 2) {
        up = jpre - 1; i_up = i - 1;
        lo = jnew + 1; i_lo = i;
        domid = 1;
      }
      if (domid)
      {
	if (mid>JSCR) mid=JSCR; else if (mid<0) mid=0;
	if (lo<0) lo=0;
	if (lo<=JSCR) while (lo <= mid) scr[i_lo][lo++] = ':';
	if (up>JSCR) up=JSCR;
        if (up>=0) while (up > mid)  scr[i_up][up--] = ':';
      }
    }
    if (0<=jnew && jnew<=JSCR) scr[i][jnew] = PICT(j);
    avma=av2;
    jpre = jnew;
  }
  p1=cgetr(3); gaffect(ybig,p1); pariputc('\n');
  pariputsf("%s ", dsprintf9(rtodbl(p1), buf));
  for (i=1; i<=ISCR; i++) pariputc(scr[i][JSCR]);
  pariputc('\n');
  for (j=(JSCR-1); j>=2; j--)
  {
    pariputs("          ");
    for (i=1; i<=ISCR; i++) pariputc(scr[i][j]);
    pariputc('\n');
  }
  p1=cgetr(3); gaffect(ysml,p1);
  pariputsf("%s ", dsprintf9(rtodbl(p1), buf));
  for (i=1; i<=ISCR; i++)  pariputc(scr[i][1]);
  pariputc('\n');
  p1=cgetr(3); gaffect(a,p1);
  p2=cgetr(3); gaffect(b,p2);
  pariputsf("%10s%-9.7g%*.7g\n"," ",rtodbl(p1),ISCR-9,rtodbl(p2));
  pop_val(ep); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      RECTPLOT FUNCTIONS                        **/
/**                                                                **/
/********************************************************************/
void
init_graph()
{
  int n;

  rectgraph = (PariRect**) gpmalloc(sizeof(PariRect*)*NUMRECT);
  for (n=0; n<NUMRECT; n++)
  {
    PariRect *e = (PariRect*) gpmalloc(sizeof(PariRect));

    e->head = e->tail = NULL;
    e->sizex = e->sizey = 0;
    current_color[n] = DEFAULT_COLOR;
    rectgraph[n] = e;
  }
}

void
free_graph()
{
  int i;

  for (i=0; i<NUMRECT; i++)
  {
    PariRect *e=rectgraph[i];

    if (RHead(e)) killrect(i);
    free((void *)e);
  }
  free((void *)rectgraph);
}

static PariRect *
check_rect(long ne)
{
  if (!GOODRECT(ne))
    err(talker,"not an rplot vector type in graphic function");
  return rectgraph[ne];
}

static PariRect *
check_rect_init(long ne)
{
  PariRect *e = check_rect(ne);
  if (!RHead(e))
    err(talker,"you must initialize the rectwindow first");
  return e;
}

void
initrect_gen(long ne, GEN x, GEN y, long flag)
{
  long xi, yi;
  if (flag) {
    double xd = gtodouble(x), yd = gtodouble(y);

    PARI_get_plot(0);
    xi = w_width - 1;  yi = w_height - 1;
    if (xd)
      xi = xd*xi + 0.5;
    if (yd)
      yi = yd*yi + 0.5;
  } else {
    xi = itos(x);  yi = itos(y);
    if (!xi || !yi)
      PARI_get_plot(0);
    if (!xi)
      xi = w_width - 1;
    if (!yi)
      yi = w_height - 1;
  }
  initrect(ne, xi, yi);
}

void
initrect(long ne, long x, long y)
{
  PariRect *e;
  RectObj *z;

  if (x<=1 || y<=1) err(talker,"incorrect dimensions in initrect");
  e = check_rect(ne); if (RHead(e)) killrect(ne);

  z = (RectObj*) gpmalloc(sizeof(RectObj));
  RoNext(z) = NULL;
  RoType(z) = ROt_NULL;
  RHead(e)=RTail(e)=z;
  RXsize(e)=x; RYsize(e)=y;
  RXcursor(e)=0; RYcursor(e)=0;
  RXscale(e)=1; RXshift(e)=0;
  RYscale(e)=1; RYshift(e)=0;
  RHasGraph(e) = 0;
}

GEN
rectcursor(long ne)
{
  PariRect *e = check_rect_init(ne);
  GEN z=cgetg(3,t_VEC);

  z[1] = lstoi((long)RXcursor(e)); z[2] = lstoi((long)RYcursor(e));
  return z;
}

static void
rectscale0(long ne, double x1, double x2, double y1, double y2)
{
  PariRect *e = check_rect_init(ne);
  double p2,p3;

  p2 = RXshift(e) + RXscale(e) * RXcursor(e);
  p3 = RYshift(e) + RYscale(e) * RYcursor(e);
  RXscale(e) = RXsize(e)/(x2-x1); RXshift(e) = -x1*RXscale(e);
  RYscale(e) = RYsize(e)/(y1-y2); RYshift(e) = -y2*RYscale(e);
  RXcursor(e) = (p2 - RXshift(e)) / RXscale(e);
  RYcursor(e) = (p3 - RYshift(e)) / RYscale(e);
}

void
rectscale(long ne, GEN x1, GEN x2, GEN y1, GEN y2)
{
  rectscale0(ne, gtodouble(x1), gtodouble(x2), gtodouble(y1), gtodouble(y2));
}

/*
 * #ifdef LONG_IS_64BIT
 * #  define MAXDTOL 9223372036854775807.0
 * #else
 * #  define MAXDTOL 2147483647.0
 * #endif
 *
 *
 * long
 * DTOL(double t)
 * {
 *   if (fabs(t) > MAXDTOL) err(affer2);
 *   return (long)t;
 * }
 */

#define DTOL(t) ((long)(t + 0.5))

static void
rectmove0(long ne, double x, double y, long relative)
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObj1P));

  if (relative)
   { RXcursor(e) += x; RYcursor(e) += y; }
  else
   { RXcursor(e) = x; RYcursor(e) = y; }
  RoNext(z) = 0; RoType(z) = ROt_MV;
  RoMVx(z) = DTOL(RXcursor(e) * RXscale(e) + RXshift(e));
  RoMVy(z) = DTOL(RYcursor(e) * RYscale(e) + RYshift(e));
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
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
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObj1P));

  if (relative)
   { RXcursor(e) += x; RYcursor(e) += y; }
  else
   { RXcursor(e) = x; RYcursor(e) = y; }
  RoNext(z)=0;
  RoPTx(z) = DTOL(RXcursor(e)*RXscale(e) + RXshift(e));
  RoPTy(z) = DTOL(RYcursor(e)*RYscale(e) + RYshift(e));
  RoType(z) = ((RoPTx(z)<0)||(RoPTy(z)<0)||(RoPTx(z)>RXsize(e))
	       ||(RoPTy(z)>RYsize(e))) ? ROt_MV : ROt_PT;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
  RoCol(z)=current_color[ne];
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
rectcolor(long ne, long color)
{
  check_rect(ne);
  if (!GOODCOLOR(color)) err(talker,"This is not a valid color");
  current_color[ne]=color;
}

void
rectline0(long ne, double gx2, double gy2, long relative) /* code = ROt_MV/ROt_LN */
{
  long dx,dy,dxy,xmin,xmax,ymin,ymax,x1,y1,x2,y2;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObj2P));

  x1 = DTOL(RXcursor(e)*RXscale(e) + RXshift(e));
  y1 = DTOL(RYcursor(e)*RYscale(e) + RYshift(e));
  if (relative)
    { RXcursor(e)+=gx2; RYcursor(e)+=gy2; }
  else
    { RXcursor(e)=gx2; RYcursor(e)=gy2; }
  x2 = DTOL(RXcursor(e)*RXscale(e) + RXshift(e));
  y2 = DTOL(RYcursor(e)*RYscale(e) + RYshift(e));
  xmin = max(min(x1,x2),0); xmax = min(max(x1,x2),RXsize(e));
  ymin = max(min(y1,y2),0); ymax = min(max(y1,y2),RYsize(e));
  dxy = x1*y2 - y1*x2; dx = x2-x1; dy = y2-y1;
  if (dy)
  {
    if (dx*dy<0)
      { xmin = max(xmin,(dxy+RYsize(e)*dx)/dy); xmax=min(xmax,dxy/dy); }
    else
      { xmin=max(xmin,dxy/dy); xmax=min(xmax,(dxy+RYsize(e)*dx)/dy); }
  }
  if (dx)
  {
    if (dx*dy<0)
      { ymin=max(ymin,(RXsize(e)*dy-dxy)/dx); ymax=min(ymax,-dxy/dx); }
    else
      { ymin=max(ymin,-dxy/dx); ymax=min(ymax,(RXsize(e)*dy-dxy)/dx); }
  }
  RoNext(z)=0;
  RoLNx1(z) = xmin; RoLNx2(z) = xmax;
  if (dx*dy<0) { RoLNy1(z) = ymax; RoLNy2(z) = ymin; }
  else { RoLNy1(z) = ymin; RoLNy2(z) = ymax; }
  RoType(z) = ((xmin>xmax)||(ymin>ymax)) ? ROt_MV : ROt_LN;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
  RoCol(z)=current_color[ne];
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
  long x1,y1,x2,y2,xmin,ymin,xmax,ymax;
  double xx,yy;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObj2P));

  x1 = DTOL(RXcursor(e)*RXscale(e) + RXshift(e));
  y1 = DTOL(RYcursor(e)*RYscale(e) + RYshift(e));
  if (relative)
  { xx = RXcursor(e)+gx2; yy = RYcursor(e)+gy2; }
  else
  {  xx = gx2; yy = gy2; }
  x2=DTOL(xx*RXscale(e) + RXshift(e));
  y2=DTOL(yy*RYscale(e) + RYshift(e));
  xmin = max(min(x1,x2),0); xmax = min(max(x1,x2),RXsize(e));
  ymin = max(min(y1,y2),0); ymax = min(max(y1,y2),RYsize(e));

  RoNext(z)=0; RoType(z) = ROt_BX;
  RoBXx1(z) = xmin; RoBXy1(z) = ymin;
  RoBXx2(z) = xmax; RoBXy2(z) = ymax;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
  RoCol(z)=current_color[ne];
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

void
killrect(long ne)
{
  RectObj *p1,*p2;
  PariRect *e = check_rect_init(ne);

  current_color[ne]=DEFAULT_COLOR;
  p1=RHead(e);
  RHead(e) = RTail(e) = NULL;
  RXsize(e) = RYsize(e) = 0;
  RXcursor(e) = RYcursor(e) = 0;
  RXscale(e) = RYscale(e) = 1;
  RXshift(e) = RYshift(e) = 0;
  while (p1)
  {
    if (RoType(p1)==ROt_MP || RoType(p1)==ROt_ML)
    {
      free(RoMPxs(p1)); free(RoMPys(p1));
    }
    if (RoType(p1)==ROt_ST) free(RoSTs(p1));
    p2=RoNext(p1); free(p1); p1=p2;
  }
}

void
rectpoints0(long ne, double *listx, double *listy, long lx) /* code = ROt_MP */
{
  long *ptx,*pty,x,y,i,cp=0;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObjMP));

  ptx=(long*) gpmalloc(lx*sizeof(long));
  pty=(long*) gpmalloc(lx*sizeof(long));
  for (i=0; i<lx; i++)
  {
    x=DTOL(RXscale(e)*listx[i] + RXshift(e));
    y=DTOL(RYscale(e)*listy[i] + RYshift(e));
    if ((x>=0)&&(y>=0)&&(x<=RXsize(e))&&(y<=RYsize(e)))
    {
      ptx[cp]=x; pty[cp]=y; cp++;
    }
  }
  RoNext(z)=0; RoType(z) = ROt_MP;
  RoMPcnt(z) = cp; RoMPxs(z) = ptx; RoMPys(z) = pty;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
  RoCol(z)=current_color[ne];
}

void
rectpoints(long ne, GEN listx, GEN listy)
{
  long i,lx, tx=typ(listx), ty=typ(listy);
  double *px,*py;

  if (!is_matvec_t(tx) || !is_matvec_t(ty))
  {
    rectpoint(ne, listx, listy); return;
  }
  if (tx == t_MAT || ty == t_MAT) err(ploter4);
  lx=lg(listx); if (lg(listy)!=lx) err(ploter5);
  lx--; if (!lx) return;

  px = (double*) gpmalloc(lx*sizeof(double));
  py = (double*) gpmalloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    px[i]=gtodouble((GEN)listx[i+1]); py[i]=gtodouble((GEN)listy[i+1]);
  }
  rectpoints0(ne,px,py,lx);
  free(px); free(py);
}

void
rectlines0(long ne, double *x, double *y, long lx, long flag) /* code = ROt_ML */
{
  long i,I,*ptx,*pty;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObj2P));

  I = flag ? lx+1 : lx;
  ptx = (long*) gpmalloc(I*sizeof(long));
  pty = (long*) gpmalloc(I*sizeof(long));
  for (i=0; i<lx; i++)
  {
    ptx[i]=DTOL(RXscale(e)*x[i] + RXshift(e));
    pty[i]=DTOL(RYscale(e)*y[i] + RYshift(e));
  }
  if (flag)
  {
    ptx[i]=DTOL(RXscale(e)*x[0] + RXshift(e));
    pty[i]=DTOL(RYscale(e)*y[0] + RYshift(e));
  }
  RoNext(z)=0; RoType(z)=ROt_ML;
  RoMLcnt(z)=lx; RoMLxs(z)=ptx; RoMLys(z)=pty;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
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
  if (tx == t_MAT || ty == t_MAT) err(ploter4);
  if (lg(listy)!=lx) err(ploter5);
  lx--; if (!lx) return;

  x = (double*) gpmalloc(lx*sizeof(double));
  y = (double*) gpmalloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    x[i] = gtodouble((GEN)listx[i+1]); y[i] = gtodouble((GEN)listy[i+1]);
  }
  rectlines0(ne,x,y,lx,flag);
  free(x); free(y);
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
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObjST));
  long l = strlen(str);
  char *s = (char *) gpmalloc(l+1);

  strcpy(s,str);
  RoNext(z)=0; RoType(z) = ROt_ST;
  RoSTl(z) = l; RoSTs(z) = s;
  RoSTx(z) = DTOL(RXscale(e)*RXcursor(e)+RXshift(e));
  RoSTy(z) = DTOL(RYscale(e)*RYcursor(e)+RYshift(e));
  RoSTdir(z) = dir;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
  RoCol(z)=current_color[ne];
}

void
rectpointtype(long ne, long type) /* code = ROt_PTT */
{
 if (ne == -1) {
     rectpoint_itype = type;
 } else {
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObjPN));

  RoNext(z) = 0; RoType(z) = ROt_PTT;
  RoPTTpen(z) = type;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
 }
}

void
rectpointsize(long ne, GEN size) /* code = ROt_PTS */
{
 if (ne == -1) {
     set_pointsize(gtodouble(size));	/* Immediate set */
 } else {
     PariRect *e = check_rect_init(ne);
     RectObj *z = (RectObj*) gpmalloc(sizeof(RectObjPS));

     RoNext(z) = 0; RoType(z) = ROt_PTS;
     RoPTSsize(z) = gtodouble(size);
     if (!RHead(e)) RHead(e)=RTail(e)=z;
     else { RoNext(RTail(e))=z; RTail(e)=z; }
 }
}

void
rectlinetype(long ne, long type)
{
 if (ne == -1) {
     rectline_itype = type;
 } else {
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) gpmalloc(sizeof(RectObjPN));

  RoNext(z) = 0; RoType(z) = ROt_LNT;
  RoLNTpen(z) = type;
  if (!RHead(e)) RHead(e)=RTail(e)=z;
  else { RoNext(RTail(e))=z; RTail(e)=z; }
 }
}

void
rectcopy_gen(long source, long dest, GEN xoff, GEN yoff, long flag)
{
  long xi, yi;
  if (flag & RECT_CP_RELATIVE) {
    double xd = gtodouble(xoff), yd = gtodouble(yoff);

    PARI_get_plot(0);
    xi = w_width - 1;  yi = w_height - 1;
    xi = xd*xi + 0.5;
    yi = yd*yi + 0.5;
  } else {
    xi = itos(xoff);  yi = itos(yoff);
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
  RectObj *p1 = RHead(s);
  RectObj *tail = RTail(d);
  RectObj *next;
  int i;

  while (p1)
  {
    switch(RoType(p1))
    {
      case ROt_PT:
	next = (RectObj*) gpmalloc(sizeof(RectObj1P));
	memcpy(next,p1,sizeof(RectObj1P));
	RoPTx(next) += xoff; RoPTy(next) += yoff;
	RoNext(tail) = next; tail = next;
	break;
      case ROt_LN: case ROt_BX:
	next = (RectObj*) gpmalloc(sizeof(RectObj2P));
	memcpy(next,p1,sizeof(RectObj2P));
	RoLNx1(next) += xoff; RoLNy1(next) += yoff;
	RoLNx2(next) += xoff; RoLNy2(next) += yoff;
	RoNext(tail) = next; tail = next;
	break;
      case ROt_MP: case ROt_ML:
	next = (RectObj*) gpmalloc(sizeof(RectObjMP));
	memcpy(next,p1,sizeof(RectObjMP));
	RoMPxs(next) = (long*) gpmalloc(sizeof(long)*RoMPcnt(next));
	RoMPys(next) = (long*) gpmalloc(sizeof(long)*RoMPcnt(next));
	memcpy(RoMPxs(next),RoMPxs(p1),sizeof(long)*RoMPcnt(next));
	memcpy(RoMPys(next),RoMPys(p1),sizeof(long)*RoMPcnt(next));
	for (i=0; i<RoMPcnt(next); i++)
	{
	  RoMPxs(next)[i] += xoff; RoMPys(next)[i] += yoff;
	 }
	RoNext(tail) = next; tail = next;
	break;
      case ROt_ST:
	next = (RectObj*) gpmalloc(sizeof(RectObjST));
	memcpy(next,p1,sizeof(RectObjMP));
	RoSTs(next) = (char*) gpmalloc(RoSTl(p1)+1);
	memcpy(RoSTs(next),RoSTs(p1),RoSTl(p1)+1);
	RoSTx(next) += xoff; RoSTy(next) += yoff;
	RoNext(tail) = next; tail = next;
	break;
      case ROt_PTT: case ROt_LNT: case ROt_PTS:
	next = (RectObj*) gpmalloc(sizeof(RectObjPN));
	memcpy(next,p1,sizeof(RectObjPN));
	RoNext(tail) = next; tail = next;
	break;
    }
    p1=RoNext(p1);
  }
  RoNext(tail) = NULL; RTail(d) = tail;
}

#define CLIPLINE_NONEMPTY	1
#define CLIPLINE_CLIP_1		2
#define CLIPLINE_CLIP_2		4

/* A simpler way is to clip by 4 half-planes */
static int
clipline(long xmin, long xmax, long ymin, long ymax, long *x1p, long *y1p, long *x2p, long *y2p)
{
    int xy_exch = 0, rc = CLIPLINE_NONEMPTY;
    double t;
    double xi, yi;
    double sl;
    double xmn, xmx;
    double ymn, ymx;
    int x1_is_ymn, x1_is_xmn;
    double x1 = *x1p, x2 = *x2p, y1 = *y1p, y2 = *y2p;

    if ((x1 < xmin &&  x2 < xmin) || (x1 > xmax && x2 > xmax))
	return 0;
    if (fabs(x1 - x2) < fabs(y1 - y2)) { /* Exchange x and y */
	xy_exch = 1;
	t = xmin, xmin = ymin, ymin = t;
	t = xmax, xmax = ymax, ymax = t;
	t = x1, x1 = y1, y1 = t;
	t = x2, x2 = y2, y2 = t;
    }

    /* Build y as a function of x */
    xi = x1, yi = y1;
    sl = ( (x1==x2) ? 0 : (y2 - yi)/(x2 - xi) );

    xmn = x1, xmx = x2;
    if (x1 > x2) {
	x1_is_xmn = 0;
	xmn = x2, xmx = x1;
    } else
	x1_is_xmn = 1;

    if (xmn < xmin) {
	xmn = xmin;
	rc |= (x1_is_xmn ? CLIPLINE_CLIP_1 : CLIPLINE_CLIP_2);
    }
    
    if (xmx > xmax) {
	xmx = xmax;
	rc |= (x1_is_xmn ? CLIPLINE_CLIP_2 : CLIPLINE_CLIP_1);
    }
    
    if (xmn > xmx)
	return 0;

    ymn = yi + (xmn - xi)*sl;
    ymx = yi + (xmx - xi)*sl;

    if (sl < 0)
	t = ymn, ymn = ymx, ymx = t;
    if (ymn > ymax || ymx < ymin)
	return 0;

    if (rc & CLIPLINE_CLIP_1)
	x1 = (x1_is_xmn ? xmn : xmx);
    if (rc & CLIPLINE_CLIP_2)
	x2 = (x1_is_xmn ? xmx : xmn);

    /* Now we know there is an intersection, need to move x1 and x2 */
    x1_is_ymn = ((sl >= 0) == (x1 < x2));
    if (ymn < ymin) {
	double x = (ymin - yi)/sl + xi; /* slope != 0  ! */

	if (x1_is_ymn)
	    x1 = x, rc |= CLIPLINE_CLIP_1;
	else
	    x2 = x, rc |= CLIPLINE_CLIP_2;
    }
    if (ymx > ymax) {
	double x = (ymax - yi)/sl + xi; /* slope != 0  ! */

	if (x1_is_ymn)
	    x2 = x, rc |= CLIPLINE_CLIP_2;
	else
	    x1 = x, rc |= CLIPLINE_CLIP_1;
    }
    if (rc & CLIPLINE_CLIP_1)
	y1 = yi + (x1 - xi)*sl;
    if (rc & CLIPLINE_CLIP_2)
	y2 = yi + (x2 - xi)*sl;
    if (xy_exch)			/* Exchange x and y */
	*x1p = y1, *x2p = y2, *y1p = x1, *y2p = x2;
    else
	*x1p = x1, *x2p = x2, *y1p = y1, *y2p = y2;
    return rc;
}

void
rectclip(long rect)
{
  PariRect *s = check_rect_init(rect);
  RectObj *p1 = RHead(s);
  RectObj **prevp = &RHead(s);
  RectObj *next;
  double xmin = 0;
  double xmax = RXsize(s);
  double ymin = 0;
  double ymax = RYsize(s);

  while (p1) {
      int did_clip = 0;

      next = RoNext(p1);
      switch(RoType(p1)) {
      case ROt_PT:
	  if ( RoPTx(p1) < xmin || RoPTx(p1) > xmax
	       || RoPTy(p1) < ymin || RoPTy(p1) > ymax) {
		 remove:
	      *prevp = next;
	      free(p1);
	      break;
	  }
	  goto do_next;
      case ROt_BX:
	  if (RoLNx1(p1) < xmin)
	      RoLNx1(p1) = xmin, did_clip = 1;
	  if (RoLNx2(p1) < xmin)
	      RoLNx2(p1) = xmin, did_clip = 1;
	  if (RoLNy1(p1) < ymin)
	      RoLNy1(p1) = ymin, did_clip = 1;
	  if (RoLNy2(p1) < ymin)
	      RoLNy2(p1) = ymin, did_clip = 1;
	  if (RoLNx1(p1) > xmax)
	      RoLNx1(p1) = xmax, did_clip = 1;
	  if (RoLNx2(p1) > xmax)
	      RoLNx2(p1) = xmax, did_clip = 1;
	  if (RoLNy1(p1) > ymax)
	      RoLNy1(p1) = ymax, did_clip = 1;
	  if (RoLNy2(p1) > ymax)
	      RoLNy2(p1) = ymax, did_clip = 1;
	  /* Remove zero-size clipped boxes */
	  if ( did_clip
	       && RoLNx1(p1) == RoLNx2(p1) && RoLNy1(p1) == RoLNy2(p1) )
	      goto remove;
	  goto do_next;
      case ROt_LN:
	  if (!clipline(xmin, xmax, ymin, ymax, 
			&RoLNx1(p1), &RoLNy1(p1), &RoLNx2(p1), &RoLNy2(p1)))
	      goto remove;
	  goto do_next;
      case ROt_MP: 
      {
	  int c = RoMPcnt(p1);
	  int f = 0, t = 0;

	  while (f < c) {
	      if ( RoMPxs(p1)[f] >= xmin && RoMPxs(p1)[f] <= xmax
		   && RoMPys(p1)[f] >= ymin && RoMPys(p1)[f] <= ymax) {
		  if (t != f) {
		      RoMPxs(p1)[t] = RoMPxs(p1)[f];
		      RoMPys(p1)[t] = RoMPys(p1)[f];
		  }
		  t++;
	      }
	      f++;
	  }
	  if (t == 0)
	      goto remove;
	  RoMPcnt(p1) = t;
	  goto do_next;
      }
      case ROt_ML:
      {
	  /* Hard case.  Here we need to break a multiline into
	     several pieces if some part is clipped. */
	  int c = RoMPcnt(p1) - 1;
	  int f = 0, t = 0, had_lines = 0, had_hole = 0, rc;
	  long ox = RoMLxs(p1)[0], oy = RoMLys(p1)[0], oxn, oyn;

	  while (f < c) {
	      /* Endpoint of this segment is the startpoint of the
		 next one, so we need to preserve it if it is clipped. */
	      oxn = RoMLxs(p1)[f + 1], oyn = RoMLys(p1)[f + 1];
	      rc = clipline(xmin, xmax, ymin, ymax, 
			    /* &RoMLxs(p1)[f], &RoMLys(p1)[f], */
			    &ox, &oy,
			    &RoMLxs(p1)[f+1], &RoMLys(p1)[f+1]);
	      RoMLxs(p1)[f] = ox; RoMLys(p1)[f] = oy;
	      ox = oxn; oy = oyn;
	      if (!rc) {
		  if (had_lines)
		      had_hole = 1;
		  f++;
		  continue;
	      }

	      if ( !had_lines || (!(rc & CLIPLINE_CLIP_1) && !had_hole) ) {
		  /* Continuous */
		  had_lines = 1;
		  if (t != f) {
		      if (t == 0) {
			  RoMPxs(p1)[t] = RoMPxs(p1)[f];
			  RoMPys(p1)[t] = RoMPys(p1)[f];
		      }
		      RoMPxs(p1)[t+1] = RoMPxs(p1)[f+1];
		      RoMPys(p1)[t+1] = RoMPys(p1)[f+1];
		  }
		  t++;
		  f++;
		  if ( rc & CLIPLINE_CLIP_2)
		      had_hole = 1, RoMLcnt(p1) = t + 1;
		  continue;
	      }
	      /* Is not continuous, automatically p1 is not free()ed.  */
	      RoMLcnt(p1) = t + 1;
	      if ( rc & CLIPLINE_CLIP_2) { /* Needs separate entry */
		  RectObj *n = (RectObj*) gpmalloc(sizeof(RectObj2P));

		  RoType(n) = ROt_LN;
		  RoCol(n) = RoCol(p1);
		  RoLNx1(n) = RoMLxs(p1)[f];	RoLNy1(n) = RoMLys(p1)[f];
		  RoLNx2(n) = RoMLxs(p1)[f+1];	RoLNy2(n) = RoMLys(p1)[f+1];
		  RoNext(n) = next;
		  RoNext(p1) = n;
		  /* Restore the unclipped value: */
		  RoMLxs(p1)[f + 1] = oxn;	RoMLys(p1)[f + 1] = oyn;
		  f++;
		  prevp = &RoNext(n);
	      }
	      if (f + 1 < c) {		/* Are other lines */
		  RectObj *n = (RectObj*) gpmalloc(sizeof(RectObjMP));
		  RoType(n) = ROt_ML;
		  RoCol(n) = RoCol(p1);
		  RoMLcnt(n) = c - f;
		  RoMLxs(n) = (long*) gpmalloc(sizeof(long)*(c - f));
		  RoMLys(n) = (long*) gpmalloc(sizeof(long)*(c - f));
		  memcpy(RoMPxs(n),RoMPxs(p1) + f, sizeof(long)*(c - f));
		  memcpy(RoMPys(n),RoMPys(p1) + f, sizeof(long)*(c - f));
		  RoMPxs(n)[0] = oxn; RoMPys(n)[0] = oyn; 
		  RoNext(n) = next;
		  RoNext(p1) = n;
		  next = n;
	      }
	      goto do_next;
	  }
	  if (t == 0)
	      goto remove;
	  goto do_next;
      }
#if 0
      case ROt_ST:
	  next = (RectObj*) gpmalloc(sizeof(RectObjMP));
	  memcpy(next,p1,sizeof(RectObjMP));
	  RoSTs(next) = (char*) gpmalloc(RoSTl(p1)+1);
	  memcpy(RoSTs(next),RoSTs(p1),RoSTl(p1)+1);
	  RoSTx(next) += xoff; RoSTy(next) += yoff;
	  RoNext(tail) = next; tail = next;
	  break;
#endif
      default: {
	do_next:  
	      prevp = &RoNext(p1);
	      break;
	  }
      }
      p1 = next;
  }
}

/********************************************************************/
/**                                                                **/
/**                        HI-RES PLOT                             **/
/**                                                                **/
/********************************************************************/

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
  long param=(flags & PLOT_PARAMETRIC);
  GEN x,y;

  if (! is_vec_t(tx)) err(talker,"not a vector in gtodblList");
  if (!nl) return NULL;
  lx1=lg(data[1]);

  /* Allocate memory, then convert coord. to double */
  l=(dblPointList*) gpmalloc(nl*sizeof(dblPointList));
  for (i=0; i<nl-1; i+=2)
  {
    u=i+1;
    x=(GEN)data[u]; tx = typ(x);
    y=(GEN)data[u+1]; ty = typ(y);
    if (!is_vec_t(tx) || !is_vec_t(ty)) err(ploter4);
    lx=lg(x); if (lg(y)!=lx) err(ploter5);
    if (!param && lx != lx1) err(ploter5);
    lx--;

    if (lx)
    {
      l[i].d = (double*) gpmalloc(lx*sizeof(double));
      l[u].d = (double*) gpmalloc(lx*sizeof(double));

      for (j=0; j<lx; j=v)
      {
	v=j+1;
	l[i].d[j]=gtodouble((GEN)x[v]);
	l[u].d[j]=gtodouble((GEN)y[v]);
      }
    }
    l[i].nb=l[u].nb=lx;
  }

  xsml=xbig=l[0].d[0]; ysml=ybig=l[1].d[0];

  /* Now compute extremas */
  if (param)
  {
    l[0].nb=nl/2;
    for (i=0; i<l[0].nb; i+=2)
    {
      u=i+1;
      for (j=0; j<l[u].nb; j++)
      {
	if (l[i].d[j]<xsml)
	  xsml=l[i].d[j];
	else
	  if (l[i].d[j]>xbig) xbig=l[i].d[j];

	if (l[u].d[j]<ysml)
	  ysml=l[u].d[j];
	else
	  if (l[u].d[j]>ybig) ybig=l[u].d[j];
      }
    }
  }
  else
  {
    l[0].nb=nl-1;
    for (j=0; j<l[1].nb; j++)
    {
      if (l[0].d[j]<xsml)
	xsml=l[0].d[j];
      else
	if (l[0].d[j]>xbig) xbig=l[0].d[j];
    }
    for (i=1; i<=l[0].nb; i++)
    {
      for (j=0; j<l[i].nb; j++)
      {
	if (l[i].d[j]<ysml)
	  ysml=l[i].d[j];
	else
	  if (l[i].d[j]>ybig) ybig=l[i].d[j];
      }
    }
  }
  l[0].xsml=xsml; l[0].xbig=xbig;
  l[0].ysml=ysml; l[0].ybig=ybig;
  return l;
}

static void
single_recursion(dblPointList *pl,char *ch,entree *ep,GEN xleft,GEN yleft,
  GEN xright,GEN yright,long depth)
{
  GEN xx,yy;
  long av=avma;
  double dy=pl[0].ybig - pl[0].ysml;

  if (depth==RECUR_MAXDEPTH) return;

  yy=cgetr(3); xx=gmul2n(gadd(xleft,xright),-1);
  ep->value = (void*) xx; gaffect(READ_EXPR(ch), yy);

  if (dy)
  {
    if (fabs(rtodbl(yleft)+rtodbl(yright)-2*rtodbl(yy))/dy < RECUR_PREC)
      return;
  }
  single_recursion(pl,ch,ep, xleft,yleft, xx,yy, depth+1);

  Appendx(&pl[0],&pl[0],rtodbl(xx));
  Appendy(&pl[0],&pl[1],rtodbl(yy));

  single_recursion(pl,ch,ep, xx,yy, xright,yright, depth+1);

  avma=av;
}

static void
param_recursion(dblPointList *pl,char *ch,entree *ep, GEN tleft,GEN xleft,
  GEN yleft, GEN tright,GEN xright,GEN yright, long depth)
{
  GEN tt,xx,yy, p1;
  long av=avma;
  double dy=pl[0].ybig - pl[0].ysml;
  double dx=pl[0].xbig - pl[0].xsml;

  if (depth==PARAMR_MAXDEPTH) return;

  xx=cgetr(3); yy=cgetr(3); tt=gmul2n(gadd(tleft,tright),-1);
  ep->value = (void*)tt; p1=READ_EXPR(ch);
  gaffect((GEN)p1[1],xx); gaffect((GEN)p1[2],yy);

  if (dx && dy)
  {
    if (fabs(rtodbl(xleft)+rtodbl(xright)-2*rtodbl(xx))/dx < RECUR_PREC &&
       fabs(rtodbl(yleft)+rtodbl(yright)-2*rtodbl(yy))/dy < RECUR_PREC)
        return;
  }
  param_recursion(pl,ch,ep, tleft,xleft,yleft, tt,xx,yy, depth+1);

  Appendx(&pl[0],&pl[0],rtodbl(xx));
  Appendy(&pl[0],&pl[1],rtodbl(yy));

  param_recursion(pl,ch,ep, tt,xx,yy, tright,xright,yright, depth+1);

  avma=av;
}

/*
 *  Pure graphing. If testpoints is 0, it is set to the default.
 *  Returns a dblPointList of (absolute) coordinates.
 */
static dblPointList *
rectplothin(entree *ep, GEN a, GEN b, char *ch, long prec, ulong flags,
            long testpoints)
{
  long single_c;
  long param=flags & PLOT_PARAMETRIC;
  long recur=flags & PLOT_RECURSIVE;
  GEN p1,dx,x,xleft,xright,yleft,yright,tleft,tright;
  dblPointList *pl;
  long tx,av = avma,av2,i,j,sig,nc,nl,nbpoints;
  double xsml,xbig,ysml,ybig,fx,fy;

  if (!testpoints)
  {
    if (recur)
      testpoints = RECUR_NUMPOINTS;
    else
      testpoints = param? PARAM_NUMPOINTS : PLOTH_NUMPOINTS;
  }
  if (recur)
    nbpoints = testpoints << (param? PARAMR_MAXDEPTH : RECUR_MAXDEPTH);
  else
    nbpoints = testpoints;

  sig=gcmp(b,a); if (!sig) return 0;
  if (sig<0) { x=a; a=b; b=x; }
  dx=gdivgs(gsub(b,a),testpoints-1);

  x = cgetr(prec); gaffect(a,x); push_val(ep, x);
  av2=avma; p1=READ_EXPR(ch); tx=typ(p1);
  if (!is_matvec_t(tx))
  {
    xsml = gtodouble(a);
    xbig = gtodouble(b);
    ysml = ybig = gtodouble(p1);
    nc=1; nl=2; /* nc = nb of curves; nl = nb of coord. lists */
    if (param)
      err(warner,"flag PLOT_PARAMETRIC ignored");
    single_c=1; param=0;
  }
  else
  {
    if (tx != t_VEC) err(talker,"not a row vector in ploth");
    nl=lg(p1)-1; if (!nl) { avma=av; return 0; }
    single_c=0;
    if (param) nc=nl/2; else { nc=nl; nl++; }
    if (recur && nc > 1) err(talker,"multi-curves cannot be plot recursively");

    if (param)
    {
      xbig=xsml=gtodouble((GEN)p1[1]);
      ybig=ysml=gtodouble((GEN)p1[2]);
      for (i=3; i<=nl; i++)
      {
	fx=gtodouble((GEN)p1[i]); i++;
        fy=gtodouble((GEN)p1[i]);
	if (xsml>fx) xsml=fx; else if (xbig<fx) xbig=fx;
	if (ysml>fy) ysml=fy; else if (ybig<fy) ybig=fy;
      }
    }
    else
    {
      xsml=gtodouble(a); xbig=gtodouble(b);
      ysml=gtodouble(vecmin(p1)); ybig=gtodouble(vecmax(p1));
    }
  }

  pl=(dblPointList*) gpmalloc(nl*sizeof(dblPointList));
  for (i = 0; i < nl; i++)
  {
    pl[i].d = (double*) gpmalloc((nbpoints+1)*sizeof(dblPointList));
    pl[i].nb=0;
  }
  pl[0].xsml=xsml; pl[0].ysml=ysml; pl[0].xbig=xbig; pl[0].ybig=ybig;

  if (recur) /* recursive plot */
  {
    xleft=cgetr(3); xright=cgetr(3); yleft=cgetr(3); yright=cgetr(3);
    if (param)
    {
      tleft=cgetr(prec); tright=cgetr(prec);
      av2=avma;
      gaffect(a,tleft); ep->value = (void*)tleft; p1=READ_EXPR(ch);
      gaffect((GEN)p1[1],xleft); gaffect((GEN)p1[2],yleft);
      for (i=0; i<testpoints-1; i++)
      {
	if (i) {
	  gaffect(tright,tleft); gaffect(xright,xleft); gaffect(yright,yleft);
	 }
	gaddz(tleft,dx,tright); ep->value = (void*)tright;
        p1 = READ_EXPR(ch);
        if (lg(p1) != 3) err(talker,"inconsistent data in rectplothin");
        gaffect((GEN)p1[1],xright); gaffect((GEN)p1[2],yright);

	Appendx(&pl[0],&pl[0],rtodbl(xleft));
	Appendy(&pl[0],&pl[1],rtodbl(yleft));

	param_recursion(pl,ch,ep, tleft,xleft,yleft, tright,xright,yright, 0);
	avma=av2;
      }
      Appendx(&pl[0],&pl[0],rtodbl(xright));
      Appendy(&pl[0],&pl[1],rtodbl(yright));
    }
    else /* single_c */
    {
      av2=avma;
      gaffect(a,xleft); ep->value = (void*) xleft;
      gaffect(READ_EXPR(ch),yleft);
      for (i=0; i<testpoints-1; i++)
      {
        gaddz(xleft,dx,xright); ep->value = (void*) xright;
	gaffect(READ_EXPR(ch),yright);

	Appendx(&pl[0],&pl[0],rtodbl(xleft));
	Appendy(&pl[0],&pl[1],rtodbl(yleft));

        single_recursion(pl,ch,ep,xleft,yleft,xright,yright,0);
        avma=av2;
        gaffect(xright,xleft); gaffect(yright,yleft);
      }
      Appendx(&pl[0],&pl[0],rtodbl(xright));
      Appendy(&pl[0],&pl[1],rtodbl(yright));
    }
  }
  else /* non-recursive plot */
  {
    if (single_c)
      for (i=0; i<testpoints; i++)
      {
	p1 = READ_EXPR(ch);
	pl[0].d[i]=gtodouble(x);
	Appendy(&pl[0],&pl[1],gtodouble(p1));
	gaddz(x,dx,x); avma=av2;
      }
    else if (param)
    {
      long k;
      double z;

      for (i=0; i<testpoints; i++)
      {
	p1 = READ_EXPR(ch);
        if (lg(p1) != nl+1) err(talker,"inconsistent data in rectplothin");
	for (j=0; j<nl; j=k)
	{
	  k=j+1; z=gtodouble((GEN)p1[k]);
	  Appendx(&pl[0], &pl[j],z);

	  j=k; k++; z=gtodouble((GEN)p1[k]);
	  Appendy(&pl[0], &pl[j],z);
	 }
	gaddz(x,dx,x); avma=av2;
      }
    }
    else /* plothmult */
      for (i=0; i<testpoints; i++)
      {
	p1 = READ_EXPR(ch);
        if (lg(p1) != nl) err(talker,"inconsistent data in rectplothin");
	pl[0].d[i]=gtodouble(x);
	for (j=1; j<nl; j++) { Appendy(&pl[0],&pl[j],gtodouble((GEN)p1[j])); }
	gaddz(x,dx,x); avma=av2;
      }
  }
  pl[0].nb=nc; pop_val(ep); avma = av;
  return pl;
}

GEN polint_i(GEN xa, GEN ya, GEN x, long n, GEN *ptdy);

/* Uses highlevel plotting functions to implement splines as
   a low-level plotting function.
   Most probably one does not need to make varn==0 into pure variable,
   since plotting functions should take care of this. */
static void
rectsplines(long ne, double *x, double *y, long lx, long flag)
{
  long i, j, oldavma = avma;
  GEN tas, xa = cgetg(lx+1, t_VEC), ya = cgetg(lx+1, t_VEC);
  entree *var0 = varentries[ordvar[0]];

  if (lx < 4)
      err(talker, "Too few points (%ld) for spline plot", lx);
  for (i = 1; i <= lx; i++) {
      xa[i] = (long) dbltor(x[i-1]);
      ya[i] = (long) dbltor(y[i-1]);
  }
  if (flag & PLOT_PARAMETRIC) {
      tas = new_chunk(4);
      for (j = 1; j <= 4; j++)
	  tas[j-1] = (long)stoi(j);
      quark_gen = cgetg(2 + 1, t_VEC);
  }
  for (i = 0; i <= lx - 4; i++) {
      long oavma = avma;

      xa++; ya++;
      if (flag & PLOT_PARAMETRIC) {
	  quark_gen[1] = (long)polint_i(tas, xa, polx[0], 4, NULL);
	  quark_gen[2] = (long)polint_i(tas, ya, polx[0], 4, NULL);
      } else {
	  quark_gen = polint_i(xa, ya, polx[0], 4, NULL);
          tas = xa;
      }
      rectploth(ne, var0,
                 (GEN)(i==0 ? tas[0] : tas[1]),
                 (GEN)(i==lx-4 ? tas[3] : tas[2]),
                 QUARK,
		 DEFAULTPREC,		/* XXXX precision */
		 PLOT_RECURSIVE
                   | PLOT_NO_RESCALE
                   | PLOT_NO_FRAME
		   | PLOT_NO_AXE_Y
                   | PLOT_NO_AXE_X
                   | (flag & PLOT_PARAMETRIC),
		 2);			/* Start with 3 points */
      avma = oavma;
  }
  avma = oldavma;
}

/*
 * Plot a dblPointList. Complete with axes, bounding box, etc.
 * We use two drawing rectangles: one for strings, another
 * for graphs.
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
 * Additional flags: PLOT_NO_AXE_X, PLOT_NO_AXE_Y, PLOT_NO_FRAME.
 */

static GEN
rectplothrawin(long stringrect, long drawrect, dblPointList *data,
               long flags, PARI_plot *WW)
{
  PARI_plot W;
  GEN res;
  dblPointList y,x;
  double xsml,xbig,ysml,ybig,tmp;
  long ltype=0, ltop=avma;
  long is,js,i,lm,rm,tm,bm,nc,nbpoints, w[2], wx[2], wy[2];

  w[0]=stringrect; w[1]=drawrect;
  if (!data) return cgetg(1,t_VEC);
  x=data[0]; nc=x.nb; xsml=x.xsml; xbig=x.xbig; ysml=x.ysml; ybig=x.ybig;
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

  if (WW) /* no rectwindow has been supplied ==> ps or screen output */
  {
    W = *WW;
    lm = W.fwidth*10; /* left margin   */
    rm = W.hunit-1; /* right margin  */
    tm = W.vunit-1; /* top margin    */
    bm = W.vunit+W.fheight-1; /* bottom margin */

    is = W.width - (lm+rm); js = W.height - (tm+bm);
    wx[0]=wy[0]=0; wx[1]=lm; wy[1]=tm;
  /*
   * Window size (W.width x W.height) is given in pixels, and
   * correct pixels are 0..w_width-1.
   *
   * On the other hand, rect functions work with windows whose pixel
   * range is [0,width].
   */

    initrect(stringrect, W.width-1, W.height-1);
    if (drawrect != stringrect) initrect(drawrect, is-1, js-1);
  }
  RHasGraph(check_rect(drawrect)) = 1;

  if (!(flags & PLOT_NO_RESCALE))
    rectscale0(drawrect, xsml, xbig, ysml, ybig);

  if (!(flags & PLOT_NO_FRAME))
  {
    rectlinetype(drawrect, -2); 		/* Frame. */
    current_color[drawrect]=BLACK;
    rectmove0(drawrect,xsml,ysml,0);
    rectbox0(drawrect,xbig,ybig,0);
  }

  if (!(flags & PLOT_NO_AXE_Y) && (xsml<=0 && xbig >=0))
  {
    rectlinetype(drawrect, -1); 		/* Axes. */
    current_color[drawrect]=BLUE;
    rectmove0(drawrect,0.0,ysml,0);
    rectline0(drawrect,0.0,ybig,0);
  }

  if (!(flags & PLOT_NO_AXE_X) && (ysml<=0 && ybig >=0))
  {
    rectlinetype(drawrect, -1); 		/* Axes. */
    current_color[drawrect]=BLUE;
    rectmove0(drawrect,xsml,0.0,0);
    rectline0(drawrect,xbig,0.0,0);
  }

  if (flags & PLOT_PARAMETRIC) i=0; else i=1;
  current_color[drawrect]=RED;
  for (; ltype < nc; )
  {
    if (nc>1)
    {
      if (ltype & 1) current_color[drawrect]=RED;
      else current_color[drawrect]=SIENNA;
    }
    if (flags & PLOT_PARAMETRIC) x=data[i++];

    y=data[i++]; nbpoints=y.nb;
    if ((flags & PLOT_POINTS_LINES) || (flags & PLOT_POINTS)) {
	rectlinetype(drawrect, rectpoint_itype + ltype); 	/* Graphs. */
	rectpointtype(drawrect, rectpoint_itype + ltype); 	/* Graphs. */
	rectpoints0(drawrect,x.d,y.d,nbpoints);
    }
    if ((flags & PLOT_POINTS_LINES) || !(flags & PLOT_POINTS)) {
	if (flags & PLOT_SPLINES) {
	    /* rectsplines will call us back with ltype == 0 */
	    int old = rectline_itype;

	    rectline_itype = rectline_itype + ltype;
	    rectsplines(drawrect,x.d,y.d,nbpoints,flags);	
	    rectline_itype = old;
	} else {
	    rectlinetype(drawrect, rectline_itype + ltype); 	/* Graphs. */
	    rectlines0(drawrect,x.d,y.d,nbpoints,0);	
	}
    }
    ltype++;				/* Graphs. */
  }
  for (i--; i>=0; i--) free(data[i].d);
  free(data);

  if (WW)
  {
    char c1[16],c2[16],c3[16],c4[16];

    sprintf(c1,"%.5g",ybig); sprintf(c2,"%.5g",ysml);
    sprintf(c3,"%.5g",xsml); sprintf(c4,"%.5g",xbig);

    rectlinetype(stringrect,-2); /* Frame */
    current_color[stringrect]=BLACK;
    put_string( stringrect, lm, 0, c1,
		RoSTdirRIGHT | RoSTdirHGAP | RoSTdirTOP);
    put_string(stringrect, lm, W.height - bm, c2,
		RoSTdirRIGHT | RoSTdirHGAP | RoSTdirVGAP);
    put_string(stringrect, lm, W.height - bm, c3,
		RoSTdirLEFT | RoSTdirTOP);
    put_string(stringrect, W.width - rm - 1, W.height - bm, c4,
		RoSTdirRIGHT | RoSTdirTOP);

    if (flags & PLOT_POSTSCRIPT)
      postdraw0(w,wx,wy,2);
    else
      rectdraw0(w,wx,wy,2, 0);

    killrect(drawrect); if (stringrect != drawrect) killrect(stringrect);
  }

  avma=ltop;
  res = cgetg(5,t_VEC);
  res[1]=(long)dbltor(xsml); res[2]=(long)dbltor(xbig);
  res[3]=(long)dbltor(ysml); res[4]=(long)dbltor(ybig);
  return res;
}

/*************************************************************************/
/*                                                                       */
/*                          HI-RES FUNCTIONS                             */
/*                                                                       */
/*************************************************************************/

GEN
rectploth(long drawrect,entree *ep,GEN a,GEN b,char *ch,
          long prec,ulong flags,long testpoints)
{
  dblPointList *pl=rectplothin(ep, a,b, ch, prec, flags,testpoints);
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
ploth0(long stringrect,long drawrect,entree *ep,GEN a,GEN b,char *ch,
             long prec,ulong flags,long testpoints)
{
  PARI_plot *output = init_output(flags);
  dblPointList *pl=rectplothin(ep, a,b, ch, prec, flags,testpoints);
  return rectplothrawin(stringrect,drawrect, pl, flags, output);
}

static GEN
plothraw0(long stringrect, long drawrect, GEN listx, GEN listy, long flags)
{
  PARI_plot *output = init_output(flags);
  long data[] = {evaltyp(t_VEC) | m_evallg(3), 0, 0};
  dblPointList *pl;

  data[1] = (long) listx;
  data[2] = (long) listy;
  pl=gtodblList(data,PLOT_PARAMETRIC);
  if (!pl) return cgetg(1,t_VEC);
  return rectplothrawin(stringrect,drawrect,pl,flags | PLOT_PARAMETRIC,output);
}

GEN
plothraw(GEN listx, GEN listy, long flags)
{
  flags=(flags)? 0: PLOT_POINTS;
  return plothraw0(STRINGRECT, DRAWRECT, listx, listy, flags);
}

GEN
ploth(entree *ep, GEN a, GEN b, char *ch, long prec,long flags,long numpoints)
{
  return ploth0(STRINGRECT, DRAWRECT, ep,a,b,ch,prec,flags,numpoints);
}

GEN
ploth2(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  return ploth0(STRINGRECT, DRAWRECT, ep,a,b,ch,prec,PLOT_PARAMETRIC,0);
}

GEN
plothmult(entree *ep, GEN a, GEN b, char *ch, long prec)
{
  return ploth0(STRINGRECT, DRAWRECT, ep,a,b,ch,prec,0,0);
}

GEN
postplothraw(GEN listx, GEN listy, long flags)
{
  flags=(flags)? 0: PLOT_POINTS;
  return plothraw0(STRINGRECT, DRAWRECT, listx, listy, flags|PLOT_POSTSCRIPT);
}

GEN
postploth(entree *ep, GEN a, GEN b, char *ch, long prec,long flags,
           long numpoints)
{
  return ploth0(STRINGRECT,DRAWRECT,ep,a,b,ch,prec,flags|PLOT_POSTSCRIPT,
                numpoints);
}

GEN
postploth2(entree *ep, GEN a, GEN b, char *ch, long prec,
           long numpoints)
{
  return ploth0(STRINGRECT,DRAWRECT,ep,a,b,ch,prec,
		PLOT_PARAMETRIC|PLOT_POSTSCRIPT,numpoints);
}

GEN
plothsizes()
{
  return plothsizes_flag(0);
}

GEN
plothsizes_flag(long flag)
{
  GEN vect = cgetg(1+6,t_VEC);
  int i;

  PARI_get_plot(0);
  for (i=1; i<=2; i++) vect[i]=lgeti(3);
  affsi(w_width,(GEN)vect[1]); affsi(w_height,(GEN)vect[2]);
  if (flag) {
    vect[3] = (long)dbltor(h_unit*1.0/w_width);
    vect[4] = (long)dbltor(v_unit*1.0/w_height);
    vect[5] = (long)dbltor(f_width*1.0/w_width);
    vect[6] = (long)dbltor(f_height*1.0/w_height);
  } else {
    for (; i <= 6; i++) vect[i]=lgeti(3);
    affsi(h_unit, (GEN)vect[3]); affsi(v_unit, (GEN)vect[4]);
    affsi(f_width,(GEN)vect[5]); affsi(f_height,(GEN)vect[6]);
  }
  return vect;
}	

/*************************************************************************/
/*                                                                       */
/*                         POSTSCRIPT OUTPUT                             */
/*                                                                       */
/*************************************************************************/

typedef struct spoint {
  int x,y; } SPoint;
typedef struct ssegment {
  int x1,y1,x2,y2; } SSegment;
typedef struct srectangle {
  int x,y,width,height; } SRectangle;

static void ps_point(FILE *psfile, int x, int y);
static void ps_line(FILE *psfile, int x1, int y1, int x2, int y2);
static void ps_rect(FILE *psfile, int x1, int y1, int x2, int y2);
static void ps_string(FILE *psfile, int x, int y, char *c, long dir);

#undef ISCR
#undef JSCR
#define ISCR 1120 /* 1400 en haute resolution */
#define JSCR 800  /* 1120 en haute resolution */

static void
PARI_get_psplot()
{
  pari_psplot.height = JSCR - 60;
  pari_psplot.width  = ISCR - 40;
  pari_psplot.fheight = 15;
  pari_psplot.fwidth = 6;
  pari_psplot.hunit = 5;
  pari_psplot.vunit = 5;
}

static void
gendraw(GEN list, long ps, long flag)
{
  long i,n,ne,*w,*x,*y;
  GEN x0,y0,win;

  if (typ(list) != t_VEC) err(talker,"not a vector in rectdraw");
  n = lg(list)-1;
  if (n%3) err(talker,"incorrect number of components in rectdraw");
  n = n/3; if (!n) return;
  w = (long*)gpmalloc(n*sizeof(long));
  x = (long*)gpmalloc(n*sizeof(long));
  y = (long*)gpmalloc(n*sizeof(long));
  if (flag)
    PARI_get_plot(0);
  for (i=0; i<n; i++)
  {
    win=(GEN)list[3*i+1]; x0=(GEN)list[3*i+2]; y0=(GEN)list[3*i+3];
    if (typ(win)!=t_INT || (!flag && (typ(x0)!=t_INT || typ(y0)!= t_INT)))
      err(talker, "not an integer type in rectdraw");
    if (flag) {
      double xd = gtodouble(x0), yd = gtodouble(y0);
      long xi, yi;

      xi = w_width - 1;  yi = w_height - 1;
      xi = xd*xi + 0.5;
      yi = yd*yi + 0.5;
      x[i] = xi; y[i] = yi;
    } else {
      x[i]=itos(x0); y[i]=itos(y0);
    }
    ne=itos(win); check_rect(ne);
    w[i]=ne;
  }
  if (ps) postdraw00(w,x,y,n,flag); else rectdraw0(w,x,y,n, 1);
  free(x); free(y); free(w);
}

void
postdraw(GEN list) { gendraw(list, 1, 0); }

void
rectdraw(GEN list) { gendraw(list, 0, 0); }

void
postdraw_flag(GEN list, long flag) { gendraw(list, 1, flag); }

void
rectdraw_flag(GEN list, long flag) { gendraw(list, 0, flag); }

static char*
zmalloc(size_t x)
{
  return x? gpmalloc(x): NULL;
}

void
postdraw0(long *w, long *x, long *y, long lw)
{
  postdraw00(w, x, y, lw, 0);
}

void
postdraw00(long *w, long *x, long *y, long lw, long scale)
{
  long *ptx,*pty,*numpoints,*numtexts,*xtexts,*ytexts,*dirtexts;
  RectObj *p1;
  PariRect *e;
  long i,j,x0,y0;
  long a,b,c,d,nd[ROt_MAX+1];
  char **texts;
  FILE *psfile;
  double xscale = 0.65, yscale = 0.65;
  long fontsize = 16, xtick = 5, ytick = 5;

  SPoint *points, **lines, *SLine;
  SSegment *seg;
  SRectangle *rect, SRec;

  if (scale) {
    double postxsize, postysize;

    PARI_get_psplot(); 
    postxsize = pari_psplot.width;
    postysize = pari_psplot.height;
    PARI_get_plot(0);
    xscale *= postxsize * 1.0/w_width;
    fontsize = fontsize/(postxsize * 1.0/w_width);
    yscale *= postysize * 1.0/w_height;
    xtick = h_unit;  ytick = v_unit;
  }
  psfile = fopen(current_psfile, "a");
  if (!psfile)
    err(openfiler,"postscript",current_psfile);

  for (i=0; i<=ROt_MAX; i++) nd[i]=0;

  for (i=0; i<lw; i++)
  {
    e = check_rect_init(w[i]); p1=RHead(e);
    while (p1)
    {
      if (RoType(p1) != ROt_MP) nd[RoType(p1)]++;
      else nd[ROt_PT]+=RoMPcnt(p1);
      p1=RoNext(p1);
    }
  }
  points=(SPoint*) zmalloc(nd[ROt_PT]*sizeof(SPoint));
  seg=(SSegment*) zmalloc(nd[ROt_LN]*sizeof(SSegment));
  rect=(SRectangle*) zmalloc(nd[ROt_BX]*sizeof(SRectangle));
  lines=(SPoint**) zmalloc(nd[ROt_ML]*sizeof(SPoint*));
  numpoints=(long*) zmalloc(nd[ROt_ML]*sizeof(long));
  texts=(char**) zmalloc(nd[ROt_ST]*sizeof(char*));
  numtexts=(long*) zmalloc(nd[ROt_ST]*sizeof(long));
  xtexts = (long*) zmalloc(nd[ROt_ST]*sizeof(long));
  ytexts = (long*) zmalloc(nd[ROt_ST]*sizeof(long));
  dirtexts = (long*) zmalloc(nd[ROt_ST]*sizeof(long));
  for (i=0; i<=ROt_MAX; i++) nd[i]=0;

  for (i=0; i<lw; i++)
  {
    e=rectgraph[w[i]]; p1=RHead(e); x0=x[i]; y0=y[i];
    while (p1)
    {
      switch(RoType(p1))
      {
	case ROt_PT:
	  points[nd[ROt_PT]].x=RoPTx(p1)+x0;
	  points[nd[ROt_PT]].y=RoPTy(p1)+y0;
	  nd[ROt_PT]++; break;
	case ROt_LN:
	  seg[nd[ROt_LN]].x1=RoLNx1(p1)+x0;
	  seg[nd[ROt_LN]].y1=RoLNy1(p1)+y0;
	  seg[nd[ROt_LN]].x2=RoLNx2(p1)+x0;
	  seg[nd[ROt_LN]].y2=RoLNy2(p1)+y0;
	  nd[ROt_LN]++; break;
	case ROt_BX:
	  a=rect[nd[ROt_BX]].x=RoBXx1(p1)+x0;
	  b=rect[nd[ROt_BX]].y=RoBXy1(p1)+y0;
	  rect[nd[ROt_BX]].width =RoBXx2(p1)+x0-a;
	  rect[nd[ROt_BX]].height=RoBXy2(p1)+y0-b;
	  nd[ROt_BX]++; break;
	case ROt_MP:
	  ptx=RoMPxs(p1); pty=RoMPys(p1);
	  for (j=0; j<RoMPcnt(p1); j++)
	  {
	    points[nd[ROt_PT]+j].x=ptx[j]+x0;
	    points[nd[ROt_PT]+j].y=pty[j]+y0;
	  }
	  nd[ROt_PT]+=RoMPcnt(p1); break;
	case ROt_ML:
	  ptx=RoMLxs(p1); pty=RoMLys(p1);
	  numpoints[nd[ROt_ML]]=RoMLcnt(p1);
	  lines[nd[ROt_ML]]=(SPoint*)gpmalloc(RoMLcnt(p1)*sizeof(SPoint));
	  for (j=0; j<RoMLcnt(p1); j++)
	  {
	    lines[nd[ROt_ML]][j].x=ptx[j]+x0;
	    lines[nd[ROt_ML]][j].y=pty[j]+y0;
	  }
	  nd[ROt_ML]++; break;
	case ROt_ST:
	  texts[nd[ROt_ST]]=RoSTs(p1);
	  numtexts[nd[ROt_ST]]=RoSTl(p1);
	  xtexts[nd[ROt_ST]]=RoSTx(p1)+x0;
	  ytexts[nd[ROt_ST]]=RoSTy(p1)+y0;
	  dirtexts[nd[ROt_ST]]=RoSTdir(p1);
	  nd[ROt_ST]++; break;
	default: break;
      }
      p1=RoNext(p1);
    }
  }
  /* Definitions taken from post terminal of Gnuplot. */
  fprintf(psfile,"%%!\n50 50 translate\n/Times-Roman findfont %ld scalefont setfont\n%g %g scale\n", fontsize, yscale,xscale);
  fprintf(psfile,"/Lshow { moveto 90 rotate show -90 rotate } def\n/Rshow { 3 -1 roll dup 4 1 roll stringwidth pop sub Lshow } def\n/Cshow { 3 -1 roll dup 4 1 roll stringwidth pop 2 div sub Lshow } def\n");
  fprintf(psfile,"/Xgap %ld def\n/Ygap %ld def\n", xtick, ytick);
  fprintf(psfile,"/Bbox { gsave newpath 0 0 moveto true charpath pathbbox grestore } def\n");
  fprintf(psfile,"/Height { Bbox 4 1 roll pop pop pop } def\n");
  fprintf(psfile,"/TopAt { 3 -1 roll dup 4 1 roll Height 3 -1 roll add exch } def\n");
  fprintf(psfile,"/VCenter { 3 -1 roll dup 4 1 roll Height 2 div 3 -1 roll add exch } def\n");
  fprintf(psfile,"/Tgap { exch Ygap add exch } def\n");
  fprintf(psfile,"/Bgap { exch Ygap sub exch } def\n");
  fprintf(psfile,"/Lgap { Xgap add } def\n");
  fprintf(psfile,"/Rgap { Xgap sub } def\n");

  for (i=0; i<nd[ROt_PT]; i++)
    ps_point(psfile,points[i].x,points[i].y);
  for (i=0; i<nd[ROt_LN]; i++)
    ps_line(psfile,seg[i].x1,seg[i].y1,seg[i].x2,seg[i].y2);
  for (i=0; i<nd[ROt_BX]; i++)
  {
    SRec=rect[i]; a=SRec.x; b=SRec.y; c=a+SRec.width;
    d=b+SRec.height; ps_rect(psfile,a,b,c,d);
  }
  for (i=0; i<nd[ROt_ML]; i++)
  {
    SLine=lines[i];
    for (j=0; j<numpoints[i]; j++)
    {
      if (!j) fprintf(psfile,"%d %d moveto\n",SLine[0].y,SLine[0].x);
      else fprintf(psfile,"%d %d lineto\n",SLine[j].y,SLine[j].x);
    }
  }
  for (i=0; i<nd[ROt_ST]; i++)
    ps_string(psfile,xtexts[i],ytexts[i],texts[i], dirtexts[i]);
  fprintf(psfile,"stroke showpage\n"); fclose(psfile);
#define xfree(pointer) if (pointer) free(pointer)
  xfree(points); xfree(seg); xfree(rect); xfree(numpoints);
  for (i=0; i<nd[ROt_ML]; i++) xfree(lines[i]);
  xfree(lines); xfree(texts); xfree(numtexts); xfree(xtexts); xfree(ytexts);
#undef xfree
}

static void
ps_point(FILE *psfile, int x, int y)
{
  fprintf(psfile,"%d %d moveto\n0 2 rlineto 2 0 rlineto 0 -2 rlineto closepath fill\n",y,x);
}

static void
ps_line(FILE *psfile, int x1, int y1, int x2, int y2)
{
  fprintf(psfile,"%d %d moveto\n%d %d lineto\n",y1,x1,y2,x2);
}

static void
ps_rect(FILE *psfile, int x1, int y1, int x2, int y2)
{
  fprintf(psfile,"%d %d moveto\n%d %d lineto\n%d %d lineto\n%d %d lineto\nclosepath\n",y1,x1,y1,x2,y2,x2,y2,x1);
}

static void
ps_string(FILE *psfile, int x, int y, char *s, long dir)
{
    if (strpbrk(s, "(\\)")) {
	fprintf(psfile,"(");
	while (*s) {
	    if ( *s=='(' || *s==')' || *s=='\\' )
		fputc('\\', psfile);
	    fputc(*s, psfile);
	    s++;
	}
    } else
	fprintf(psfile,"(%s", s);
    fprintf(psfile,") %d %d %s%s%s%sshow\n",
	    y, x,
	    ((dir & RoSTdirVGAP)
	     ? ((dir & RoSTdirVPOS_mask) == RoSTdirTOP ? "Tgap " : "Bgap ")
	     : ""),
	    ((dir & RoSTdirHGAP)
	     ? ((dir & RoSTdirHPOS_mask) == RoSTdirRIGHT ? "Rgap " : "Lgap ")
	     : ""),
	    ((dir & RoSTdirVPOS_mask) == RoSTdirBOTTOM ? ""
	     : (dir & RoSTdirVPOS_mask) == RoSTdirTOP ? "TopAt " : "VCenter "),
	    ((dir & RoSTdirHPOS_mask) == RoSTdirLEFT ? "L"
	     : ((dir & RoSTdirHPOS_mask) == RoSTdirRIGHT ? "R" : "C")));
}
