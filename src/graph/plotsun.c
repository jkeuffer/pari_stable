/*******************************************************************/
/*                                                                 */
/*                  HI-RES PLOT. SUNVIEW INTERFACE                 */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "rect.h"
#include <suntool/sunview.h>
#include <suntool/canvas.h>
#include <suntool/textsw.h>
#include <suntool/panel.h>

typedef struct spoint {int x,y;} SPoint;
typedef struct ssegment {int x1,y1,x2,y2;} SSegment;
typedef struct srectangle {int x,y,width,height;} SRectangle;

#define ISCR 1120 /* 1400 en haute resolution */
#define JSCR 800  /* 1120 en haute resolution */

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free)
{
  long *ptx,*pty,*numpoints,*numtexts,*xtexts,*ytexts;
  long n,i,j,x0,y0;
  long a,b,c,d,ne;
  long rcnt[ROt_MAX+1];
  char **texts;
  PariRect *e;
  RectObj *p1;

  Frame ecran;
  Canvas canevas;
  Pixwin *pw;
  Pixfont *font;
  SPoint *points, **lines, *SLine;
  SSegment *segments;
  SRectangle *rectangles, SRec;

  if (fork()) return;  /* parent process returns */

  /* child process goes on */
  freeall();  /* PARI stack isn't needed anymore, keep rectgraph */
  PARI_get_plot(1);

  rcnt[ROt_MV]=rcnt[ROt_PT]=rcnt[ROt_LN]=0;
  rcnt[ROt_BX]=rcnt[ROt_MP]=rcnt[ROt_ML]=0;
  rcnt[ROt_ST]=0;

  for(i=0;i<lw;i++)
  {
    e=rectgraph[w[i]]; p1=RHead(e);
    while(p1)
    {
      if(RoType(p1) != ROt_MP) rcnt[RoType(p1)]++;
      else rcnt[ROt_PT] += RoMPcnt(p1);
      p1=RoNext(p1);
    }
  }
  points=(SPoint*)gpmalloc(rcnt[ROt_PT]*sizeof(SPoint));
  segments=(SSegment*)gpmalloc(rcnt[ROt_LN]*sizeof(SSegment));
  rectangles=(SRectangle*)gpmalloc(rcnt[ROt_BX]*sizeof(SRectangle));
  lines=(SPoint**)gpmalloc(rcnt[ROt_ML]*sizeof(SPoint*));
  numpoints=(long*)gpmalloc(rcnt[ROt_ML]*sizeof(long));
  texts=(char**)gpmalloc(rcnt[ROt_ST]*sizeof(char*));
  numtexts=(long*)gpmalloc(rcnt[ROt_ST]*sizeof(long));
  xtexts=(long*)gpmalloc(rcnt[ROt_ST]*sizeof(long));
  ytexts=(long*)gpmalloc(rcnt[ROt_ST]*sizeof(long));
  rcnt[ROt_PT]=rcnt[ROt_LN]=rcnt[ROt_BX]=rcnt[ROt_ML]=rcnt[ROt_ST]=0;

  for(i=0;i<lw;i++)
  {
    e=rectgraph[w[i]];p1=RHead(e);x0=x[i];y0=y[i];
    while(p1)
    {
      switch(RoType(p1))
      {
	case ROt_PT:
	  points[rcnt[ROt_PT]].x=RoPTx(p1)+x0;
	  points[rcnt[ROt_PT]].y=RoPTy(p1)+y0;
	  rcnt[ROt_PT]++;break;
	case ROt_LN:
	  segments[rcnt[ROt_LN]].x1=RoLNx1(p1)+x0;
	  segments[rcnt[ROt_LN]].y1=RoLNy1(p1)+y0;
	  segments[rcnt[ROt_LN]].x2=RoLNx2(p1)+x0;
	  segments[rcnt[ROt_LN]].y2=RoLNy2(p1)+y0;
	  rcnt[ROt_LN]++;break;
	case ROt_BX:
	  a=rectangles[rcnt[ROt_BX]].x=RoBXx1(p1)+x0;
	  b=rectangles[rcnt[ROt_BX]].y=RoBXy1(p1)+y0;
	  rectangles[rcnt[ROt_BX]].width=RoBXx2(p1)+x0-a;
	  rectangles[rcnt[ROt_BX]].height=RoBXy2(p1)+y0-b;
	  rcnt[ROt_BX]++;break;
	case ROt_MP:
	  ptx=RoMPxs(p1);pty=RoMPys(p1);
	  for(j=0;j<RoMPcnt(p1);j++)
	  {
	    points[rcnt[ROt_PT]+j].x=ptx[j]+x0;
	    points[rcnt[ROt_PT]+j].y=pty[j]+y0;
	  }
	  rcnt[ROt_PT]+=RoMPcnt(p1);break;
	case ROt_ML:
	  ptx=RoMLxs(p1);pty=RoMLys(p1);
	  numpoints[rcnt[ROt_ML]]=RoMLcnt(p1);
	  lines[rcnt[ROt_ML]]=(SPoint*)gpmalloc(RoMLcnt(p1)*sizeof(SPoint));
	  for(j=0;j<RoMLcnt(p1);j++)
	  {
	    lines[rcnt[ROt_ML]][j].x=ptx[j]+x0;
	    lines[rcnt[ROt_ML]][j].y=pty[j]+y0;
	  }
	  rcnt[ROt_ML]++;break;
        case ROt_ST:
	  texts[rcnt[ROt_ST]]=RoSTs(p1); numtexts[rcnt[ROt_ST]]=RoSTl(p1);
	  xtexts[rcnt[ROt_ST]]=RoSTx(p1)+x0; ytexts[rcnt[ROt_ST]]=RoSTy(p1)+y0;
	  rcnt[ROt_ST]++;break;
	default: break;
      }
      p1=RoNext(p1);
    }
  }
  ecran=window_create(NULL,FRAME,FRAME_LABEL,"rectplot",
                      WIN_ERROR_MSG,"you must be in suntools",0);
  canevas=window_create(ecran,CANVAS,WIN_HEIGHT,JSCR, WIN_WIDTH,ISCR,0);
  window_fit(ecran);pw=canvas_pixwin(canevas);

  font=pw_pfsysopen();
  for(i=0;i<rcnt[ROt_PT];i++) pw_put(pw,points[i].x,points[i].y,1);
  for(i=0;i<rcnt[ROt_LN];i++)
    pw_vector(pw,segments[i].x1,segments[i].y1,
              segments[i].x2,segments[i].y2,PIX_SRC,1);
  for(i=0;i<rcnt[ROt_BX];i++)
  {
    SRec=rectangles[i];a=SRec.x;b=SRec.y;c=a+SRec.width;
    d=b+SRec.height;
    pw_vector(pw,a,b,c,b,PIX_SRC,1); pw_vector(pw,c,b,c,d,PIX_SRC,1);
    pw_vector(pw,a,d,c,d,PIX_SRC,1); pw_vector(pw,a,b,a,d,PIX_SRC,1);
  }
  for(i=0;i<rcnt[ROt_ML];i++)
  {
    SLine=lines[i];
    for(j=1;j<numpoints[i];j++)
      pw_vector(pw,SLine[j-1].x,SLine[j-1].y,SLine[j].x,SLine[j].y,PIX_SRC,1);
  }
  for(i=0;i<rcnt[ROt_ST];i++)
    for(j=0;texts[i][j];j++)
      pw_char(pw,xtexts[i]+9*j,ytexts[i],PIX_SRC|PIX_DST,font,texts[i][j]);

  window_main_loop(ecran);

  free(points);free(segments);free(rectangles);
  free(numpoints);for(i=0;i<rcnt[ROt_ML];i++) free(lines[i]);
  free(lines);free(texts);free(numtexts);free(xtexts);free(ytexts);
  if (do_free) { free(w); free(x); free(y); }
  free_graph(); exit(0);
}

void
PARI_get_plot(long fatal)
{
  if (pari_plot.init) return;

  w_width = ISCR; w_height = JSCR;
  f_height = 15; f_width = 9;
  h_unit = 5; v_unit = 5;
  pari_plot.init = 1;
}

long
term_set(char *s)
{
  return 1;
}

long
plot_outfile_set(char *s) { return 1; }

void
set_pointsize(double d) 
{
}
