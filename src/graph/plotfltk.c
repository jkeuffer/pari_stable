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
/////////////////////////////////////////////////////////////////////////////
//
//  High resolution plot using FLTK library
//  Bill Alombert 2003
//
//  Based on plotQt by Nils-Peter Skoruppa (www.countnumber.de)
/////////////////////////////////////////////////////////////////////////////
extern "C" {
#include "pari.h"
#include "rect.h"
    void rectdraw0(long *, long *, long *, long, long);
}

#include <FL/Fl.H>
#include <FL/Fl_Window.H>
#include <FL/fl_draw.H>

typedef struct Point_s {long x, y;} Point;
typedef struct Rectangle_s {long x, y, width, height;} Rectangle;
typedef struct Segment_s {long x1, y1, x2, y2;} Segment;
typedef char* String;

class Plotter: public Fl_Window {

public:
    //Plotter(int x, int y, int w, int h, const char
    //   *label = 0);
    Plotter( long *w, long *x, long *y, long lw, const char* name = 0);
    ~Plotter();

private:
    void alloc();
    void draw();
    int handle(int event);

private:
    long *my_w;                        // map into rectgraph indexes
    long *my_x;                        // x, y: array of x,y-coordinates of the
    long *my_y;                        // top left corners of the rectwindows
    long my_lw;                        // lw: number of rectwindows
    col_counter rcolcnt;
    long rcnt[ROt_MAX+1];
    Point *points[MAX_COLORS];
    Segment *seg[MAX_COLORS];
    Point **lines[MAX_COLORS];
    Rectangle *rec[MAX_COLORS];
    Point *textPos[MAX_COLORS];
    String *texts[MAX_COLORS];
    Fl_Color color[MAX_COLORS];
    long *numpoints[MAX_COLORS];
    long *numtexts[MAX_COLORS];
};

Fl_Color rgb_color(int R, int G, int B)
{ 
  return fl_color_cube(R*FL_NUM_RED/256, G*FL_NUM_GREEN/256,
         B*FL_NUM_BLUE/256);
}

Plotter::Plotter( long *w, long *x, long *y, long lw,
	     const char* name) 
        : Fl_Window(pari_plot.width, pari_plot.height, "PARI/GP")

{

    this->my_w=w; this->my_x=x; this->my_y=y; this->my_lw=lw;
    alloc();
    color[0]         = FL_WHITE;
    color[BLACK]     = FL_BLACK;
    color[BLUE]      = FL_BLUE;
    color[SIENNA]    = rgb_color( 160, 82, 45) ;
    color[RED]       = FL_RED;
    color[CORNSILK]  = rgb_color( 255, 248, 220);
    color[GREY]      = rgb_color( 127, 127, 127);
    color[GAINSBORO] = rgb_color( 220, 220, 220);
}

Plotter::~Plotter() {

    for( int col = 1; col < MAX_COLORS; col++) {
        delete[] points[col];
        delete[] seg[col];
	delete[] rec[col];
        for(int i=0;i<rcolcnt[col][ROt_ML];i++) delete lines[col][i];
        delete[] lines[col];
        delete[] texts[col];
        delete[] numpoints[col];
        delete[] numtexts[col];
    }
}

void DrawPoints(Point *points,long n)
{
  for(int i=0;i<n;i++)
    fl_point(points[i].x, points[i].y);
}

void DrawSegments(Segment *seg,long n)
{
  for(int i=0;i<n;i++)
    fl_line(seg[i].x1, seg[i].y1, seg[i].x2, seg[i].y2);
}

void DrawRectangles(Rectangle *rec, long n)
{
  for(int i=0;i<n;i++)
    fl_rect(rec[i].x,rec[i].y,rec[i].width,rec[i].height);
}

void DrawLines(Point *lines, long n)
{
  for(int i=1;i<n;i++)
    fl_line(lines[i-1].x, lines[i-1].y, lines[i].x, lines[i].y);
}

void DrawString(Point textPos, String text, long n)
{
  fl_draw(text,n,textPos.x,textPos.y);
}

void Plotter::draw() 
{
  long shift;
  long j;
  long hjust, vjust, hgap, vgap, hgapsize, vgapsize;
  long *w=my_w;                        // map into rectgraph indexes
  long *x=my_x;                        // x, y: array of x,y-coorinates of the
  long *y=my_y;                        //   top left corners of the rectwindows
  long lw=my_lw;                       // lw: number of rectwindows
  long *c;
  long col;

  double xs = double(this->w())/pari_plot.width;
  double ys = double(this->h())/pari_plot.height;

  for( int col = 1; col < MAX_COLORS; col++) {
    c = rcolcnt[col];
    c[ROt_PT]=c[ROt_LN]=c[ROt_BX]=c[ROt_ML]=c[ROt_ST]=0;
  }
  hgapsize = h_unit;  vgapsize = v_unit;
  for(int i=0; i<lw; i++)
  {
    PariRect *e=rectgraph[w[i]];
    RectObj *p1=RHead(e);
    long x0=x[i],y0=y[i];
    while(p1)
    {
      col=RoCol(p1); c=rcolcnt[col];
      switch(RoType(p1))
      {
      case ROt_PT:
        points[col][c[ROt_PT]].x = DTOL((RoPTx(p1)+x0)*xs);
        points[col][c[ROt_PT]].y = DTOL((RoPTy(p1)+y0)*ys);
        c[ROt_PT]++;break;
      case ROt_LN:
        seg[col][c[ROt_LN]].x1 = DTOL((RoLNx1(p1)+x0)*xs);
        seg[col][c[ROt_LN]].y1 = DTOL((RoLNy1(p1)+y0)*ys);
        seg[col][c[ROt_LN]].x2 = DTOL((RoLNx2(p1)+x0)*xs);
        seg[col][c[ROt_LN]].y2 = DTOL((RoLNy2(p1)+y0)*ys);
        c[ROt_LN]++;break;
      case ROt_BX:
        rec[col][c[ROt_BX]].x = DTOL((RoBXx1(p1)+x0)*xs);
        rec[col][c[ROt_BX]].y = DTOL((RoBXy1(p1)+y0)*ys);
        rec[col][c[ROt_BX]].width = DTOL((RoBXx2(p1)-RoBXx1(p1))*xs);
        rec[col][c[ROt_BX]].height = DTOL((RoBXy2(p1)-RoBXy1(p1))*ys);
        c[ROt_BX]++;break;
      case ROt_MP:
        {
          double *ptx = RoMPxs(p1), *pty = RoMPys(p1);
          for(int j=0;j<RoMPcnt(p1);j++)
          {
            points[col][c[ROt_PT]+j].x = DTOL((ptx[j]+x0)*xs);
            points[col][c[ROt_PT]+j].y = DTOL((pty[j]+y0)*ys);
          }
          c[ROt_PT]+=RoMPcnt(p1);
          break;
        }
      case ROt_ML:
        {
          double *ptx=RoMLxs(p1), *pty=RoMLys(p1);
          numpoints[col][c[ROt_ML]] = RoMLcnt(p1);
          lines[col][c[ROt_ML]] = new Point[RoMLcnt(p1)];
          for(j=0;j<RoMLcnt(p1);j++)
          {
            lines[col][c[ROt_ML]][j].x = DTOL((ptx[j]+x0)*xs);
            lines[col][c[ROt_ML]][j].y = DTOL((pty[j]+y0)*ys);
          }
          c[ROt_ML]++;break;
        }
      case ROt_ST:
        hjust = RoSTdir(p1) & RoSTdirHPOS_mask;
        vjust = RoSTdir(p1) & RoSTdirVPOS_mask;
        hgap = RoSTdir(p1) & RoSTdirHGAP;
        if (hgap)
          hgap = (hjust == RoSTdirLEFT) ? hgapsize : -hgapsize;
          vgap = RoSTdir(p1) & RoSTdirVGAP;
          if (vgap)
            vgap = (vjust == RoSTdirBOTTOM) ? 2*vgapsize : -2*vgapsize;
          if (vjust != RoSTdirBOTTOM)
            vgap -= ((vjust == RoSTdirTOP) ? 2 : 1)*(f_height - 1);
          texts[col][c[ROt_ST]]=RoSTs(p1);
          numtexts[col][c[ROt_ST]]=RoSTl(p1);
          shift = (hjust == RoSTdirLEFT ? 0 :
              (hjust == RoSTdirRIGHT ? 2 : 1));
          textPos[col][c[ROt_ST]].x
            = DTOL(( RoSTx(p1) + x0 + hgap
                  - (strlen(RoSTs(p1)) * pari_plot.fwidth
                    * shift)/2)*xs);
          textPos[col][c[ROt_ST]].y = DTOL((RoSTy(p1)+y0-vgap/2)*ys);
          c[ROt_ST]++;break;
        default: break;
        }
        p1=RoNext(p1);
      }
    }
    fl_font(FL_COURIER, int(pari_plot.fheight * xs));
    fl_color(FL_WHITE); // transparent window on Windows otherwise
    fl_rectf(0, 0, this->w(), this->h());
    for(col=1; col<MAX_COLORS; col++)
    {
      c = rcolcnt[col];
      fl_color(color[col]);
      if(c[ROt_PT]) DrawPoints(points[col],c[ROt_PT]);
      if(c[ROt_LN]) DrawSegments(seg[col],c[ROt_LN]);
      if(c[ROt_BX]) DrawRectangles(rec[col],c[ROt_BX]);
      for(long i=0;i<c[ROt_ML];i++)
        DrawLines(lines[col][i],numpoints[col][i]);
      for(long i=0;i<c[ROt_ST];i++)
        DrawString(textPos[col][i],texts[col][i],numtexts[col][i]);
      c[ROt_PT]=c[ROt_LN]=c[ROt_BX]=c[ROt_ML]=c[ROt_ST]=0;
    }
}

void Plotter::alloc() {
    long *c;
    plot_count(my_w, my_lw, rcolcnt);
    for (int col = 1; col<MAX_COLORS; col++) {
	c = rcolcnt[col];
	points[col]=new Point[c[ROt_PT]];
	seg[col] = new Segment[c[ROt_LN]];
	rec[col] = new Rectangle[c[ROt_BX]];
        lines[col] = new (Point*)[c[ROt_ML]];
	textPos[col] = new Point[c[ROt_ST]];
	texts[col] = new String[c[ROt_ST]];
        numpoints[col] = new long[c[ROt_ST]];
        numtexts [col] = new long[c[ROt_ST]];
    }
}

int Plotter::handle(int event)
{
  switch(event) 
  {
  case FL_PUSH:
    switch(Fl::event_button())
    {
    case 1:
     exit(0);
    case 2:
     {
       static int flag=0;
       static int my_x;
       static int my_y;
       static int my_w;
       static int my_h;
       flag=1-flag;
       if (flag)
       {
         my_x=this->x();
         my_y=this->y();
         my_w=this->w();
         my_h=this->h();
         this->fullscreen();
       }
       else
       {
         this->fullscreen_off(my_x,my_y,my_w,my_h);
         this->size_range(1,1);
       }
       return 1;
     }
    }
  default:
    return 0;
  }
}

//
// Implementation of the four architecture-dependent functions
// (from rect.h) requested by pari's plotting routines
//

void
rectdraw0(long *w, long *x, long *y, long lw, long do_free)
{
    if (fork()) return;  // parent process returns
    
    //
    // child process goes on
    //
    os_signal(SIGPIPE, SIG_IGN);
    os_signal(SIGSEGV, SIG_IGN);
    os_signal(SIGBUS, SIG_IGN);

    freeall();  // PARI stack isn't needed anymore, keep rectgraph
    PARI_get_plot(1);

    Plotter *win = new Plotter( w, x, y, lw);
    Fl::visual(FL_DOUBLE|FL_INDEX);
    win->size_range(1,1);
    win->box(FL_FLAT_BOX);
    win->end();
    win->show();
    Fl::run();
    if (do_free) { free(w); free(x); free(y); }
    exit( 0);
}

void
PARI_get_plot(long f)
/* This function initialises the structure rect.h: pari_plot */
{
    (void)f;
    if (pari_plot.init) return;      // pari_plot is already set
    pari_plot.width   = 400;         // width and
    pari_plot.height  = 300;         //  height of plot window
    pari_plot.hunit   = 3;           // 
    pari_plot.vunit   = 3;           //
    pari_plot.fwidth  = 6;           // font width
    pari_plot.fheight = 9;           //   and height
    pari_plot.init    = 1;           // flag: pari_plot is set now!
}

long
term_set(char *s) { (void)s; return 1; }

long
plot_outfile_set(char *s) {
    
//    Plotter::setPlotFile( s);
    (void)s; return 1;
}

void
set_pointsize(double d) { (void)d; }
