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
//  High resolution plot using Trolltech's Qt library
//
//  You may possibly want to use this file with a "Qt Free Edition"
//  which is distributed under the terms of the Q PUBLIC LICENSE (QPL),
//  or with a "Qt/Embedded Free Edition" which is
//  distributed under the terms of the GNU General Public License (GPL).
//  Please check http://www.trolltech.com for details.
//
//                            ---Nils-Peter Skoruppa (www.countnumber.de)
/////////////////////////////////////////////////////////////////////////////
extern "C" {
#include "pari.h"
#include "rect.h"
    void rectdraw0(long *, long *, long *, long, long);
}

#ifdef __QPE__
#include <qpeapplication.h>
#else
#include <qapplication.h>
#endif
#include <qwidget.h>
#include <qpainter.h>
#include <qarray.h>
#include <qpoint.h>
#include <qrect.h>
#include <qcolor.h>
#include <qpixmap.h>
#include <qimage.h>


class Plotter: public QWidget {

#ifdef __FANCY_WIN__
     Q_OBJECT

signals:
    void clicked();

protected:
    void mouseReleaseEvent( QMouseEvent*);
#endif

public:
    Plotter( long *w, long *x, long *y, long lw,
	     QWidget* parent = 0, const char* name = 0, WFlags fl = 0);
    ~Plotter();
    void save( const QString& s = *plotFile + ".xpm",//QString("pariplot.xpm"),
	       const QString& f = QString( "XPM"));

protected:
    void paintEvent( QPaintEvent *);
    void resizeEvent ( QResizeEvent *);
#ifndef __FANCY_WIN__
    void keyPressEvent( QKeyEvent *);
#endif

private:
    void alloc();
    void plot();

private:
    long *w;                           // map into rectgraph indexes
    long *x;                           // x, y: array of x,y-coorinates of the
    long *y;                           //   top left corners of the rectwindows
    long lw;                           // lw: number of rectwindows
    col_counter rcolcnt;
    QPointArray _points[MAX_COLORS];
    QPointArray _seg[MAX_COLORS];
    QPointArray *_lines[MAX_COLORS];
    QRect *_rec[MAX_COLORS];
    QPointArray _textPos[MAX_COLORS];
    QString *_texts[MAX_COLORS];
    QColor color[MAX_COLORS];
    QFont font;
    static QString *plotFile;

// public:
//     static void setPlotFile( const char *);
};


QString *Plotter::plotFile = new QString( "pariplot");


Plotter::Plotter( long *w, long *x, long *y, long lw,
		  QWidget* parent,  const char* name, WFlags fl)
    : QWidget( parent, name, fl), font( "lucida", 9) {

    this->w=w; this->x=x; this->y=y; this->lw=lw;
    alloc();
#ifndef __FANCY_WIN__
    this->resize( pari_plot.width, pari_plot.height);
    this->setCaption( "Pari QtPlot");
#endif
    this->setBackgroundColor( white);
    this->setFont( font);
    // defaults as in plotX.c (cf. rgb.txt in a X11 system)
    color[0]         = white;
    color[BLACK]     = black;
    color[BLUE]      = blue;
    color[SIENNA]    = QColor( 160, 82, 45) ;
    color[RED]       = red;
    color[CORNSILK]  = QColor( 255, 248, 220);
    color[GREY]      = gray;
    color[GAINSBORO] = QColor( 220, 220, 220);
}


Plotter::~Plotter() {

    for( int col = 1; col < MAX_COLORS; col++) {
	delete[] _rec[col];
	delete[] _lines[col];
	delete[] _texts[col];
    }
}


// void Plotter::setPlotFile( const char *s) {

//     delete Plotter::plotFile;
//     Plotter::plotFile = new QString( s);
// }


void Plotter::save( const QString& s, const QString& f){

    QPixmap pm( this->width(), this->height());
    QPainter p;

    p.begin( &pm, this);
    p.fillRect( 0, 0, pm.width(), pm.height(), white);
    long *c;
    for( int col = 1; col < MAX_COLORS; col++) {
	c = rcolcnt[col];
	p.setPen( color[col]);
	if( _points[col].size()) p.drawPoints( _points[col]);
	if( _seg[col].size()) p.drawLineSegments( _seg[col]);
	for( int i = 0; i < c[ROt_BX]; i++) p.drawRect( _rec[col][i]);
	for( int i = 0; i < c[ROt_ML]; i++) p.drawPolyline( _lines[col][i]);
	for( int i = 0; i < c[ROt_ST]; i++)
	    p.drawText ( _textPos[col].point(i), _texts[col][i]);
    }
    p.end();

    // supported formats in qt2: BMP, JPEG, PNG, PNM, XBM, XPM ; PNG is broken
    pm.save( s, f);
}


void Plotter::paintEvent( QPaintEvent *) {

    QPainter p;
    p.begin( this);
    long *c;
    for( int col = 1; col < MAX_COLORS; col++) {
	c = rcolcnt[col];
	p.setPen( color[col]);
	if( _points[col].size()) p.drawPoints( _points[col]);
	if( _seg[col].size()) p.drawLineSegments( _seg[col]);
	for( int i = 0; i < c[ROt_BX]; i++) p.drawRect( _rec[col][i]);
 	for( int i = 0; i < c[ROt_ML]; i++) p.drawPolyline( _lines[col][i]);
 	for( int i = 0; i < c[ROt_ST]; i++)
	    p.drawText ( _textPos[col].point(i), _texts[col][i]);
    }
    p.end();
}


void Plotter::resizeEvent( QResizeEvent *) {

    this->plot();
}


#ifndef __FANCY_WIN__
void Plotter::keyPressEvent( QKeyEvent *e) {

    switch ( tolower( e->ascii())) {
        case 's':
	    save();
	    this->setCaption( "Pari QtPlot: " + *plotFile);
            break;
    }
}
#endif


#ifdef __FANCY_WIN__
void Plotter::mouseReleaseEvent( QMouseEvent*) {

    emit clicked();
}
#endif


void Plotter::plot() {

    PariRect *e;
    RectObj *p1;
    long col, x0, y0;
    long *c;

    double xs = double(this->width())/pari_plot.width,
	ys = double(this->height())/pari_plot.height;

    for( int col = 1; col < MAX_COLORS; col++) {
	c = rcolcnt[col];
	c[ROt_PT]=c[ROt_LN]=c[ROt_BX]=c[ROt_ML]=c[ROt_ST]=0;
    }

    for( int i = 0; i < lw; i++) {
	e = rectgraph[w[i]]; p1 = RHead( e); x0 = x[i]; y0 = y[i];
	while(p1) {
	    col = RoCol( p1); c = rcolcnt[col];
	    switch( RoType( p1)) {
		case ROt_PT:
		    _points[col].setPoint( c[ROt_PT],
					   DTOL((RoPTx(p1)+x0)*xs),
					   DTOL((RoPTy(p1)+y0)*ys));
		    c[ROt_PT]++;
		    break;
		case ROt_LN:
		    _seg[col].setPoint( 2*c[ROt_LN],
					DTOL((RoLNx1(p1)+x0)*xs),
					DTOL((RoLNy1(p1)+y0)*ys));
		    _seg[col].setPoint( 2*c[ROt_LN] + 1,
					DTOL((RoLNx2(p1)+x0)*xs),
					DTOL((RoLNy2(p1)+y0)*ys));
		    c[ROt_LN]++;
		    break;
		case ROt_BX:
		    _rec[col][c[ROt_BX]].setX( DTOL((RoBXx1(p1)+x0)*xs));
		    _rec[col][c[ROt_BX]].setY( DTOL((RoBXy1(p1)+y0)*ys));
		    _rec[col][c[ROt_BX]].setWidth(
			DTOL((RoBXx2(p1)-RoBXx1(p1))*xs));
		    _rec[col][c[ROt_BX]].setHeight(
			DTOL((RoBXy2(p1)-RoBXy1(p1))*ys));
		    c[ROt_BX]++;
		    break;
		case ROt_MP:
		    double *ptx, *pty;
		    ptx = RoMPxs(p1), pty = RoMPys(p1);
		    for( int j = 0; j < RoMPcnt(p1); j++) {
			_points[col].setPoint( c[ROt_PT]+j,
					       DTOL((ptx[j]+x0)*xs),
					       DTOL((pty[j]+y0)*ys));
		    }
		    c[ROt_PT]+=RoMPcnt(p1);
		    break;
		case ROt_ML:
		    // double *ptx, *pty;
		    ptx=RoMLxs(p1); pty=RoMLys(p1);
		    _lines[col][c[ROt_ML]].resize( RoMLcnt(p1));
		    for( int j = 0; j < RoMLcnt(p1); j++) 
			_lines[col][c[ROt_ML]].setPoint( j,
							 DTOL((ptx[j]+x0)*xs),
							 DTOL((pty[j]+y0)*ys));
		    c[ROt_ML]++;
		    break;
		case ROt_ST:
 		    _texts[col][c[ROt_ST]] = QString( RoSTs(p1));

		    long hjust, vjust, hgap, vgap, hgapsize, vgapsize, shift;

		    hjust = RoSTdir(p1) & RoSTdirHPOS_mask;
		    vjust = RoSTdir(p1) & RoSTdirVPOS_mask;
		    hgap = RoSTdir(p1) & RoSTdirHGAP;
		    hgapsize = pari_plot.hunit;  vgapsize = pari_plot.vunit;
		    if (hgap)
			hgap = (hjust == RoSTdirLEFT) ? hgapsize : -hgapsize;
		    vgap = RoSTdir(p1) & RoSTdirVGAP;
		    if (vgap)
			vgap = (vjust == RoSTdirBOTTOM) ? 2*vgapsize : -2*vgapsize;
		    if (vjust != RoSTdirBOTTOM)
			vgap -= ((vjust == RoSTdirTOP) ? 2 : 1)*(pari_plot.fheight - 1);
		    shift = (hjust == RoSTdirLEFT ? 0 :
			     (hjust == RoSTdirRIGHT ? 2 : 1));

		    _textPos[col].setPoint( c[ROt_ST],
					    DTOL(( RoSTx(p1) + x0 + hgap
						   - (strlen(RoSTs(p1)) * pari_plot.fwidth
						      * shift)/2)*xs),
					    DTOL((RoSTy(p1)+y0-vgap/2)*ys));
 		    c[ROt_ST]++;
		    break;
		default:
		    break;
	    }
	    p1 = RoNext( p1);
	}
    }
}


void Plotter::alloc() {
    long *c;
    plot_count(w, lw, rcolcnt);
    for (int col = 1; col<MAX_COLORS; col++) {
	c = rcolcnt[col];
	_points[col].resize( c[ROt_PT]);
	_seg[col].resize( 2*c[ROt_LN]);
	_rec[col] = new QRect[c[ROt_BX]];
	_lines[col] = new QPointArray[c[ROt_ML]];
	_textPos[col].resize( c[ROt_ST]);
	_texts[col] = new QString[c[ROt_ST]];
    }
}



#ifdef __FANCY_WIN__
//
// The envelope for an instance of plotter
//


#include <qmainwindow.h>
#include <qpopupmenu.h>
#include <qmenubar.h>
#include <qtoolbar.h>
#include <qaction.h>
#include <qfiledialog.h>
#include <qmessagebox.h> 
#include <qfile.h> 
#include <qstatusbar.h>
#include <qimage.h>
#include <qstrlist.h>
#include <qlabel.h>
#include <qspinbox.h>
#include <qlayout.h>


/* XPM */
static const char * const fullscreen_xpm[] = {
"14 14 2 1",
" 	c None",
".	c #000000",
"..............",
".     ..     .",
".     ..     .",
".    ....    .",
".     ..     .",
".  .  ..  .  .",
"..............",
"..............",
".  .  ..  .  .",
".     ..     .",
".    ....    .",
".     ..     .",
".     ..     .",
".............."}; 


class SaveAsDialog: public
#ifdef __QPE__
//QDialog
#else
QFileDialog
#endif
{

    Q_OBJECT

public:
    SaveAsDialog( const QString & c = QString::null,
		  const QString & s = QString::null, int w = 0, int h = 0,
		  QWidget *parent = 0, const char *name = 0, WFlags f = 0);
    ~SaveAsDialog();
#ifdef __QPE__
    QString selectedFile() { return nameW->text();}
#endif
    int picWidth() { return widthW->value();}
    int picHeight() { return heightW->value();}

private:
    QLineEdit *nameW;
    QSpinBox *widthW, *heightW;

};


SaveAsDialog::SaveAsDialog( const QString & c, const QString & s, int w, int h,
			    QWidget *parent, const char *name, WFlags f)
#ifdef __QPE__
    // simplistic dialog in case of QPE ( fancy alternative: class FileSelector)

    : QDialog( parent, name, TRUE, f) {

    if( c) this->setCaption( c);
    nameW = new QLineEdit( this);
    if( s) nameW->setText( s);
    widthW = new QSpinBox( 1, 65536, 1, this);
    if( w > 0) widthW->setValue( w);
    heightW = new QSpinBox( 1, 65536, 1, this);
    if( h > 0) heightW->setValue( h);

    QVBoxLayout *top = new QVBoxLayout( this, 10);
    QGridLayout *contents = new QGridLayout( 3, 2);

    top->addLayout( contents);

    QLabel *l;
    l = new QLabel( nameW, "Name : ", this);
    l->setAlignment( AlignRight | AlignVCenter);
    contents->addWidget( l, 0, 0);
    contents->addWidget( nameW, 0, 1);
    l = new QLabel( widthW, "Width : ", this);
    l->setAlignment( AlignRight | AlignVCenter);
    contents->addWidget( l, 1, 0);
    contents->addWidget( widthW, 1, 1);
    l = new QLabel( heightW, "Height : ", this);
    l->setAlignment( AlignRight | AlignVCenter);
    contents->addWidget( l, 2, 0);
    contents->addWidget( heightW, 2, 1);

    top->activate();
    this->resize( 160, this->height()); // hack!!!
#else
    : QFileDialog( parent, name, TRUE) {

    if( c) this->setFilters( c);
    if( s) this->setSelection( s);

    QLabel *l;
    QWidget *wt = new QWidget( this);
    QHBoxLayout *spinBoxes = new QHBoxLayout( wt, 5);
    widthW = new QSpinBox( 1, 65536, 1, wt);
    l  = new QLabel( widthW, "&width ", wt);
    spinBoxes->addWidget( l);
    spinBoxes->addWidget( widthW);
    if( w > 0) widthW->setValue( w);
    heightW = new QSpinBox( 1, 65536, 1, wt);
    spinBoxes->addSpacing(10);
    l  = new QLabel( heightW, "&height ", wt);
    l->setAlignment( AlignRight | AlignVCenter);
    spinBoxes->addWidget( l);
    spinBoxes->addWidget( heightW);
    if( h > 0) heightW->setValue( h);
    l = new QLabel( "Resolution:", this);
    QFileDialog::addWidgets( l, wt, 0);
#endif
}


SaveAsDialog::~SaveAsDialog() {
}



class PlotWindow: public QMainWindow {

     Q_OBJECT

public:
    PlotWindow( long *w, long *x, long *y, long lw,
		QWidget* parent = 0, const char* name = 0, WFlags fl = 0);
    ~PlotWindow();

#ifndef __QPE__
protected:
    void resizeEvent( QResizeEvent *);
#endif

private slots:
    void fullScreen();
    void normalView();
    void save();
    void save( int);

private:
    static const QStrList file_formats;
    Plotter *plr;
    QString saveFileName;
    int saveFileFormat;
#ifndef __QPE__
    QLabel *res;
#endif
};


const QStrList PlotWindow::file_formats = QImage::outputFormats();


PlotWindow::PlotWindow( long *w, long *x, long *y, long lw,
			QWidget* parent, const char* name, WFlags fl)
    : QMainWindow( parent, name, fl),
      saveFileName( "pariplot"), saveFileFormat( 0) {

    this->setCaption( "Pari QtPlot");

#ifdef __QPE__
    QToolBar *toolBar = new QToolBar( this);
    QMenuBar *menuBar = new QMenuBar( toolBar);
    toolBar->setHorizontalStretchable( TRUE);
    this->setToolBarsMovable( FALSE);
#else
    QMenuBar *menuBar = this->menuBar();
    menuBar->setFrameStyle( QFrame::Panel | QFrame::Raised);
#endif

    // Setting up the File and View menu
    QPopupMenu *format = new QPopupMenu( this);
    for( uint i = 0; i < file_formats.count(); i++) {
	format->insertItem( QString( QStrList(file_formats).at(i)) + " ...",
			    this, SLOT( save( int)), 0, i);
	if( 0 == QString( QStrList(file_formats).at(i)).compare( "PNG"))
	    format->setItemEnabled( i, FALSE); // PNG seems to be broken
    }
    QPopupMenu *file = new QPopupMenu( this);
    CHECK_PTR( file );
    file->insertItem( "&Save", this, SLOT( save()), CTRL+Key_S);
    file->insertItem( "Save &as", format);
    file->insertSeparator();
    file->insertItem( "&Close", this, SLOT(close()), CTRL+Key_C);
    menuBar->insertItem( "&File", file );

#ifndef __QPE__
    QPopupMenu *view = new QPopupMenu( this);
    menuBar->insertItem( "&View", view);
#endif
    // Setting up the Fullscreen action
    QAction *a = new QAction( "use full screen",
			      QPixmap( (const char ** )fullscreen_xpm),
			      "&Fullscreen", CTRL+Key_F, this);
    connect( a, SIGNAL( activated()), this, SLOT( fullScreen()));
#ifdef __QPE__
    a->addTo( toolBar);
#else
    a->addTo( view);
#endif

    // Setting up an instance of plotter
    plr = new Plotter( w, x, y, lw, this);
    connect( plr, SIGNAL(clicked()), this, SLOT( normalView()));
    this->setCentralWidget( plr);

#ifndef __QPE__
    this->resize( pari_plot.width,
		  pari_plot.height + 25);
    res = new QLabel( statusBar());
    statusBar()->addWidget( res);
#endif
}


PlotWindow::~PlotWindow() {
}


#ifndef __QPE__
void PlotWindow::resizeEvent( QResizeEvent *e) {
    
    QMainWindow::resizeEvent( e);
    res->setText( QString( "Resolution: ") +
		  QString::number( plr->width()) + "x" +
		  QString::number( plr->height()));
    res->setFixedSize( res->sizeHint());
}
#endif


void PlotWindow::fullScreen() {

    if ( plr->parentWidget()) {
	plr->reparent( 0, WStyle_Tool | WStyle_Customize | WStyle_StaysOnTop,
		      QPoint( 0, 0), FALSE);
	plr->resize( qApp->desktop()->width(), qApp->desktop()->height());
	plr->show();
    }
}


void PlotWindow::normalView() {

    if ( !plr->parentWidget()) {
	plr->reparent( this, 0, QPoint(0,0), FALSE);
	this->setCentralWidget( plr);
	plr->show();
    }
}


void PlotWindow::save() {

    QString ff = QString( QStrList(file_formats).at( saveFileFormat));
    QString fn = saveFileName + "." + ff.lower();
    plr->save( fn, ff);
    this->setCaption( QString( "Pari QtPlot:") + fn);
#ifndef __QPE__
    statusBar()->message( QString( "File %1 saved" ).arg( fn), 2000 );
#endif
}


void PlotWindow::save( int id) {

    QString ff( QStrList(file_formats).at( id));
#ifdef __QPE__
    QString s( "Save as");
#else
    QString s( ff + " (*." + ff.lower() +");;All (*)");
#endif
    SaveAsDialog d( s, saveFileName + "." + ff.lower(),
		    plr->width(), plr->height());
    if( QDialog::Rejected == d.exec()) return;
    QString fn = d.selectedFile();
    if ( !fn.isEmpty()) {
	if( QFile( fn).exists() &&
	    QMessageBox::warning(
		this, this->caption(),
		QString( "A file named\n\"") + fn
		+ QString( "\"\nalready exists\n"
			   "Should this file be overwritten ?\n\n"),
		"&Overwrite", "&Cancel"))  return;
	saveFileName = fn;
	int p;
	if( (p = saveFileName.findRev( "." + ff, -1, FALSE)) >=0)
	    saveFileName.truncate( p);
	saveFileFormat = id;
	int old_w = plr->width(), old_h = plr->height();
	int w = d.picWidth(), h = d.picHeight();
	if( w != old_w ||  h != old_h) {
	    plr->resize( w, h);
	    save();
	    plr->resize( old_w, old_h);
	} else
	    save();
    }
}


#include "plotQt.moc.cpp"
#endif // __FANCY_WIN__



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

    freeall();  // PARI stack isn't needed anymore, keep rectgraph
    PARI_get_plot(1);

    // launch Qt window
    int argc = 1; char *argv[] = { "gp", "-qws"}; // set argc = 2 for cross
                                                  // development using qvfb
#ifdef __QPE__
    QPEApplication
#else
    QApplication
#endif
	a( argc, argv);
#ifdef __FANCY_WIN__
    PlotWindow *win = new PlotWindow(w, x, y, lw);
#else
    Plotter *win = new Plotter( w, x, y, lw);
#endif
#ifdef __QPE__
    a.showMainWidget( win);
#else
    a.setMainWidget( win);
    win->show();
#endif
    a.exec();
    if (do_free) { free(w); free(x); free(y); }
    exit( 0);
}

void
PARI_get_plot(long f)
/* This function initialises the structure rect.h: pari_plot */
{
    (void)f;
    if (pari_plot.init) return;      // pari_plot is already set
#ifdef __QPE__
    pari_plot.width   = 240;         // width and
    pari_plot.height  = 320;         //  height of plot window
#else
    pari_plot.width   = 400;         // width and
    pari_plot.height  = 300;         //  height of plot window
#endif
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
