/*******************************************************************/
/*                                                                 */
/*        SOME GP FUNCTION THAT MAY BE USEFUL OUTSIDE OF IT        */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#ifdef macintosh
#  include "rect.h"
#  include "anal.h"
#else
#  include "../graph/rect.h"
#  include "../language/anal.h"
#endif

void kill0(entree *ep);

void
addhelp(entree *ep, char *s)
{
  if (ep->help && ! EpSTATIC(ep)) free(ep->help);
  ep->help = pari_strdup(s);
}

#ifdef HAS_DLOPEN
#include <dlfcn.h>
void 
install0(char *name, char *code, char *gpname, char *lib)
{
  void *f, *handle;

 /* dlopen(NULL) returns a handle to the running process. 
  * bug report Y. Uchikawa: does not work for gp-dyn on FreeBSD 2.2.5
  */
#ifdef __FreeBSD__
  if (! *lib) lib = DL_DFLT_NAME;
#else
  if (! *lib) lib = NULL;
#endif
  if (! *gpname) gpname=name;
  
  handle = dlopen(lib,RTLD_LAZY);
  if (!handle)
  {
    const char *s = dlerror(); if (s) fprintferr("%s\n\n",s);
    if (lib) err(talker,"couldn't open dynamic library '%s'",lib);
    err(talker,"couldn't open dynamic symbol table of process");
  }
  f = dlsym(handle,name);
  if (!f)
  {
    if (lib) err(talker,"can't find symbol '%s' in library '%s'",name,lib);
    err(talker,"can't find symbol '%s' in dynamic symbol table of process",name);
  }
  install(f,gpname,code);
}
#else
#  ifdef _WIN32
#  include <windows.h>
void 
install0(char *name, char *code, char *gpname, char *lib)
{
  FARPROC f;
  HMODULE handle;
#ifdef WINCE
  short wlib[256];
  short wname[256];
#endif

#ifdef DL_DFLT_NAME
  if (! *lib) lib = DL_DFLT_NAME;
#endif
  if (! *gpname) gpname=name;
  
#ifdef WINCE
  MultiByteToWideChar(CP_ACP, 0, lib, strlen(lib)+1, wlib, 256);
  handle = LoadLibrary(wlib);
#else
  handle = LoadLibrary(lib);
#endif
  if (!handle)
  {
    if (lib) err(talker,"couldn't open dynamic library '%s'",lib);
    err(talker,"couldn't open dynamic symbol table of process");
  }
#ifdef WINCE
  MultiByteToWideChar(CP_ACP, 0, name, strlen(name)+1, wname, 256);
  f = GetProcAddress(handle,wname);
#else
  f = GetProcAddress(handle,name);
#endif
  if (!f)
  {
    if (lib) err(talker,"can't find symbol '%s' in library '%s'",name,lib);
    err(talker,"can't find symbol '%s' in dynamic symbol table of process",name);
  }
  install((void*)f,gpname,code);
}
#  else
void 
install0(char *name, char *code, char *gpname, char *lib) { err(archer); }
#endif
#endif

static long
get_type_num(char *st)
{
  if (isdigit((int)*st))
  {
    char *s = st;
    while (*s && isdigit((int)*s)) s++;
    if (*s) err(talker,"Unknown type: %s",s);
    return atol(st);
  }
  if (!strncmp(st,"t_",2)) st += 2; /* skip initial part */

  switch(strlen(st))
  {
    case 3:
      if (!strcmp(st,"INT")) return t_INT;
      if (!strcmp(st,"POL")) return t_POL;
      if (!strcmp(st,"SER")) return t_SER;
      if (!strcmp(st,"QFR")) return t_QFR;
      if (!strcmp(st,"QFI")) return t_QFI;
      if (!strcmp(st,"VEC")) return t_VEC;
      if (!strcmp(st,"COL")) return t_COL;
      if (!strcmp(st,"MAT")) return t_MAT;
      if (!strcmp(st,"STR")) return t_STR;
      break;

    case 4:
      if (!strcmp(st,"REAL")) return t_REAL;
      if (!strcmp(st,"FRAC")) return t_FRAC;
      if (!strcmp(st,"QUAD")) return t_QUAD;
      if (!strcmp(st,"LIST")) return t_LIST;
      break;

    case 5:
      if (!strcmp(st,"FRACN")) return t_FRACN;
      if (!strcmp(st,"PADIC")) return t_PADIC;
      if (!strcmp(st,"RFRAC")) return t_RFRAC;
      if (!strcmp(st,"SMALL")) return t_SMALL;
      break;

    case 6:
      if (!strcmp(st,"INTMOD")) return t_INTMOD;
      if (!strcmp(st,"POLMOD")) return t_POLMOD;
      if (!strcmp(st,"RFRACN")) return t_RFRACN;
      break;

    case 7:
      if (!strcmp(st,"COMPLEX")) return t_COMPLEX;
      break;

    case 8:
      if (!strcmp(st,"VECSMALL")) return t_VECSMALL;
      break;
  }
  err(talker,"Unknown type: t_%s",st);
  return 0; /* not reached */
}

GEN
type0(GEN x, char *st)
{
  long t, tx;
  if (! *st) 
  {
    char *s = type_name(typ(x));
    return strtoGENstr(s, 0);
  }
  tx = typ(x);
  t = get_type_num(st);

  if (is_frac_t(tx))
  {
    if (!is_frac_t(t) && !is_rfrac_t(t))
      err(typeer, "type");
    x = gcopy(x);
  }
  else if (is_rfrac_t(tx))
  {
    if (is_frac_t(t))
    {
      x = gred_rfrac(x);
      tx = typ(x);
      if (!is_frac_t(tx)) err(typeer, "type");
    }
    else
    {
      if (!is_rfrac_t(t)) err(typeer, "type");
      x = gcopy(x);
    }
  }
  else if (is_vec_t(tx))
  {
    if (!is_vec_t(t)) err(typeer, "type");
    x = gcopy(x);
  }
  else if (tx != t) err(typeer, "type");
  settyp(x, t); return x;
}

entree functions_highlevel[]={
{"addhelp",99,(void*)addhelp,11,"vSs"},
{"install",99,(void*)install0,11,"vrrD\"\",r,D\"\",s,"},
{"kill",85,(void*)kill0,11,"vS"},
{"plot",99,(void*)plot,10,"vV=GGIp"},
{"plotbox",35,(void*)rectbox,10,"vLGG"},
{"plotclip",99,(void*)rectclip,10,"vL"},
{"plotcolor",19,(void*)rectcolor,10,"vLL"},
{"plotcopy",99,(void*)rectcopy,10,"vLLLL"},
{"plotcursor",11,(void*)rectcursor,10,"L"},
{"plotdraw",99,(void*)rectdraw,10,"vG"},
{"plotfile",16,(void*)plot_outfile_set,10,"ls"},
{"ploth",99,(void*)ploth,10,"V=GGIpD0,L,D0,L,"},
{"plothraw",25,(void*)plothraw,10,"GGD0,L,"},
{"plothsizes",0,(void*)plothsizes,10,""},
{"plotinit",34,(void*)initrect,10,"vLLL"},
{"plotkill",99,(void*)killrect,10,"vL"},
{"plotlines",99,(void*)rectlines,10,"vLGGD0,L,"},
{"plotlinetype",19,(void*)rectlinetype,10,"vLL"},
{"plotmove",35,(void*)rectmove,10,"vLGG"},
{"plotpoints",35,(void*)rectpoints,10,"vLGG"},
{"plotpointsize",99,(void*)rectpointsize,10,"vLG"},
{"plotpointtype",19,(void*)rectpointtype,10,"vLL"},
{"plotrbox",35,(void*)rectrbox,10,"vLGG"},
{"plotrecth",73,(void*)rectploth,10,"LV=GGIpD0,L,D0,L,"},
{"plotrecthraw",45,(void*)rectplothraw,10,"LGD0,L,"},
{"plotrline",35,(void*)rectrline,10,"vLGG"},
{"plotrmove",35,(void*)rectrmove,10,"vLGG"},
{"plotrpoint",35,(void*)rectrpoint,10,"vLGG"},
{"plotscale",59,(void*)rectscale,10,"vLGGGG"},
{"plotstring",57,(void*)rectstring,10,"vLs"},
{"plotterm",16,(void*)term_set,10,"ls"},
{"psdraw",99,(void*)postdraw,10,"vG"},
{"psploth",99,(void*)postploth,10,"V=GGIpD0,L,D0,L,"},
{"psplothraw",25,(void*)postplothraw,10,"GGD0,L,"},
{"type",99,(void*)type0,11,"GD\"\",r,"},

{NULL,0,NULL,0,NULL} /* sentinel */
};

char *helpmessages_highlevel[]={
  "addhelp(symbol,\"message\"): add/change help message for a symbol",
  "install(name,code,{gpname},{lib}): load from dynamic library 'lib' the function 'name'. Assign to it the name 'gpname' in this GP session, with argument code 'code'. If 'lib' is omitted use 'libpari.so'. If 'gpname' is omitted, use 'name'",
  "kill(x):  kills the present value of the variable or function x. Returns new value or 0",
  "plot(X=a,b,expr): crude plot of expression expr, X goes from a to b",
  "plotbox(w,x2,y2): if the cursor is at position (x1,y1), draw a box with diagonal (x1,y1) and (x2,y2) in rectwindow w (cursor does not move)",
  "plotclip(w): clip the contents of the rectwindow to the bounding box (except strings)",
  "plotcolor(w,c): in rectwindow w, set default color to c. Possible values for c are 1=black, 2=blue, 3=sienna, 4=red, 5=cornsilk, 6=grey, 7=gainsborough",
  "plotcopy(sourcew,destw,dx,dy): copy the contents of rectwindow sourcew to rectwindow destw with offset (dx,dy)",
  "plotcursor(w): current position of cursor in rectwindow w",
  "plotdraw(list): draw vector of rectwindows list at indicated x,y positions; list is a vector w1,x1,y1,w2,x2,y2,etc. . ",
  "plotfile(filename): set the output file for plotting output. \"-\" redirects to the same place as PARI output",
  "ploth(X=a,b,expr,{flags=0},{n=0}): plot of expression expr, X goes from a to b in high resolution. Both flags and n are optional. Binary digits of flags mean : 1 parametric plot, 2 recursive plot, 8 omit x-axis, 16 omit y-axis, 32 omit frame, 64 do not join points, 128 plot both lines and points, 256 use cubic splines. n specifies number of reference points on the graph (0=use default value). Returns a vector for the bounding box",
  "plothraw(listx,listy,{flag=0}): plot in high resolution points whose x (resp. y) coordinates are in listx (resp. listy). If flag is non zero, join points",
  "plothsizes(): returns array of 6 elements: terminal width and height, sizes for ticks in horizontal and vertical directions (in pixels), width and height of characters",
  "plotinit(w,x,y): initialize rectwindow w to size x,y",
  "plotkill(w): erase the rectwindow w",
  "plotlines(w,listx,listy,{flag=0}): draws an open polygon in rectwindow w where listx and listy contain the x (resp. y) coordinates of the vertices. If listx and listy are both single values (i.e not vectors), draw the corresponding line (and move cursor). If (optional) flag is non-zero, close the polygon",
  "plotlinetype(w,type): change the type of following lines in rectwindow w. type -2 corresponds to frames, -1 to axes, larger values may correspond to something else. w=-1 changes highlevel plotting",
  "plotmove(w,x,y): move cursor to position x,y in rectwindow w",
  "plotpoints(w,listx,listy): draws in rectwindow w the points whose x (resp y) coordinates are in listx (resp listy). If listx and listy are both single values (i.e not vectors), draw the corresponding point (and move cursor)",
  "plotpointsize(w,size): change the \"size\" of following points in rectwindow w. w=-1 changes global value",
  "plotpointtype(w,type): change the type of following points in rectwindow w. type -1 corresponds to a dot, larger values may correspond to something else. w=-1 changes highlevel plotting",
  "plotrbox(w,dx,dy): if the cursor is at (x1,y1), draw a box with diagonal (x1,y1)-(x1+dx,y1+dy) in rectwindow w (cursor does not move)",
  "plotrecth(w,X=xmin,xmax,expr,{flags=0},{n=0}): plot graph(s) for expr in rectwindow w, where expr is scalar for a single non-parametric plot, and a vector otherwise. If plotting is parametric, its length should be even and pairs of entries give points coordinates. If not, all entries but the first are y-coordinates. Both flags and n are optional. Binary digits of flags mean: 1 parametric plot, 2 recursive plot, 4 do not rescale w, 8 omit x-axis, 16 omit y-axis, 32 omit frame, 64 do not join points, 128 plot both lines and points. n specifies the number of reference points on the graph (0=use default value). Returns a vector for the bounding box",
  "plotrecthraw(w,data,{flags=0}): plot graph(s) for data in rectwindow w, where data is a vector of vectors. If plot is parametric, length of data should be even, and pairs of entries give curves to plot. If not, first entry gives x-coordinate, and the other ones y-coordinates. Admits the same optional flags as plotrecth, save that recursive plot is meaningless",
  "plotrline(w,dx,dy): if the cursor is at (x1,y1), draw a line from (x1,y1) to (x1+dx,y1+dy) (and move the cursor) in the rectwindow w",
  "plotrmove(w,dx,dy): move cursor to position (dx,dy) relative to the present position in the rectwindow w",
  "plotrpoint(w,dx,dy): draw a point (and move cursor) at position dx,dy relative to present position of the cursor in rectwindow w",
  "plotscale(w,x1,x2,y1,y2): scale the coordinates in rectwindow w so that x goes from x1 to x2 and y from y1 to y2 (y2<y1 is allowed)",
  "plotstring(w,x): draw in rectwindow w the string corresponding to x",
  "plotterm(\"termname\"): set terminal to plot in high resolution to. Ignored by some drivers. In gnuplot driver possible terminals are the same as in gnuplot. Positive value means success",
  "psdraw(list): same as plotdraw, except that the output is a postscript program in psfile (pari.ps by default)",
  "psploth(X=a,b,expr,{flags=0},{n=0}): same as ploth, except that the output is a postscript program in psfile (pari.ps by default)",
  "psplothraw(listx,listy,{flag=0}): same as plothraw, except that the output is a postscript program in psfile (pari.ps by default)",
  "type(x,{t}): if t is not present, output the type of the GEN x. Else make a copy of x with type t. Use with extreme care, usually with t = t_FRACN or t = t_RFRACN). Try \\t for a list of types",
};

