/*******************************************************************/
/*                                                                 */
/*                    GP-SPECIFIC FUNCTIONS                        */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "../graph/rect.h"

extern void  addhelp(entree *ep, char *s);
extern void  allocatemem0(unsigned long newsize);
extern GEN   default0(char *a, char *b, long flag);
extern void  error0(GEN *g);
extern GEN   extern0(char *cmd);
extern void  gp_quit(void);
extern GEN   input0();
extern void  kill0(entree *ep);
extern void  print0(GEN *g,long flag);
extern GEN   read0(char *s);
extern long  setprecr(long n);
extern void  system0(char *cmd);
extern GEN   trap0(char *e, char *f, char *r);
extern int   whatnow(char *s, int silent);
extern void  write0(char *s, GEN *g, long flag);

static void
whatnow0(char *s) { whatnow(s,0); }

entree functions_gp[]={
{"allocatemem",0,(void*)allocatemem0,11,"vD0,L,"},
{"default",0,(void*)default0,11,"D\"\",r,D\"\",s,D0,L,"},
{"error",0,(void*)error0,11,"vs*"},
{"extern",1,(void*)extern0,11,"s"},
{"input",0,(void*)input0,11,""},
{"global",88,NULL,11,NULL},
{"print",0,(void*)print0,11,"vs*D0,L,"},
{"print1",0,(void*)print0,11,"vs*D5,L,"},
{"printp",0,(void*)print0,11,"vs*D2,L,"},
{"printp1",0,(void*)print0,11,"vs*D7,L,"},
{"printtex",0,(void*)print0,11,"vs*D4,L,"},
{"quit",0,(void*)gp_quit,11,"v"},
{"read",0,(void*)read0,11,"D\"\",s,"},
{"system",70,(void*)system0,11,"vs"},
{"trap",0,(void*)trap0,11,"D\"\",r,DI,DI"},
{"whatnow",1,(void*)whatnow0,11,"vr"},
{"write",0,(void*)write0,11,"vss*D0,L,"},
{"write1",0,(void*)write0,11,"vss*D5,L,"},
{"writetex",0,(void*)write0,11,"vss*D4,L,"},

{NULL,0,NULL,0,NULL} /* sentinel */
};

char *helpmessages_gp[]={
  "allocatemem({s=0}): allocates a new stack of s bytes. doubles the stack if s is omitted",
  "default({opt},{v},{flag}): set the default opt to v. If v is omitted, print the current default for opt. If no argument is given, print a list of all defaults as well as their values. If flag is non-zero, return the result instead of printing it on screen. See manual for details",
  "error(\"msg\"): abort script with error message msg",
  "extern(cmd): execute shell command cmd, and feeds the result to GP (as if loading from file)",
  "input(): read an expression from the input file or standard input",
  "global(x): declare x to be a global variable",
  "print(a): outputs a (in raw format) ending with newline",
  "print1(a): outputs a (in raw format) without ending with newline",
  "printp(a): outputs a (in beautified format) ending with newline",
  "printp1(a): outputs a (in beautified format) without ending with newline",
  "printtex(a): outputs a in TeX format",
  "quit(): quits GP and return to the system",
  "read({filename}): read from the input file filename. If filename is omitted, reread last input file (be it from readfile or \\r)",
  "system(a): a being a string, execute the system command a (not valid on every machine)",
  "trap({err}, {rec}, {seq}): try to execute seq, trapping error err (all of them if err ommitted); sequence rec is executed if the error occurs and is the result of the command. When seq is omitted, define rec as a default handler for error err (a break loop will be started if rec omitted). If rec is the empty string \"\" pop out the last default handler",
  "whatnow(fun): if f was present in GP version 1.39.15 or lower, gives the new function name",
  "write(filename,a): write the string expression a (same output as print) to filename",
  "write1(filename,a): write the string expression a (same output as print1) to filename",
  "writetex(filename,a): write the string expression a (same format as print) to filename, in TeX format",
};

/* Backward Compatibility */

static GEN
gtype(GEN x)
{
  return stoi(typ(x));
}

static GEN
gsettype(GEN x,long t)
{
  x=gcopy(x); settyp(x,t); return x;
}

static long
setserieslength(long n)
{
  long m=precdl;
  if(n>0) precdl=n;
  return m;
}

entree functions_oldgp[] = {
{"allocatemem",11,(void *)allocatemem0,2,"vLp"},
{"box",35,(void *)rectbox,10,"vLGG"},
{"color",2,(void *)rectcolor,2,"vLL"},
{"cursor",11,(void*)rectcursor,10,"vLp"},
{"default",0,(void*)default0,11,"D\"\",r,D\"\",s,D0,L,"},
{"draw",1,(void*)rectdraw,10,"vGp"},
{"initrect",34,(void*)initrect,10,"vLLL"},
{"kill",85,(void*)kill0,11,"vS"},
{"killrect",11,(void *)killrect,10,"vL"},
{"line",35,(void *)rectline,10,"vLGG"},
{"lines",35,(void *)rectlines,10,"vLGG"},
{"move",35,(void*)rectmove,10,"vLGG"},
{"plot",99,(void *)plot,10,"vV=GGIDGDGp"},
{"ploth",37,(void *)ploth,10,"V=GGIp"},
{"ploth2",37,(void *)ploth2,10,"V=GGIp"},
{"plothmult",37,(void *)plothmult,10,"V=GGIp"},
{"plothraw",2,(void *)plothraw,10,"GGp"},
{"point",35,(void *)rectpoint,10,"vLGG"},
{"points",35,(void *)rectpoints,10,"vLGG"},
{"postdraw",1,(void *)postdraw,10,"vG"},
{"postploth",37,(void *)postploth,10,"V=GGIpD0,L,D0,L,"},
{"postploth2",37,(void *)postploth2,10,"V=GGIpD0,L,"},
{"postplothraw",2,(void *)postplothraw,10,"GGD0,L,"},
{"pprint",0,(void*)print0,11,"vs*D2,L,"},
{"pprint1",0,(void*)print0,11,"vs*D7,L,"},
{"print",0,(void*)print0,11,"vs*D0,L,"},
{"print1",0,(void*)print0,11,"vs*D5,L,"},
{"rbox",35,(void *)rectrbox,10,"vLGG"},
{"read",0,(void *)input0,11,""},
{"rline",35,(void *)rectrline,10,"vLGG"},
{"rlines",35,(void *)rectlines,10,"vLGG"},
{"rmove",35,(void *)rectrmove,10,"vLGG"},
{"rpoint",35,(void *)rectrpoint,10,"vLGG"},
{"rpoints",35,(void *)rectpoints,10,"vLGG"},
{"scale",59,(void *)rectscale,10,"vLGGGG"},
{"setprecision",15,(void *)setprecr,2,"lL"},
{"setserieslength",15,(void *)setserieslength,2,"lL"},
{"settype",21,(void *)gsettype,2,"GL"},
{"string",57,(void*)rectstring,10,"vLs"},
{"system",70,(void*) system0,11,"vs"},
{"texprint",0,(void*)print0,11,"vs*D4,L,"},
{"type",1,(void *)gtype,2,"Gp"},

{NULL,0,NULL,0,NULL} /* sentinel */
};

char *helpmessages_oldgp[] = {
  "allocatemem(s)=allocates a new stack of s bytes, or doubles the stack if size is 0",
  "box(w,x2,y2)=if the cursor is at position (x1,y1), draw a box with diagonal (x1,y1) and (x2,y2) in rectwindow w (cursor does not move)",
  "color(w,c)=set default color to c in rectwindow. Possible values for c are 1=sienna, 2=cornsilk, 3=red, 4=black, 5=grey, 6=blue, 7=gainsborough",
  "cursor(w)=current position of cursor in rectwindow w",
  "default({opt},{v},{flag}): set the default opt to v. If v is omitted, print the current default for opt. If no argument is given, print a list of all defaults as well as their values. If flag is non-zero, return the result instead of printing it on screen. See manual for details",
  "draw(list)=draw vector of rectwindows list at indicated x,y positions; list is a vector w1,x1,y1,w2,x2,y2,etc...",
  "initrect(w,x,y)=initialize rectwindow w to size x,y",
  "kill(x)= kills the present value of the variable or function x. Returns new value or 0",
  "killrect(w)=erase the rectwindow w",
  "line(w,x2,y2)=if cursor is at position (x1,y1), draw a line from (x1,y1) to (x2,y2) (and move the cursor) in the rectwindow w",
  "lines(w,listx,listy)=draws an open polygon in rectwindow w where listx and listy contain the x (resp. y) coordinates of the vertices",
  "move(w,x,y)=move cursor to position x,y in rectwindow w",
  "plot(X=a,b,expr)=crude plot of expression expr, X goes from a to b",
  "ploth(X=a,b,expr)=plot of expression expr, X goes from a to b in high resolution",
  "ploth2(X=a,b,[expr1,expr2])=plot of points [expr1,expr2], X goes from a to b in high resolution",
  "plothmult(X=a,b,[expr1,...])=plot of expressions expr1,..., X goes from a to b in high resolution",
  "plothraw(listx,listy)=plot in high resolution points whose x (resp. y) coordinates are in listx (resp. listy)",
  "point(w,x,y)=draw a point (and move cursor) at position x,y in rectwindow w",
  "points(w,listx,listy)=draws in rectwindow w the points whose x (resp y) coordinates are in listx (resp listy)",
  "postdraw(list)=same as plotdraw, except that the output is a PostScript program in file \"pari.ps\"",
  "postploth(X=a,b,expr)=same as ploth, except that the output is a PostScript program in the file \"pari.ps\"",
  "postploth2(X=a,b,[expr1,expr2])=same as ploth2, except that the output is a PostScript program in the file \"pari.ps\"",
  "postplothraw(listx,listy)=same as plothraw, except that the output is a PostScript program in the file \"pari.ps\"",
  "pprint(a)=outputs a in beautified format ending with newline",
  "pprint1(a)=outputs a in beautified format without ending with newline",
  "print(a)=outputs a in raw format ending with newline",
  "print1(a)=outputs a in raw format without ending with newline",
  "rbox(w,dx,dy)=if the cursor is at (x1,y1), draw a box with diagonal (x1,y1)-(x1+dx,y1+dy) in rectwindow w (cursor does not move)",
  "read()=read an expression from the input file or standard input",
  "rline(w,dx,dy)=if the cursor is at (x1,y1), draw a line from (x1,y1) to (x1+dx,y1+dy) (and move the cursor) in the rectwindow w",
  "rlines(w,dx,dy)=draw in rectwindow w the points given by vector of first coordinates xsand vector of second coordinates, connect them by lines",
  "rmove(w,dx,dy)=move cursor to position (dx,dy) relative to the present position in the rectwindow w",
  "rpoint(w,dx,dy)=draw a point (and move cursor) at position dx,dy relative to present position of the cursor in rectwindow w",
  "rpoints(w,xs,ys)=draw in rectwindow w the points given by vector of first coordinates xs and vector of second coordinates ys",
  "scale(w,x1,x2,y1,y2)=scale the coordinates in rectwindow w so that x goes from x1 to x2 and y from y1 to y2 (y2<y1 is allowed)",
  "setprecision(n)=set the current precision to n decimal digits if n>0, or return the current precision if n<=0",
  "setserieslength(n)=set the default length of power series to n if n>0, or return the current default length if n<=0",
  "settype(x,t)=make a copy of x with type t (to use with extreme care)",
  "string(w,x)=draw in rectwindow w the string corresponding to x, where x is either a string, or a number in R, written in format 9.3",
  "system(a): a being a string, execute the system command a (not valid on every machine)",
  "texprint(a)=outputs a in TeX format",
  "type(x)=internal type number of the GEN x"
};
