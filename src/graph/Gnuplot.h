/* This header should be included in one C file only! */

#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>

#ifdef __cplusplus
  extern "C" {
#endif

/* CAT2:
 *      This macro catenates 2 tokens together.
 */
/* STRINGIFY:
 *      This macro surrounds its token with double quotes.
 */
#ifndef CAT2
# if 42 == 1
#  define CAT2(a,b)a/**/b
#  define CAT3(a,b,c)a/**/b/**/c
#  define CAT4(a,b,c,d)a/**/b/**/c/**/d
#  define CAT5(a,b,c,d,e)a/**/b/**/c/**/d/**/e
#  define STRINGIFY(a)"a"
                /* If you can get stringification with catify, tell me how! */
# endif
# if 42 == 42
#  define CAT2(a,b)a ## b
#  define CAT3(a,b,c)a ## b ## c
#  define CAT4(a,b,c,d)a ## b ## c ## d
#  define CAT5(a,b,c,d,e)a ## b ## c ## d ## e
#  define StGiFy(a)# a
#  define STRINGIFY(a)StGiFy(a)
#  define SCAT2(a,b)StGiFy(a) StGiFy(b)
#  define SCAT3(a,b,c)StGiFy(a) StGiFy(b) StGiFy(c)
#  define SCAT4(a,b,c,d)StGiFy(a) StGiFy(b) StGiFy(c) StGiFy(d)
#  define SCAT5(a,b,c,d,e)StGiFy(a) StGiFy(b) StGiFy(c) StGiFy(d) StGiFy(e)
# endif
# ifndef CAT2
#   include "Bletch: How does this C preprocessor catenate tokens?"
# endif
#endif /* CAT2 */


#define TERM_CAN_MULTIPLOT    1  /* tested if stdout not redirected */
#define TERM_CANNOT_MULTIPLOT 2  /* tested if stdout is redirected  */
#define TERM_BINARY           4  /* open output file with "b"       */

#ifndef NO_JUNK_SMALL

/* Compatibility with the old gnuplot: */
extern  FILE *outfile;
FILE *outfile = NULL;

extern  FILE *gpoutfile;
FILE *gpoutfile = NULL;

static outfile_set;
static void
set_gpoutfile(void)
{
  outfile = stdout;
  gpoutfile = stdout;
}

#define SET_OUTFILE (outfile_set++ ? 1 : (set_gpoutfile(), 1))

extern int encoding;
int        encoding = 0;
extern float                   xoffset;  /* x origin */
extern float                   yoffset;  /* y origin */
float                   xoffset = 0.0;  /* x origin */
float                   yoffset = 0.0;  /* y origin */
extern int		multiplot;
int		multiplot		= 0;

extern char *outstr;
#define MAX_ID_LEN 50
/* char        outstr[MAX_ID_LEN+1] = "STDOUT"; */
char        *outstr = NULL;
extern double ticscale; /* scale factor for tic marks (was (0..1])*/
double        ticscale = 1.0; /* scale factor for tic mark */

char *input_line = NULL;
int inline_num;          /* from command.c */

float xsize=1.0, ysize=1.0;
double pointsize=1.0;		/* During test! */

int interactive;    /* from plot.c */
char *infile_name;       /* from plot.c */
extern char     default_font[];
char            default_font[MAX_ID_LEN+1] = "\0"; /* Entry added by DJL */

typedef int TBOOLEAN;

enum DATA_TYPES {
	INTGR, CMPLX
};

#if !(defined(ATARI)&&defined(__GNUC__)&&defined(_MATH_H)) &&  !(defined(MTOS)&&defined(__GNUC__)&&defined(_MATH_H)) /* FF's math.h has the type already */
struct cmplx {
	double real, imag;
};
#endif

struct value {
	enum DATA_TYPES type;
	union {
		int int_val;
		struct cmplx cmplx_val;
	} v;
};

struct lexical_unit {	/* produced by scanner */
	TBOOLEAN is_token;	/* true if token, false if a value */
	struct value l_val;
	int start_index;	/* index of first char in token */
	int length;			/* length of token in chars */
};

/* char *token; */
#define MAX_TOKENS 20
extern struct lexical_unit *token;
struct lexical_unit tokens[MAX_TOKENS];	/* We only process options,
					   there should not be many */
struct lexical_unit *token = tokens;
long c_token = 0, num_tokens = 0;
char term_options[200] = "";

/* Here are the only missing functions: */

struct value*
const_express(struct value*v)
{
    if (token[c_token].is_token)
	croak("Expect a number, got a string");
    *v = token[c_token++].l_val;
    return v;
}

void*
gp_alloc(unsigned long size, char *usage)
{
  return malloc(size);
}

void*
gp_realloc(void *old, unsigned long size, char *usage)
{
  return realloc(old,size);
}

void
bail_to_command_line()
{
  croak("panic: gnuplot");
}

#endif	/* NO_JUNK_SMALL */ 

/* Cannot pull the whole plot.h, too many contradictions. */

#ifdef __ZTC__
typedef int (*FUNC_PTR)(...);
#else
typedef int (*FUNC_PTR)();
#endif

struct TERMENTRY {
        char *name;
#if defined(_Windows) && !defined(WIN32)
        char GPFAR description[80];     /* to make text go in FAR segment */
#else
        char *description;
#endif
        unsigned int xmax,ymax,v_char,h_char,v_tic,h_tic;
        FUNC_PTR options,init,reset,text,scale,graphics,move,vector,linetype,
                put_text,text_angle,justify_text,point,arrow,set_font,
		pointsize;
	int flags;
        FUNC_PTR suspend,resume,fillbox,linewidth;
};

#ifdef _Windows
#  define termentry TERMENTRY far
#else
#  define termentry TERMENTRY
#endif

extern struct termentry *term;
struct termentry *term;

#define RETVOID
#define RETINT , 1

#define F_0 void(*)()
#define F_1 void(*)(int)
#define F_1I int(*)(int)
#define F_1D void(*)(double)
#define F_1IP int(*)(char*)
#define F_2 void(*)(unsigned int,unsigned int)
#define F_2D int(*)(double,double)
#define F_3 void(*)(unsigned int,unsigned int,int)
#define F_3T void(*)(int,int,char*)
#define F_4 void(*)(int,int,int,int)
#define F_5 void(*)(int,int,int,int,int)

#define CALL_G_METH0(method) CALL_G_METH(method,0,(),RETVOID)
#define CALL_G_METH1(method,arg1) CALL_G_METH(method,1,(arg1),RETVOID)
#define CALL_G_METH1I(method,arg1) CALL_G_METH(method,1I,(arg1),RETINT)
#define CALL_G_METH1D(method,arg1) CALL_G_METH(method,1D,(arg1),RETVOID)
#define CALL_G_METH1IP(method,arg1) CALL_G_METH(method,1IP,(arg1),RETINT)
#define CALL_G_METH2(method,arg1,arg2) \
		CALL_G_METH(method,2,((arg1),(arg2)),RETVOID)
#define CALL_G_METH2D(method,arg1,arg2) \
		CALL_G_METH(method,2D,((arg1),(arg2)),RETINT)
#define CALL_G_METH3(method,arg1,arg2,arg3) \
		CALL_G_METH(method,3,((arg1),(arg2),(arg3)),RETVOID)
#define CALL_G_METH3T(method,arg1,arg2,arg3) \
		CALL_G_METH(method,3T,((arg1),(arg2),(arg3)),RETVOID)
#define CALL_G_METH4(method,arg1,arg2,arg3,arg4) \
		CALL_G_METH(method,4,((arg1),(arg2),(arg3),(arg4)),RETVOID)
#define CALL_G_METH5(method,arg1,arg2,arg3,arg4,arg5) \
		CALL_G_METH(method,5,((arg1),(arg2),(arg3),(arg4),(arg5)),RETVOID)

#define CALL_G_METH(method,mult,args,returnval)    (		\
       (term==0) ? (						\
	 croak("No terminal specified") returnval		\
       ) :							\
       (*(CAT2(F_,mult))term->method)args		\
     )

#define GET_G_FLAG(mask)    (		\
       (term==0) ? (						\
	 croak("No terminal specified") RETINT		\
       ) :							\
       (term->flags & (mask)))

#ifdef DONT_POLLUTE_INIT
#  define gptable_init()	CALL_G_METH0(init)
#else
#  define init()		CALL_G_METH0(init)
#  define gptable_init		init
#endif
#define reset()		CALL_G_METH0(reset)
#define text()		CALL_G_METH0(text)
#define options()	CALL_G_METH0(options)
#define graphics()	CALL_G_METH0(graphics)
#define linetype(lt)	CALL_G_METH1(linetype,lt)
#define justify_text(mode)	CALL_G_METH1I(justify_text,mode)
#define text_angle(ang)	CALL_G_METH1I(text_angle,ang)
#define scale(xs,ys)	CALL_G_METH2D(scale,xs,ys)
#define move(x,y)	CALL_G_METH2(move,x,y)
#define vector(x,y)	CALL_G_METH2(vector,x,y)
#define put_text(x,y,str)	CALL_G_METH3T(put_text,x,y,str)
#define point(x,y,p)	CALL_G_METH3(point,x,y,p)
#define arrow(sx,sy,ex,ey,head)	CALL_G_METH5(arrow,sx,sy,ex,ey,head)
#define set_font(font)	CALL_G_METH1IP(set_font,font)
#define setpointsize(size)	CALL_G_METH1D(pointsize,size)
#define suspend()	CALL_G_METH0(suspend)
#define resume()	CALL_G_METH0(resume)
#define fillbox(sx,sy,ex,ey,head)	CALL_G_METH5(fillbox,sx,sy,ex,ey,head)
#define linewidth(size)	CALL_G_METH1D(linewidth,size)
#define can_multiplot()	GET_G_FLAG(TERM_CAN_MULTIPLOT)
#define cannot_multiplot()	GET_G_FLAG(TERM_CANNOT_MULTIPLOT)
#define is_binary()	GET_G_FLAG(TERM_BINARY)

#define termprop(prop) (term->prop)
#define termset(term) my_change_term(term,strlen(term))

struct termentry * change_term(char*,int);

#define TTABLE_STARTPLOT	0
#define TTABLE_ENDPLOT		1
#define TTABLE_STARTMPLOT	2
#define TTABLE_ENDMPLOT		3
#define TTABLE_INIT		4
#define TTABLE_LIST		5
#define TTABLE_COUNT		6

typedef void (*TSET_FP)(char *s);
typedef void (*TST_END_FP)(void);
typedef void (*SET_SIZES_t)(double x, double y);
typedef double (*GET_SIZES_t)(int flag);

struct t_ftable {
  int loaded;
  FUNC_PTR change_term_p;
  TSET_FP term_set_outputp;
  SET_SIZES_t set_sizesp;
  GET_SIZES_t get_sizesp;
  TST_END_FP term_funcs[TTABLE_COUNT];
};

#ifdef DYNAMIC_PLOTTING			/* Can load plotting DLL later */

UNKNOWN_null()
{
    croak("gnuplot-like plotting environment not loaded yet");
}

static void myterm_table_not_loaded_v(void);
static void myterm_table_not_loaded(char*);
static int myterm_table_not_loaded_u();
static void myterm_table_not_loaded_vdd(double x, double y);
static double myterm_table_not_loaded_di(int flag);

#if 0
static int ftable_warned;
static void
tmp_my_term_init
{
  if (!warned++)
     warn("This runtime link with gnuplot-shim does not implement midlevel start/end functions");
  shim_myinit();
}
#endif

static struct t_ftable my_term_ftable = 
{
	0, &myterm_table_not_loaded_u, &myterm_table_not_loaded,
	&myterm_table_not_loaded_vdd,
	&myterm_table_not_loaded_di,
	{&myterm_table_not_loaded_v, &myterm_table_not_loaded_v, 
	 &myterm_table_not_loaded_v, &myterm_table_not_loaded_v,
	 &myterm_table_not_loaded_v, &myterm_table_not_loaded_v}
};

static struct t_ftable *my_term_ftablep = &my_term_ftable;

static void
myterm_table_not_loaded_v(void)
{
    if (!my_term_ftablep->loaded) {
        UNKNOWN_null();
	return;
    }
    croak("This runtime link with gnuplot-shim does not implement midlevel start/end functions");
}

static void
myterm_table_not_loaded(char *s)
{
  myterm_table_not_loaded_v();
}

static void
myterm_table_not_loaded_vdd(double x, double y)
{
  myterm_table_not_loaded_v();
}

static double
myterm_table_not_loaded_di(int flag)
{
  myterm_table_not_loaded_v();
}

static int
myterm_table_not_loaded_u()
{
  myterm_table_not_loaded_v();
  return 0;
}

#  define change_term		(*my_term_ftablep->change_term_p)
#  define term_set_output	(*my_term_ftablep->term_set_outputp)
#  define term_start_plot	(*my_term_ftablep->term_funcs[TTABLE_STARTPLOT])
#  define term_end_plot	(*my_term_ftablep->term_funcs[TTABLE_ENDPLOT])
#  define term_start_multiplot	(*my_term_ftablep->term_funcs[TTABLE_STARTMPLOT])
#  define term_end_multiplot	(*my_term_ftablep->term_funcs[TTABLE_ENDMPLOT])
#  define term_init		(*my_term_ftablep->term_funcs[TTABLE_INIT])
#  define list_terms		(*my_term_ftablep->term_funcs[TTABLE_LIST])
#  define plotsizes_scale	(*my_term_ftablep->set_sizesp)
#  define plotsizes_scale_get	(*my_term_ftablep->get_sizesp)

#  define scaled_xmax()	((int)termprop(xmax)*plotsizes_scale_get(0))
#  define scaled_ymax()	((int)termprop(ymax)*plotsizes_scale_get(1))

#define USE_FUNCTION_FROM_TABLE

static struct termentry *
my_change_term(char*s,int l)
{
    SET_OUTFILE;
    if (!my_term_ftablep->change_term_p)
	UNKNOWN_null();
    return term = (struct termentry *)(*my_term_ftablep->change_term_p)(s,l);
}

static struct termentry dummy_term_tbl[] = {
    {"unknown", "Unknown terminal type - not a plotting device",
	  100, 100, 1, 1,
	  1, 1, UNKNOWN_null, UNKNOWN_null, UNKNOWN_null,
	  UNKNOWN_null, UNKNOWN_null, UNKNOWN_null, UNKNOWN_null, UNKNOWN_null,
	  UNKNOWN_null, UNKNOWN_null, UNKNOWN_null,
     UNKNOWN_null, UNKNOWN_null, UNKNOWN_null, UNKNOWN_null, UNKNOWN_null, 0,
	  UNKNOWN_null, UNKNOWN_null, UNKNOWN_null, UNKNOWN_null},
};

#define set_term_funcp(change_p, term_p) set_term_funcp2((change_p), 0)
/* #define set_term_funcp3(change_p, term_p, tchange) \
			set_term_funcp2((change_p), (tchange)) */

/* This function should be called before any graphic code can be used... */
void
set_term_funcp2(FUNC_PTR change_p, TSET_FP tchange)
{
    SET_OUTFILE;
    my_term_ftable.change_term_p = change_p;
    my_term_ftable.loaded = 1;
    if (tchange) {
	my_term_ftable.term_set_outputp = tchange;
    }
}

/* Used from Math::Pari */
void
set_term_funcp3(FUNC_PTR change_p, void *term_p, TSET_FP tchange)
{
  set_term_funcp2(change_p, tchange);
}

void
set_term_ftable(struct t_ftable *p)
{
  SET_OUTFILE;
  my_term_ftablep = p;
}

#else /* !DYNAMIC_PLOTTING */

extern struct termentry term_tbl[];

#  define my_change_term	change_term
#  define my_term_tbl		term_tbl

extern void term_set_output(char *s);
extern void term_start_plot(void);
extern void term_end_plot(void);
extern void term_start_multiplot(void);
extern void term_end_multiplot(void);
extern void term_init(void);
extern void list_terms(void);

static void
plotsizes_scale(double x, double y)	{ xsize=x; ysize=y; }

static double
plotsizes_get(int flag)	{ return (flag ? ysize : xsize); }

struct t_ftable my_term_ftable =
{
	1, (FUNC_PTR)&change_term, &term_set_output,
	&plotsizes_scale, &plotsizes_get,
	{&term_start_plot, &term_end_plot, 
	 &term_start_multiplot, &term_end_multiplot, &term_init, &list_terms}
};

struct t_ftable *get_term_ftable()	{ SET_OUTFILE; return &my_term_ftable; }
void set_term_ftable()	{ SET_OUTFILE; }


void
set_term_funcp3(FUNC_PTR change_p, void *term_p, TSET_FP tchange)
{
    SET_OUTFILE;
    my_term_ftable.change_term_p = change_p;
    my_term_ftable.loaded = 1;
    if (tchange) {
	my_term_ftable.term_set_outputp = tchange;
    }
}

#define scaled_xmax()	((int)termprop(xmax)*xsize)
#define scaled_ymax()	((int)termprop(ymax)*ysize)

#endif /* !DYNAMIC_PLOTTING */

#define int_get_term_ftable()	((IV)get_term_ftable())
#define int_set_term_ftable(a) (v_set_term_ftable((void*)a))

void
v_set_term_ftable(void *a) { set_term_ftable((struct t_ftable*)a); }

void
setup_gpshim(void) { SET_OUTFILE; }

#ifdef SET_OPTIONS_FROM_STRING
/* This sets the tokens for the options */
void
set_tokens_string(char *start)
{
    char *s = start;
    char *tstart;
    int is_real, is_integer, has_exp;
    
    num_tokens = 0;
    while (num_tokens < MAX_TOKENS) {
	while (*s == ' ' || *s == '\t' || *s == '\n')
	    s++;
	if (!*s)
	    return;
	tstart = s;
	if (*s == ',') {
	    s++;
	    is_integer = is_real = 0;
	    goto process;
	}
	is_integer = is_real = ((*s) != 0);
	if (*s == '+' || *s == '-')
	    s++;
	has_exp = 0;
	while (*s && !(*s == ' ' || *s == '\t' || *s == '\n')) {
	    if (!(*s <= '9' && *s >= '0')) {
		if (*s == '.') {		
		    if (!is_integer)
			is_real = 0;
		    else if (is_integer == 1 && !(s[1] <= '9' && s[1] >= '0'))
			is_real = 0;
		} else if (*s == 'e' || *s == 'E') {
		    if (has_exp)
			is_real = 0;
		    has_exp = 1;
		    if (s[1] == '+' || s[1] == '-')
			s++;
		} else if (*s == ',' && (is_integer || is_real))
		    break;
		else
		    is_real = 0;
		is_integer = 0;
	    } else if (is_integer)
		is_integer++;
	    s++;	    
	}
      process:
	token[num_tokens].start_index = tstart - input_line;
	token[num_tokens].length = s - tstart;
	if (is_integer) {
	    token[num_tokens].is_token = 0;
	    token[num_tokens].l_val.type = INTGR;
	    token[num_tokens].l_val.v.int_val = atoi(tstart);
	} else if (is_real) {
	    token[num_tokens].is_token = 0;
	    token[num_tokens].l_val.type = CMPLX;
	    token[num_tokens].l_val.v.cmplx_val.real = atof(tstart);
	    token[num_tokens].l_val.v.cmplx_val.imag = 0;
	} else {
	    token[num_tokens].is_token = 1;
	}
	num_tokens++;
    }
    if (num_tokens >= MAX_TOKENS) {
	char buf[80];
	sprintf(buf, "panic: more than %d tokens for options", MAX_TOKENS);
	croak(buf);    
    }
}

void
set_options_from(char *s)
{
    char *o = input_line;

    input_line = s;		/* for error reports */
    set_tokens_string(s);
    options();
    input_line = o;
    c_token = num_tokens = 0;
}
#endif

#ifdef GNUPLOT_OUTLINE_STDOUT
int
StartOutput() {}

int
EndOutput() {}

int
OutLine(char *s)
{
   return fprintf(stdout, "%s", s);
}
#endif

#ifdef __cplusplus
  }
#endif
