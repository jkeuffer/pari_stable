/*******************************************************************/
/**                                                               **/
/**                 INPUT/OUTPUT SUBROUTINES                      **/
/**                                                               **/
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "anal.h"
GEN confrac(GEN x); /* should be static here, but use hiremainder */
GEN convi(GEN x);
static void bruti(GEN g, long n);
static void texi(GEN g, long nosign);
static void sori(GEN g);
char * type_name(long t);
static char format;
static long decimals, chmp, initial;

/* output a space or do nothing depending on original caller */
static void (*sp)();

void
hit_return()
{
  char tmp[16];
  pariputs("---- (type return to continue) ----");
  do fgets(tmp,16,stdin); while (tmp[strlen(tmp)-1] != '\n');
  /* \n has to be echoed later if we are under emacs (E. Kowalski) */
  pariputc('\n');
}

/********************************************************************/
/**                                                                **/
/**                        INPUT FILTER                            **/
/**                                                                **/
/********************************************************************/

#define ONE_LINE_COMMENT   2
#define MULTI_LINE_COMMENT 1
/* filter s in place. If status not a query, return pointer to ending '\0'.
 * return s / NULL otherwise
 */
char *
filtre(char *s, int status)
{
  static int in_string, in_comment = 0;
  char c, *t;
  int downcase;

  if (status & f_INIT) in_string = 0;
  switch(status)
  {
    case f_ENDFILE:
      if (in_string)
      {
        err(warner,"run-away string. Closing it");
        in_string = 0;
      }
      if (in_comment)
      {
        err(warner,"run-away comment. Closing it");
        in_comment = 0;
      } /* fall through */
    case f_INIT: case f_COMMENT:
      return in_comment? s: NULL;
  }
  downcase = ((status & f_KEEPCASE) == 0 && compatible == OLDALL);
  t = s;
  while ((c = *s++))
  {
    if (in_string) *t++ = c; /* copy verbatim */
    else if (in_comment)
    {
      if (in_comment == MULTI_LINE_COMMENT)
      {
        while (c != '*' || *s != '/')
        {
          if (!*s) { *t=0; return t; }
          c = *s++;
        }
        s++;
      }
      else
        while (c != '\n')
        {
          if (!*s)
          {
            if (status == f_READL) in_comment=0;
            *t=0; return t;
          }
          c = *s++;
        }
      in_comment=0; continue;
    }
    else
    { /* weed out comments and spaces */
      if (c=='\\' && *s=='\\') { in_comment = ONE_LINE_COMMENT; continue; }
      if (isspace((int)c)) continue;
      *t++ = downcase? tolower(c): c;
    }
    switch(c)
    {
      case '/':
        if (*s != '*' || in_string) break;
        /* start multi-line comment */
        t--; in_comment = MULTI_LINE_COMMENT; break;

      case '\\':
        if (!in_string) break;
        if (!*s) return t;     /* this will result in an error */
        *t++ = *s++; break; /* in strings, \ is the escape character */
        /*  \" does not end a string. But \\" does */

      case '"':
        in_string = !in_string;
    }
  }
  *t = 0; return t;
}
#undef ONE_LINE_COMMENT
#undef MULTI_LINE_COMMENT

GEN
lisGEN(FILE *fi)
{
  long size = 512, n = size;
  char *buf = gpmalloc(n), *s = buf;

  for(;;)
    if (fgets(s, n, fi))
    {
      if (s[strlen(s)-1] == '\n')
      {
        GEN x = flisexpr(buf);
        free(buf); return x;
      }
      buf = gprealloc(buf, size<<1, size);
      s = buf + (size-1); n = size+1; size <<= 1;
    }
}

/********************************************************************/
/**                                                                **/
/**                  GENERAL PURPOSE PRINTING                      **/
/**                                                                **/
/********************************************************************/
PariOUT *pariOut, *pariErr;

static void
normalOutC(char c)
{
  putc(c, pari_outfile);
  if (logfile) putc(c, logfile);
}
static void
normalOutS(char *s)
{
  fputs(s, pari_outfile);
  if (logfile) { fputs(s, logfile); }
}
static void
normalOutF(void)
{
  fflush(pari_outfile);
  if (logfile) fflush(logfile);
}
PariOUT defaultOut = {normalOutC, normalOutS, normalOutF, NULL};

static void
normalErrC(char c)
{
  putc(c, errfile);
  if (logfile) putc(c, logfile);
}
static void
normalErrS(char *s)
{
  fputs(s, errfile);
  if (logfile) fputs(s, logfile);
}
static void
normalErrF(void)
{
  fflush(errfile);
  if (logfile) fflush(logfile);
}
PariOUT defaultErr = {normalErrC, normalErrS, normalErrF, NULL};

void
initout(int initerr)
{
  infile = stdin; pari_outfile = stdout; errfile = stderr;
  pariOut = &defaultOut;
  if (initerr) pariErr = &defaultErr;
}

void
pariputc(char c) { pariOut->putch(c); }

void
pariputs(char *s) { pariOut->puts(s); }

void
pariflush(void) { pariOut->flush(); }

void
flusherr() { pariErr->flush(); }

/* format is standard printf format, except %Z is a GEN (cast to long) */
void
vpariputs(char* format, va_list args)
{
  char buf[1024], str[1024], *f = format, *s = str;
  long nb = 0;

  while (*f)
  {
    if (*f != '%') *s++ = *f++;
    else
    {
      if (f[1] != 'Z') { *s++ = *f++; *s++ = *f++; }
      else
      {
        strcpy(s,"\003%016ld\003"); /* brace with unprobable characters */
        nb++; s += 8; f += 2; /* skip %Z */
      }
    }
  }
  *s = 0; vsprintf(buf,str,args); s = buf;
  if (nb)
    for (f=s; *f; f++)
      if (*f == '\003' && f[17] == '\003')
      {
        *f = 0; f[17] = 0; /* remove the bracing chars */
        pariOut->puts(s); bruteall((GEN)atol(f+1),'g',-1,1);
        f += 18; s = f;
        nb--; if (!nb) break;
      }
  pariOut->puts(s);
}

void
pariputsf(char *format, ...)
{
  va_list args;

  va_start(args,format); vpariputs(format,args);
  va_end(args);
}

/* start printing in "color" c */
/* terminal has to support ANSI color escape sequences */
void
term_color(int c)
{
  pariputs(term_get_color(c));
}

void
decode_color(int n, int *c)
{
  if (n < 0) n = -n;
  c[1] = n & 0xf; n >>= 4; /* foreground */
  c[2] = n & 0xf; n >>= 4; /* background */
  c[0] = n & 0xf; /* attribute */
}

char *
term_get_color(int n)
{
  static char s[16];
  int c[3], a;

  if (disable_color) return "";
  if (n == c_NONE || (a = gp_colors[n]) == c_NONE)
    return "\033[0m"; /* reset */

  decode_color(a,c);
  if (c[1]<8) c[1] += 30; else c[1] += 82;
  if (a < 0)
    sprintf(s, "\033[%d;%dm", c[0], c[1]);
  else
  {
    if (c[2]<8) c[2] += 40; else c[2] += 92;
    sprintf(s, "\033[%d;%d;%dm", c[0], c[1], c[2]);
  }
  return s;
}

/********************************************************************/
/**                                                                **/
/**                  PRINTING BASED ON SCREEN WIDTH                **/
/**                                                                **/
/********************************************************************/
static int col_index, lin_index, max_width, max_lin;
void init_lim_lines(char *s, long max);
#ifdef HAS_TIOCGWINSZ
#  include <sys/termios.h>
#  include <sys/ioctl.h>
#endif

static int
term_width_intern()
{
#ifdef WINCE
	return 0;
#endif
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!under_emacs && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_col;
  }
#endif
#ifdef UNIX
  {
    char *str;
    if ((str = getenv("COLUMNS"))) return atoi(str);
  }
#endif
#ifdef __EMX__
  {
    int scrsize[2];
    _scrsize(scrsize); return scrsize[0];
  }
#endif
  return 0;
}

static int
term_height_intern()
{
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!under_emacs && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_row;
  }
#endif
#ifdef UNIX
  {
    char *str;
    if ((str = getenv("LINES"))) return atoi(str);
  }
#endif
#ifdef __EMX__
  {
    int scrsize[2];
    _scrsize(scrsize); return scrsize[1];
  }
#endif
  return 0;
}

#define DFT_TERM_WIDTH  80
#define DFT_TERM_HEIGHT 20

int
term_width()
{
  int n = term_width_intern();
  return (n>1)? n: DFT_TERM_WIDTH;
}

int
term_height()
{
  int n = term_height_intern();
  return (n>1)? n: DFT_TERM_HEIGHT;
}

#define MAX_WIDTH 76
/* output string wrapped after MAX_WIDTH characters (for gp -test) */
static void
putc80(char c)
{
  if (c == '\n') col_index = -1;
  else if (col_index == MAX_WIDTH)
    { putc('\n',pari_outfile); col_index = 0; }
  putc(c, pari_outfile); col_index++;
}
#undef MAX_WIDTH
static void
puts80(char *s)
{
  while (*s) putc80(*s++);
}
PariOUT pariOut80= {putc80, puts80, normalOutF, NULL};

void
init80(long n)
{
  col_index = n; pariOut = &pariOut80;
}

/* output stopped after max_line have been printed (for default(lines,)) */
static void
putc_lim_lines(char c)
{
  if (lin_index > max_lin) return;
  if (lin_index == max_lin)
    if (c == '\n' || col_index >= max_width-5)
    {
      normalOutS(term_get_color(c_ERR));
      normalOutS("[+++]"); lin_index++; return;
    }
  if (c == '\n')
  {
    col_index = -1; lin_index++;
  }
  else if (col_index == max_width)
  {
    col_index =  0; lin_index++;
  }
  col_index++; normalOutC(c);
}
static void
puts_lim_lines(char *s)
{
  long i,len;
  if (lin_index > max_lin) return;
  len = strlen(s);
  for(i=0; i<len; i++) putc_lim_lines(s[i]);
}

PariOUT pariOut_lim_lines= {putc_lim_lines, puts_lim_lines, normalOutF, NULL};

/* s = prefix already printed (print up to max lines) */
void
init_lim_lines(char *s, long max)
{
  if (!max) return;
  max_width = term_width();
  max_lin = max;
  lin_index = 1; col_index = strlen(s);
  pariOut = &pariOut_lim_lines;
}

#define is_blank_or_null(c) (!(c) || is_blank(c))
#define is_blank(c) ((c) == ' ' || (c) == '\n')
#define MAX_WORD_LEN 255

static void
_new_line(char *prefix)
{
  pariputc('\n'); if (prefix) pariputs(prefix);
}

/* output: <prefix>< s wrapped at EOL >
 *         <prefix>< ... > <str>
 *                         ^---
 * If str is NULL, omit the arrow
 * If prefix is NULL, use ""
 */
void
print_prefixed_text(char *s, char *prefix, char *str)
{
  long prelen = prefix? strlen(prefix): 0;
  long oldwlen=0, linelen=prelen, w = term_width();
  char word[MAX_WORD_LEN+1], oldword[MAX_WORD_LEN+1], *u=word;

  if (prefix) pariputs(prefix);
  oldword[0]='\0';
  while ((*u++ = *s++))
  {
    if (is_blank_or_null(*s))
    {
      while (is_blank(*s)) s++;
      linelen += oldwlen;
      if (linelen >= w)
      {
        _new_line(prefix);
        linelen = oldwlen + prelen;
      }
      pariputs(oldword); *u++ = ' '; *u = '\0'; oldwlen = u-word;
      if (*s) { strcpy(oldword,word);  u = word; }
    }
  }
  if (!str)
    { if (u[-2] != '.') u[-2] = '.'; }
  else
    { *(u-2) = 0; oldwlen--; }
  linelen += oldwlen;
  if (linelen >= w) { _new_line(prefix); linelen = prelen + oldwlen; }
  pariputs(word);
  if (str)
  {
    long i,len = strlen(str);
    int space = (*str == ' ' && str[1]);
    if (linelen + len >= w)
    {
      _new_line(prefix); linelen = prelen;
      if (space) { str++; len--; space = 0; }
    }
    pariputs(str); if (str[len-1] != '\n') pariputc('\n');
    if (space) { linelen++; len--; }
    for (i=0; i<linelen; i++) pariputc(' ');
    pariputc('^');
    for (i=0; i<len; i++) pariputc('-');
  }
  pariputc('\n');
}

/********************************************************************/
/**                                                                **/
/**                    GEN <---> CHARACTER STRINGS                 **/
/**                                                                **/
/********************************************************************/

typedef struct outString {
  char *string;
  ulong len,size;
} outString;
static outString *OutStr, *ErrStr = NULL;

#define STEPSIZE 1024
#define check_output_length(str,l) { \
  const ulong s = str->size; \
  if (str->len + l >= s) { \
    ulong t = s + l + STEPSIZE; \
    str->string = gprealloc(str->string, t, s); \
    str->size = t; \
  } \
}

#define str_putc(str, c) { \
  check_output_length(str,1); \
  str->string[str->len++] = c; \
}
static void
outstr_putc(char c) { str_putc(OutStr, c); }
static void
errstr_putc(char c) { str_putc(ErrStr, c); }

#define str_puts(str, s) {\
  const long len=strlen(s); \
  check_output_length(str,len); \
  strcpy(str->string+str->len,s); \
  str->len += len; \
}
static void
outstr_puts(char *s) { str_puts(OutStr, s); }
static void
errstr_puts(char *s) { str_puts(ErrStr, s); }

static void
outstr_flush(void) { /* empty */ }
PariOUT pariOut2Str = {outstr_putc, outstr_puts, outstr_flush, NULL};
PariOUT pariErr2Str = {errstr_putc, errstr_puts, outstr_flush, NULL};
#undef STEPSIZE

char *
pari_strdup(char *s)
{
   int n = strlen(s)+1;
   char *t = gpmalloc(n);
   memcpy(t,s,n); return t;
}

/* returns a malloc-ed string, which should be freed after usage */
char *
GENtostr0(GEN x, void(*do_out)(GEN))
{
  PariOUT *tmp = pariOut;
  outString *tmps = OutStr, newStr;

  if (typ(x) == t_STR) return pari_strdup(GSTR(x));
  pariOut = &pariOut2Str; OutStr = &newStr;
  OutStr->len = 0; OutStr->size=0; OutStr->string=NULL;
  do_out(x); OutStr->string[OutStr->len] = 0;

  pariOut = tmp; OutStr = tmps; return newStr.string;
}

char *
GENtostr(GEN x) { return GENtostr0(x,outbrute); }
/********************************************************************/
/**                                                                **/
/**                         TEXMACS INTERFACE                      **/
/**                                                                **/
/********************************************************************/
extern jmp_buf environnement;
#include "TeXmacs.h"
static TeXmacs_exports_1 *TeXmacs;

static char *
pari_evaluate(char *s, char *session, char **fail)
{
  static PariOUT *tmp;
  static outString *tmps;
  outString newStr;
  long av = avma;
  char *t;

  (void)session;
  tmp = pariErr; pariErr = &pariErr2Str;
  tmps = ErrStr; ErrStr  = &newStr;
  ErrStr->len = 0; ErrStr->size=0; ErrStr->string=NULL;
  if (setjmp(environnement))
  {
    if (!ErrStr)
    {
      tmps = ErrStr; ErrStr  = &newStr;
      ErrStr->string=pari_strdup("Leaving Pari");
      ErrStr->len=strlen(ErrStr->string);
    }
    t = NULL;
  }
  else
  {
    char *s2 = GENtostr(flisexpr(s));
    t = TeXmacs->translate_prg(s2,"pari/pari_out","pari/tm_out");
    avma = av; free(s2);
  }
  if (ErrStr->string) ErrStr->string[ErrStr->len] = 0;
  *fail = ErrStr->string;
  pariErr = tmp; ErrStr = tmps; return t;
}

static char *
pari_install(TeXmacs_exports_1 *_TeXmacs, char *options, char **fail)
{
  (void)options;
  TeXmacs = _TeXmacs;
  pari_init(1000000, 500000);
  if (setjmp(environnement))
  {
    *fail = pari_strdup("Pari Error");
    return NULL;
  }
  else
  {
    *fail = NULL;
    return pari_strdup("Pari Ready");
  }
}

static char *
pari_execute(char *s, char *session, char **fail)
{
  (void)s; (void)session;
  *fail = NULL; return pari_strdup("");
}

static package_exports_1 PARI_exports_1 = {
  "TeXmacs communication protocol 1", 
  PARIVERSION,
  &pari_install,
  &pari_evaluate,
  &pari_execute
};

package_exports_1 *
get_pari_package(int i)
{
  (void)i;
  return &PARI_exports_1;
}

/********************************************************************/
/**                                                                **/
/**                         WRITE AN INTEGER                       **/
/**                                                                **/
/********************************************************************/
#define putsigne(x) pariputs((x>0)? " + " : " - ")
#define sp_sign_sp(x) sp(), pariputc(x>0? '+': '-'), sp()
#define sp_plus_sp() sp(), pariputc('+'), sp()
#define comma_sp() pariputc(','), sp()

static void wr_space() {pariputc(' ');}
static void no_space() {}

static void
blancs(long nb) { while (nb-- > 0) pariputc(' '); }

static void
zeros(long nb)  { while (nb-- > 0) pariputc('0'); }

static long
coinit(long x)
{
  char cha[10], *p = cha + 9;

  *p = 0;
  do { *--p = x%10 + '0'; x /= 10; } while (x);
  pariputs(p); return 9 - (p - cha);
}

static void
comilieu(long x)
{
  char cha[10], *p = cha + 9;

  for (*p = 0; p > cha; x /= 10) *--p = x%10 + '0';
  pariputs(cha);
}

static void
cofin(long x, long decim)
{
  char cha[10], *p = cha + 9;

  for (; p > cha; x /= 10) *--p = x%10 + '0';
  cha[decim] = 0; pariputs(cha);
}

static long
nbdch(long l)
{
  if (l<100000)
  {
    if (l<10) return 1;
    if (l<100) return 2;
    if (l<1000) return 3;
    if (l<10000) return 4;
    return 5;
  }
  if (l<1000000) return 6;
  if (l<10000000) return 7;
  if (l<100000000) return 8;
  if (l<1000000000) return 9;
  return 10; /* not reached */
}

/* write an int. fw = field width (pad with ' ') */
static void
wr_int(GEN x, long fw, long nosign)
{
  long *res,*re,i, sx=signe(x);

  if (!sx) { blancs(fw-1); pariputc('0'); return; }
  setsigne(x,1); re = res = convi(x);
  setsigne(x,sx);
  i = nbdch(*--re); while (*--re >= 0) i+=9;
  if (nosign || sx>0) blancs(fw-i);
  else
     { i++; blancs(fw-i); pariputc('-'); }
  coinit(*--res); while (*--res >= 0) comilieu(*res);
}

static void
wr_vecsmall(GEN g)
{
  long i,l;
  pariputc('['); l = lg(g);
  for (i=1; i<l; i++)
  {
    pariputsf("%ld", g[i]);
    if (i<l-1) comma_sp();
  }
  pariputc(']');
}
/********************************************************************/
/**                                                                **/
/**                        WRITE A REAL NUMBER                     **/
/**                                                                **/
/********************************************************************/
static void wr_exp(GEN x);

/* assume x != 0 and print |x| in floating point format */
static void
wr_float(GEN x)
{
  long *res, ex,s,d,e,decmax,deceff, dec = decimals;
  GEN p1;

  if (dec>0) /* round if needed */
  {
    GEN arrondi = cgetr(3);
    arrondi[1] = (long) (x[1]-((double)BITS_IN_LONG/pariK)*dec-2);
    arrondi[2] = x[2]; x = addrr(x,arrondi);
  }
  ex = expo(x);
  if (ex >= bit_accuracy(lg(x))) { wr_exp(x); return; }

/* integer part */
  p1 = gcvtoi(x,&e); s = signe(p1);
  if (e > 0) err(bugparier,"wr_float");
  if (!s) { pariputc('0'); d=1; }
  else
  {
    setsigne(p1,1); res = convi(p1); d = coinit(*--res);
    setsigne(p1,s);
    while (*(--res) >= 0) { d += 9; comilieu(*res); }
    x = subri(x,p1);
  }
  pariputc('.');

/* fractional part: 0 < x < 1 */
  if (!signe(x))
  {
    if (dec<0) dec=(long) (-expo(x)*L2SL10+1);
    dec -= d; if (dec>0) zeros(dec);
    return;
  }
  if (!s)
  {
    for(;;)
    {
      p1=mulsr(1000000000,x); if (expo(p1)>=0) break;
      pariputs("000000000"); x=p1;
    }
    for(;;)
    {
      p1=mulsr(10,x); if (expo(p1)>=0) break;
      pariputc('0'); x=p1;
    }
    d=0;
  }
  res = (long *) confrac(x); decmax = d + *res++;
  if (dec<0) dec=decmax;
  deceff = dec-decmax; dec -= d;
  while (dec>8)
  {
    if (dec>deceff) comilieu(*res++); else pariputs("000000000");
    dec -= 9;
  }
  if (dec>0)
  {
    if (dec>deceff) cofin(*res,dec); else zeros(dec);
  }
}

/* as above in exponential format */
static void
wr_exp(GEN x)
{
  GEN dix = cgetr(lg(x)+1);
  long ex = expo(x);

  ex = (ex>=0)? (long)(ex*L2SL10): (long)(-(-ex*L2SL10)-1);
  affsr(10,dix); if (ex) x = mulrr(x,gpuigs(dix,-ex));
  if (absr_cmp(x, dix) >= 0) { x=divrr(x,dix); ex++; }
  wr_float(x); sp(); pariputsf("E%ld",ex);
}

/* Write real number x.
 * format: e (exponential), f (floating point), g (as f unless x too small)
 *   if format isn't correct (one of the above) act as e.
 * decimals: number of decimals to print (all if <0).
 */
#define print_float(fo,ex) ((fo == 'g' && ex >= -32) || fo == 'f')
static void
wr_real(GEN x, long nosign)
{
  long ltop, sx = signe(x), ex = expo(x);

  if (!sx) /* real 0 */
  {
    if (print_float(format,ex))
    {
      if (decimals<0)
      {
        long d = 1+((-ex)>>TWOPOTBITS_IN_LONG);
        if (d < 0) d = 0;
        decimals=(long)(pariK*d);
      }
      pariputs("0."); zeros(decimals);
    }
    else
    {
      ex = (ex>=0)? (long)(ex*L2SL10): (long)(-(-ex*L2SL10)-1);
      pariputsf("0.E%ld", ex+1);
    }
    return;
  }
  if (!nosign && sx < 0) pariputc('-'); /* print sign if needed */
  ltop = avma;
  if (print_float(format,ex)) wr_float(x); else wr_exp(x);
  avma = ltop;
}
#undef print_float

void
ecrire(GEN x, char f, long d, long fw)
{
  if (typ(x)==t_INT)
    wr_int(x,fw,0);
  else
  {
    sp = &wr_space; format = f; decimals = d;
    wr_real(x,0);
  }
}

/********************************************************************/
/**                                                                **/
/**                       HEXADECIMAL OUTPUT                       **/
/**                                                                **/
/********************************************************************/

static void
sorstring(char* b, long x)
{
#ifdef LONG_IS_64BIT
  pariputsf(b,(ulong)x>>32,x & MAXHALFULONG);
#else
  pariputsf(b,x);
#endif
}

/* English ordinal numbers -- GN1998Apr17 */
static const char *ordsuff[4] = {"st","nd","rd","th"};

const char*
eng_ord(long i)                        /* i > 0 assumed */
{
  switch (i%10)
  {
    case 1:
      if (i%100==11) return ordsuff[3]; /* xxx11-th */
      return ordsuff[0];         /* xxx01-st, xxx21-st,... */
    case 2:
      if (i%100==12) return ordsuff[3]; /* xxx12-th */
      return ordsuff[1];         /* xxx02-nd, xxx22-nd,... */
    case 3:
      if (i%100==13) return ordsuff[3]; /* xxx13-th */
      return ordsuff[2];         /* xxx03-rd, xxx23-rd,... */
    default:
      return ordsuff[3];         /* xxxx4-th,... */
  }
}

static void
voir2(GEN x, long nb, long bl)
{
  long tx=typ(x),i,j,e,dx,lx=lg(x);

  if (tx == t_INT && x == gzero) { pariputs("gzero\n"); return; }
  sorstring(VOIR_STRING1,(ulong)x);
  if (tx!=t_POL && tx!=t_SER)
    pariputsf("%s%c", type_name(tx)+2, isclone(x)?'!':'|');
  else
    pariputsf("%s %d%c", type_name(tx)+2, varn(x), isclone(x)?'!':'|');
  if (! is_recursive_t(tx)) /* t_SMALL, t_INT, t_REAL, t_STR, t_VECSMALL */
  {
    if (nb<0) nb = (tx==t_INT)? lgefint(x): lx;
    if (tx == t_SMALL) x = (GEN)&x;
    for (i=0; i<nb; i++) sorstring(VOIR_STRING2,x[i]);
    pariputc('\n'); return;
  }

  if (tx == t_POL || tx == t_LIST) lx = lgef(x);
  for (i=0; i<lx; i++) sorstring(VOIR_STRING2,x[i]);
  bl+=2; pariputc('\n');
  switch(tx)
  {
    case t_INTMOD: case t_POLMOD:
    {
      char *s = (tx==t_INTMOD)? "int = ": "pol = ";
      if (isonstack(x[1])) blancs(bl); else { blancs(bl-2); pariputs("* "); }
      pariputs("mod = "); voir2((GEN)x[1],nb,bl);
      blancs(bl); pariputs(s);        voir2((GEN)x[2],nb,bl);
      break;
    }
    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      blancs(bl); pariputs("num = "); voir2((GEN)x[1],nb,bl);
      blancs(bl); pariputs("den = "); voir2((GEN)x[2],nb,bl);
      break;

    case t_COMPLEX:
      blancs(bl); pariputs("real = "); voir2((GEN)x[1],nb,bl);
      blancs(bl); pariputs("imag = "); voir2((GEN)x[2],nb,bl);
      break;

    case t_PADIC:
      blancs(bl-2); pariputsf("precp : %d   valp : %d\n", precp(x), valp(x));
      if (isonstack(x[2])) blancs(bl); else { blancs(bl-2); pariputs("* "); }
      pariputs("  p : "); voir2((GEN)x[2],nb,bl);
      blancs(bl); pariputs("p^l : "); voir2((GEN)x[3],nb,bl);
      blancs(bl); pariputs("  I : "); voir2((GEN)x[4],nb,bl);
      break;

    case t_QUAD:
      blancs(bl); pariputs("pol = ");  voir2((GEN)x[1],nb,bl);
      blancs(bl); pariputs("real = "); voir2((GEN)x[2],nb,bl);
      blancs(bl); pariputs("imag = "); voir2((GEN)x[3],nb,bl);
      break;

    case t_POL: case t_SER:
      if (tx == t_SER)
      {
	blancs(bl); pariputsf("prec : %d   valp : %d\n", lg(x)-2, valp(x));
      }
      e = (tx==t_SER)? valp(x): 0;
      for (i=2; i<lx; i++)
      {
	blancs(bl); pariputsf("coef of degree %ld = ",e);
	e++; voir2((GEN)x[i],nb,bl);
      }
      break;

    case t_LIST: case t_QFR: case t_QFI: case t_VEC: case t_COL:
      i = (tx==t_LIST)? 2: 1;
      for (   ; i<lx; i++)
      {
        blancs(bl); pariputsf("%ld%s component = ",i,eng_ord(i));
	voir2((GEN)x[i],nb,bl);
      }
      break;

    case t_MAT:
      if (lx==1) return;
      dx=lg((GEN)x[1]);
      for (i=1; i<dx; i++)
	for (j=1; j<lx; j++)
	{
	  blancs(bl); pariputsf("mat(%ld,%ld) = ",i,j);
	  voir2(gcoeff(x,i,j),nb,bl);
	}
  }
}

void
voir(GEN x, long nb)
{
  voir2(x,nb,0);
}

char *
type_name(long t)
{
  char *s;
  switch(t)
  {
    case t_SMALL  : s="t_SMALL";   break;
    case t_INT    : s="t_INT";     break;
    case t_REAL   : s="t_REAL";    break;
    case t_INTMOD : s="t_INTMOD";  break;
    case t_FRAC   : s="t_FRAC";    break;
    case t_FRACN  : s="t_FRACN";   break;
    case t_COMPLEX: s="t_COMPLEX"; break;
    case t_PADIC  : s="t_PADIC";   break;
    case t_QUAD   : s="t_QUAD";    break;
    case t_POLMOD : s="t_POLMOD";  break;
    case t_POL    : s="t_POL";     break;
    case t_SER    : s="t_SER";     break;
    case t_RFRAC  : s="t_RFRAC";   break;
    case t_RFRACN : s="t_RFRACN";  break;
    case t_QFR    : s="t_QFR";     break;
    case t_QFI    : s="t_QFI";     break;
    case t_VEC    : s="t_VEC";     break;
    case t_COL    : s="t_COL";     break;
    case t_MAT    : s="t_MAT";     break;
    case t_LIST   : s="t_LIST";    break;
    case t_STR    : s="t_STR";     break;
    case t_VECSMALL:s="t_VECSMALL";break;
  }
  return s;
}

/********************************************************************/
/**                                                                **/
/**                        FORMATTED OUTPUT                        **/
/**                                                                **/
/********************************************************************/
static char *
get_var(long v, char *buf)
{
  entree *ep = varentries[v];

  if (ep) return ep->name;
  if (v==MAXVARN) return "#";
  sprintf(buf,"#<%d>",(int)v); return buf;
}

static char *
get_texvar(long v, char *buf)
{
  entree *ep = varentries[v];
  char *s, *t = buf;

  if (!ep) err(talker, "this object uses debugging variables");
  s = ep->name;
  if (strlen(s)>=64) err(talker, "TeX variable name too long");
  while(isalpha((int)*s)) *t++ = *s++;
  *t = 0; if (isdigit((int)*s) || *s++ == '_') sprintf(t,"_{%s}",s);
  return buf;
}

static void
monome(char *v, long deg)
{
  if (deg)
  {
    pariputs(v);
    if (deg!=1) pariputsf("^%ld",deg);
  }
  else pariputc('1');
}

static void
texnome(char *v, long deg)
{
  if (deg)
  {
    pariputs(v);
    if (deg!=1) pariputsf("^{%ld}",deg);
  }
  else pariputc('1');
}

#define padic_nome(p,e) {pariputs(p); if (e != 1) pariputsf("^%ld",e);}
#define padic_texnome(p,e) {pariputs(p); if (e != 1) pariputsf("^{%ld}",e);}

void
etatpile(unsigned int n)
{
  long av=avma,nu,i,l,m;
  GEN adr,adr1;
  double r;

  nu = (top-avma)/BYTES_IN_LONG;
  l = (top-bot)/BYTES_IN_LONG;
  r = 100.0*nu/l;
  pariputsf("\n Top : %lx   Bottom : %lx   Current stack : %lx\n",
          top, bot, avma);

  pariputsf(" Used :                         %ld  long words  (%ld K)\n",
           nu, nu/1024*BYTES_IN_LONG);

  pariputsf(" Available :                    %ld  long words  (%ld K)\n",
           (l-nu), (l-nu)/1024*BYTES_IN_LONG);

  pariputsf(" Occupation of the PARI stack : %6.2f percent\n",r);

  adr=getheap();
  pariputsf(" %ld objects on heap occupy %ld long words\n\n",
                 itos((GEN)adr[1]), itos((GEN)adr[2]));
  avma=av;

  pariputsf(" %ld variable names used out of %d\n\n",manage_var(3,NULL),MAXVARN);
  if (!n) return;

  if (n>nu) n=nu; adr=(GEN)avma; adr1=adr+n;
  while (adr<adr1)
  {
    sorstring(VOIR_STRING3,(ulong)adr);
    l=lg(adr); m = (adr==polvar) ? MAXVARN : 0;
    for (i=0; i<l && adr<adr1; i++,adr++) sorstring(VOIR_STRING2,*adr);
    pariputc('\n'); adr=polvar+m;
  }
  pariputc('\n');
}

/********************************************************************/
/**                                                                **/
/**                           RAW OUTPUT                           **/
/**                                                                **/
/********************************************************************/
#define isnull_for_pol(g)  ((typ(g)==t_INTMOD)? !signe(g[2]): isnull(g))

/* is to be printed as '0' */
static long
isnull(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_SMALL:
      return !smalltos(g);
    case t_INT:
      return !signe(g);
    case t_COMPLEX:
      return isnull((GEN)g[1]) && isnull((GEN)g[2]);
    case t_QUAD:
      return isnull((GEN)g[2]) && isnull((GEN)g[3]);
    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      return isnull((GEN)g[1]);
    case t_POLMOD:
      return isnull((GEN)g[2]);
    case t_POL:
      for (i=lgef(g)-1; i>1; i--)
	if (!isnull((GEN)g[i])) return 0;
      return 1;
  }
  return 0;
}

/* return 1 or -1 if g is 1 or -1, 0 otherwise*/
static long
isone(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_SMALL:
      switch(smalltos(g))
      {
        case  1: return  1;
        case -1: return -1;
      }
      break;
    case t_INT:
      return (signe(g) && is_pm1(g))? signe(g): 0;
    case t_COMPLEX:
      return isnull((GEN)g[2])? isone((GEN)g[1]): 0;
    case t_QUAD:
      return isnull((GEN)g[3])? isone((GEN)g[2]): 0;
    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      return isone((GEN)g[1]) * isone((GEN)g[2]);
    case t_POL:
      if (!signe(g)) return 0;
      for (i=lgef(g)-1; i>2; i--)
	if (!isnull((GEN)g[i])) return 0;
      return isone((GEN)g[2]);
  }
  return 0;
}

/* if g is a "monomial", return its sign, 0 otherwise */
static long
isfactor(GEN g)
{
  long i,deja,sig;
  switch(typ(g))
  {
    case t_INT: case t_REAL:
      return (signe(g)<0)? -1: 1;
    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      return isfactor((GEN)g[1]);
    case t_COMPLEX:
      if (isnull((GEN)g[1])) return isfactor((GEN)g[2]);
      if (isnull((GEN)g[2])) return isfactor((GEN)g[1]);
      return 0;
    case t_PADIC:
      return !signe((GEN)g[4]);
    case t_QUAD:
      if (isnull((GEN)g[2])) return isfactor((GEN)g[3]);
      if (isnull((GEN)g[3])) return isfactor((GEN)g[2]);
      return 0;
    case t_POL: deja = 0; sig = 1;
      for (i=lgef(g)-1; i>1; i--)
        if (!isnull((GEN)g[i]))
	{
	  if (deja) return 0;
	  sig=isfactor((GEN)g[i]); deja=1;
	}
      return sig? sig: 1;
    case t_SER:
      for (i=lg(g)-1; i>1; i--)
        if (!isnull((GEN)g[i])) return 0;
  }
  return 1;
}

/* return 1 if g is a "truc" (see anal.c) */
static long
isdenom(GEN g)
{
  long i,deja;
  switch(typ(g))
  {
    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      return 0;
    case t_COMPLEX: return isnull((GEN)g[2]);
    case t_PADIC: return !signe((GEN)g[4]);
    case t_QUAD: return isnull((GEN)g[3]);

    case t_POL: deja = 0;
      for (i=lgef(g)-1; i>1; i--)
        if (!isnull((GEN)g[i]))
	{
	  if (deja) return 0;
	  if (i==2) return isdenom((GEN)g[2]);
	  if (!isone((GEN)g[i])) return 0;
	  deja=1;
	}
      return 1;
    case t_SER:
      for (i=lg(g)-1; i>1; i--)
	if (!isnull((GEN)g[i])) return 0;
  }
  return 1;
}

/* write a * v^d */
static void
wr_monome(GEN a, char *v, long d)
{
  long sig = isone(a);

  if (sig) { sp_sign_sp(sig); monome(v,d); }
  else
  {
    sig = isfactor(a);
    if (sig) { sp_sign_sp(sig); bruti(a,sig); }
    else
    {
      sp_plus_sp(); pariputc('('); bruti(a,sig); pariputc(')');
    }
    if (d) { pariputc('*'); monome(v,d); }
  }
}

static void
wr_texnome(GEN a, char *v, long d)
{
  long sig = isone(a);

  if (sig) { putsigne(sig); texnome(v,d); }
  else
  {
    sig = isfactor(a);
    if (sig) { putsigne(sig); texi(a,sig); }
    else
    {
      pariputs("+("); texi(a,sig); pariputc(')');
    }
    if (d) texnome(v,d);
  }
}

static void
wr_lead_monome(GEN a, char *v, long d, long nosign)
{
  long sig = isone(a);
  if (sig)
  {
    if (!nosign && sig<0) pariputc('-');
    monome(v,d);
  }
  else
  {
    if (isfactor(a)) bruti(a,nosign);
    else
    {
      pariputc('('); bruti(a,0); pariputc(')');
    }
    if (d) { pariputc('*'); monome(v,d); }
  }
}

static void
wr_lead_texnome(GEN a, char *v, long d, long nosign)
{
  long sig = isone(a);
  if (sig)
  {
    if (!nosign && sig<0) pariputc('-');
    texnome(v,d);
  }
  else
  {
    if (isfactor(a)) texi(a,nosign);
    else
    {
      pariputc('('); texi(a,0); pariputc(')');
    }
    if (d) texnome(v,d);
  }
}

static void
bruti(GEN g, long nosign)
{
  long tg,l,i,j,r;
  GEN a,b;
  char *v, buf[32];

  if (!g) { pariputs("NULL"); return; }
  if (isnull(g)) { pariputc('0'); return; }
  r = isone(g);
  if (r)
  {
    if (!nosign && r<0) pariputc('-');
    pariputc('1'); return;
  }

  tg = typ(g);
  switch(tg)
  {
    case t_SMALL: pariputsf("%ld",smalltos(g)); break;
    case t_INT: wr_int(g,0,nosign); break;
    case t_REAL: wr_real(g,nosign); break;

    case t_INTMOD: case t_POLMOD:
      pariputs(new_fun_set? "Mod(": "mod(");
      bruti((GEN)g[2],0); comma_sp();
      bruti((GEN)g[1],0); pariputc(')'); break;

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      r = isfactor((GEN)g[1]); if (!r) pariputc('(');
      bruti((GEN)g[1],nosign);
      if (!r) pariputc(')');
      pariputc('/');
      r = isdenom((GEN)g[2]); if (!r) pariputc('(');
      bruti((GEN)g[2],0);
      if (!r) pariputc(')');
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = (GEN)g[r+1]; b = (GEN)g[r+2]; v = r? "w": "I";
      if (isnull(a))
      {
        wr_lead_monome(b,v,1,nosign);
        return;
      }
      bruti(a,nosign);
      if (!isnull(b)) wr_monome(b,v,1);
      break;

    case t_POL: v = get_var(ordvar[varn(g)], buf);
      /* hack: we want g[i] = coeff of degree i. */
      i = lgef(g)-3; g += 2; while (isnull((GEN)g[i])) i--;
      wr_lead_monome((GEN)g[i],v,i,nosign);
      while (i--)
      {
        a = (GEN)g[i];
        if (!isnull_for_pol(a)) wr_monome(a,v,i);
      }
      break;

    case t_SER: v = get_var(ordvar[varn(g)], buf);
      i = valp(g);
      if (signe(g))
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g += (2-i);
        wr_lead_monome((GEN)g[i],v,i,nosign);
        while (++i < l)
        {
          a = (GEN)g[i];
          if (!isnull_for_pol(a)) wr_monome(a,v,i);
        }
        sp_plus_sp();
      }
      pariputs("O("); monome(v,i); pariputc(')'); break;

    case t_PADIC:
    {
      GEN p = (GEN)g[2];
      i = valp(g); l = precp(g)+i;
      g = (GEN)g[4]; v = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int(a,0,1); if (i) pariputc('*');
	  }
	  if (i) padic_nome(v,i);
          sp_plus_sp();
	}
      }
      pariputs("O("); padic_nome(v,i); pariputc(')');
      free(v); break;
    }

    case t_QFR: case t_QFI: r = (tg == t_QFR);
      if (new_fun_set) pariputs("Qfb("); else pariputs(r? "qfr(": "qfi(");
      bruti((GEN)g[1],0); comma_sp();
      bruti((GEN)g[2],0); comma_sp();
      bruti((GEN)g[3],0);
      if (r) { comma_sp(); bruti((GEN)g[4],0); }
      pariputc(')'); break;

    case t_VEC: case t_COL:
      pariputc('['); l = lg(g);
      for (i=1; i<l; i++)
      {
        bruti((GEN)g[i],0);
        if (i<l-1) comma_sp();
      }
      pariputc(']'); if (tg==t_COL) pariputc('~');
      break;
    case t_VECSMALL: wr_vecsmall(g); break;

    case t_LIST:
      pariputs("List(["); l = lgef(g);
      for (i=2; i<l; i++)
      {
        bruti((GEN)g[i],0);
        if (i<l-1) comma_sp();
      }
      pariputs("])"); break;

    case t_STR:
      pariputc('"'); pariputs(GSTR(g)); pariputc('"');
      return;

    case t_MAT:
      r = lg(g); if (r==1) { pariputs("[;]"); return; }
      l = lg(g[1]);
      if (l==1)
      { 
        pariputsf(new_fun_set? "matrix(0,%ld)":"matrix(0,%ld,j,k,0)", r-1);
        return;
      }
      if (l==2) 
      {
        pariputs(new_fun_set? "Mat(": "mat(");
        if (r == 2) { bruti(gcoeff(g,1,1),0); pariputc(')'); return; }
      }
      pariputc('[');
      for (i=1; i<l; i++)
      {
	for (j=1; j<r; j++)
	{
	  bruti(gcoeff(g,i,j),0);
          if (j<r-1) comma_sp();
	}
	if (i<l-1) { pariputc(';'); sp(); }
      }
      pariputc(']'); if (l==2) pariputc(')');
      break;

    default: sorstring(VOIR_STRING2,*g);
  }
}

static void
matbruti(GEN g, long flag)
{
  long i,j,r,l;

  if (typ(g) != t_MAT) { bruti(g,flag); return; }

  r=lg(g); if (r==1 || lg(g[1])==1) { pariputs("[;]\n"); return; }
  pariputc('\n'); l = lg(g[1]);
  for (i=1; i<l; i++)
  {
    pariputc('[');
    for (j=1; j<r; j++)
    {
      bruti(gcoeff(g,i,j),0); if (j<r-1) pariputc(' ');
    }
    if (i<l-1) pariputs("]\n\n"); else pariputs("]\n");
  }
}

static void
sor_monome(GEN a, char *v, long d)
{
  long sig = isone(a);
  if (sig) { putsigne(sig); monome(v,d); }
  else
  {
    sig = isfactor(a);
    if (sig) { putsigne(sig); if (sig < 0) a = gneg(a); }
    else pariputs(" + ");
    sori(a); if (d) { pariputc(' '); monome(v,d);}
  }
}

static void
sor_lead_monome(GEN a, char *v, long d)
{
  long sig = isone(a);
  if (sig)
  {
    if (sig < 0) pariputc('-');
    monome(v,d);
  }
  else
  {
    sori(a);
    if (d) { pariputc(' '); monome(v,d); }
  }
}

static void
sori(GEN g)
{
  long tg=typ(g), i,j,r,l,close_paren;
  GEN a,b;
  char *v, buf[32];

  switch (tg)
  {
    case t_SMALL: pariputsf("%ld",smalltos(g)); return;
    case t_INT: wr_int(g,chmp,0); return;
    case t_REAL: wr_real(g,0); return;
    case t_STR:
      pariputc('"'); pariputs(GSTR(g)); pariputc('"'); return;
    case t_LIST:
      chmp=0; pariputs("List(");
      for (i=2; i<lgef(g); i++)
      {
	sori((GEN)g[i]); if (i<lgef(g)-1) pariputs(", ");
      }
      pariputs(")\n"); return;
  }
  close_paren=0;
  if (!is_matvec_t(tg)) chmp = 0;
  if (!is_graphicvec_t(tg))
  {
    if (is_frac_t(tg) && gsigne(g) < 0) pariputc('-');
    if (! is_rfrac_t(tg)) { pariputc('('); close_paren=1; }
  }
  switch(tg)
  {
    case t_INTMOD: case t_POLMOD:
      a = (GEN)g[2]; b = (GEN)g[1];
      if (tg == t_INTMOD && signe(a) < 0) a = addii(a,b);
      sori(a); pariputs(" mod "); sori(b); break;
	
    case t_FRAC: case t_FRACN:
      a=(GEN)g[1]; wr_int(a,chmp,1); pariputs(" /");
      b=(GEN)g[2]; wr_int(b,chmp,1); break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = (GEN)g[r+1]; b = (GEN)g[r+2]; v = r? "w": "I";
      if (isnull(a)) { sor_lead_monome(b,v,1); break; }
      sori(a); if (!isnull(b)) sor_monome(b,v,1);
      break;

    case t_PADIC:
    {
      GEN p = (GEN)g[2];
      i = valp(g); l = precp(g)+i;
      g = (GEN)g[4]; v = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int(a,chmp,1); pariputc(i? '*': ' ');
	  }
	  if (i) { padic_nome(v,i); pariputc(' '); }
          pariputs("+ ");
	}
      }
      pariputs("O(");
      if (!i) pariputs(" 1)"); else padic_nome(v,i);
      pariputc(')'); free(v); break;
    }

    case t_POL:
      if (!signe(g)) { pariputc('0'); break; }
      v = get_var(ordvar[varn(g)],buf);
      i = lgef(g)-3; g += 2; while (isnull((GEN)g[i])) i--;
      sor_lead_monome((GEN)g[i],v,i);
      while (i--)
      {
        a = (GEN)g[i]; if (!isnull_for_pol(a)) sor_monome(a,v,i);
      }
      break;
	
    case t_SER: v = get_var(ordvar[varn(g)],buf);
      i = valp(g);
      if (signe(g))
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g += (2-i);
        sor_lead_monome((GEN)g[i],v,i);
        while (++i < l)
        {
          a = (GEN)g[i]; if (!isnull_for_pol(a)) sor_monome(a,v,i);
        }
        pariputs(" + ");
      }
      pariputs("O(");
      if (!i) pariputs(" 1)"); else monome(v,i);
      pariputc(')'); break;

    case t_RFRAC: case t_RFRACN:
    if (initial)
    {
      char *v1, *v2;
      long sd = 0, sn = 0, d,n;
      long wd = term_width();

      initial = 0;
      v1 = GENtostr0((GEN)g[1], &sori); n = strlen(v1);
      v2 = GENtostr0((GEN)g[2], &sori); d = strlen(v2);

      pariputc('\n');
      i = max(n,d)+2;
      if (i > wd)
      {
        pariputs(v1); pariputs("\n\n");
        for (j=0; j<wd; j++) pariputc('-');
        pariputs("\n\n");
        pariputs(v2);
        pariputc('\n'); return;
      }
      if (n < d) sn = (d-n) >> 1; else sd = (n-d) >> 1;
      blancs(sn+1); pariputs(v1);
      pariputs("\n\n"); for (j=0; j<i; j++) pariputc('-');
      pariputs("\n\n");
      blancs(sd+1); pariputs(v2);
      pariputc('\n'); return;
    }
    pariputc('('); sori((GEN)g[1]); pariputs(" / "); sori((GEN)g[2]);
    pariputc(')'); return;
	
    case t_QFR: case t_QFI: pariputc('{');
      sori((GEN)g[1]); pariputs(", ");
      sori((GEN)g[2]); pariputs(", ");
      sori((GEN)g[3]);
      if (tg == t_QFR) { pariputs(", "); sori((GEN)g[4]); }
      pariputs("}\n"); break;
	
    case t_VEC:
      chmp=0; pariputc('[');
      for (i=1; i<lg(g); i++)
      {
	sori((GEN)g[i]); if (i<lg(g)-1) pariputs(", ");
      }
      pariputc(']'); break;
    case t_VECSMALL: wr_vecsmall(g); break;

    case t_COL:
      if (lg(g)==1) { pariputs("[]\n"); return; }
      pariputc('\n');
      for (i=1; i<lg(g); i++)
      {
        pariputc('['); sori((GEN)g[i]); pariputs("]\n");
      }
      break;
	
    case t_MAT:
    {
      long lx = lg(g);

      if (lx==1) { pariputs("[;]\n"); return; }
      pariputc('\n'); l=lg((GEN)g[1]);
      for (i=1; i<l; i++)
      {
	pariputc('[');
	for (j=1; j<lx; j++)
	{
	  sori(gcoeff(g,i,j)); if (j<lx-1) pariputc(' ');
	}
	pariputs("]\n"); if (i<l-1) pariputc('\n');
      }
      break;
    }
    default: sorstring(VOIR_STRING2,*g);
  }
  if (close_paren) pariputc(')');
}

/********************************************************************/
/**                                                                **/
/**                           TeX OUTPUT                           **/
/**                                                                **/
/********************************************************************/

/* this follows bruti exactly */
static void
texi(GEN g, long nosign)
{
  long tg,i,j,l,r;
  GEN a,b;
  char *v, buf[67];

  if (isnull(g)) { pariputs("{0}"); return; }
  r = isone(g); pariputc('{');
  if (r)
  {
    if (!nosign && r<0) pariputc('-');
    pariputs("1}"); return;
  }

  tg = typ(g);
  switch(tg)
  {
    case t_INT: wr_int(g,0,nosign); break;
    case t_REAL: wr_real(g,nosign); break;

    case t_INTMOD: case t_POLMOD:
      texi((GEN)g[2],0); pariputs("mod");
      texi((GEN)g[1],0); break;

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      texi((GEN)g[1],nosign); pariputs("\\over");
      texi((GEN)g[2],0); break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = (GEN)g[r+1]; b = (GEN)g[r+2]; v = r? "w": "I";
      if (isnull(a))
      {
        wr_lead_texnome(b,v,1,nosign);
        break;
      }
      texi(a,nosign);
      if (!isnull(b)) wr_texnome(b,v,1);
      break;

    case t_POL: v = get_texvar(ordvar[varn(g)],buf);
      /* hack: we want g[i] = coeff of degree i. */
      i = lgef(g)-3; g += 2; while (isnull((GEN)g[i])) i--;
      wr_lead_texnome((GEN)g[i],v,i,nosign);
      while (i--)
      {
        a = (GEN)g[i];
        if (!isnull_for_pol(a)) wr_texnome(a,v,i);
      }
      break;

    case t_SER: v = get_texvar(ordvar[varn(g)],buf);
      i = valp(g);
      if (signe(g))
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g += (2-i);
        wr_lead_texnome((GEN)g[i],v,i,nosign);
        while (++i < l)
        {
          a = (GEN)g[i];
          if (!isnull_for_pol(a)) wr_texnome(a,v,i);
        }
        pariputc('+');
      }
      pariputs("O("); texnome(v,i); pariputc(')'); break;

    case t_PADIC:
    {
      GEN p = (GEN)g[2];
      i = valp(g); l = precp(g)+i;
      g = (GEN)g[4]; v = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int(a,0,1); if (i) pariputs("\\cdot");
	  }
	  if (i) padic_texnome(v,i);
	  pariputc('+');
	}
      }
      pariputs("O("); padic_texnome(v,i); pariputc(')');
      free(v); break;
    }
    case t_QFR: case t_QFI: r = (tg == t_QFR);
      if (new_fun_set) pariputs("Qfb("); else pariputs(r? "qfr(": "qfi(");
      texi((GEN)g[1],0); pariputs(", ");
      texi((GEN)g[2],0); pariputs(", ");
      texi((GEN)g[3],0);
      if (r) { pariputs(", "); texi((GEN)g[4],0); }
      pariputc(')'); break;

    case t_VEC:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi((GEN)g[i],0); if (i<lg(g)-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_LIST:
      pariputs("\\pmatrix{ "); l = lgef(g);
      for (i=2; i<l; i++)
      {
	texi((GEN)g[i],0); if (i<lgef(g)-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_COL:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi((GEN)g[i],0); pariputs("\\cr\n");
      }
      pariputc('}'); break;

    case t_STR:
      pariputs("\\mbox{"); pariputs(GSTR(g));
      pariputc('}'); break;

    case t_MAT:
      pariputs("\\pmatrix{\n "); r = lg(g);
      if (r>1)
      {
        l = lg(g[1]);
        for (i=1; i<l; i++)
        {
          for (j=1; j<r; j++)
          {
            texi(gcoeff(g,i,j),0); if (j<r-1) pariputc('&');
          }
          pariputs("\\cr\n ");
        }
      }
      pariputc('}'); break;
  }
  pariputc('}');
}

/*******************************************************************/
/**                                                               **/
/**                        USER OUTPUT FUNCTIONS                  **/
/**                                                               **/
/*******************************************************************/

void
bruteall(GEN g, char f, long d, long flag)
{
  long av = avma;
  void (*oldsp)() = sp;

  sp = flag? &wr_space: &no_space;
  format = f; decimals = d;
  bruti(changevar(g,polvar),0);
  sp = oldsp; avma = av;
}

void
matbrute(GEN g, char f, long d)
{
  long av=avma; sp = &wr_space;
  format = f; decimals = d;
  matbruti(changevar(g,polvar),0); avma=av;
}

void
sor(GEN g, char f, long d, long c)
{
  long av=avma; sp = &wr_space;
  format = f; decimals = d; chmp = c; initial = 1;
  sori(changevar(g,polvar)); avma = av;
}

void
texe(GEN g, char f, long d)
{
  long av=avma; sp = &no_space;
  format = f; decimals = d;
  texi(changevar(g,polvar),0); avma=av;
}

void
brute(GEN g, char format, long decimals) { bruteall(g,format,decimals,1); }

void
outbrute(GEN g) { bruteall(g,'g',-1,1); }

void
outsor(GEN g) { sor(g,'g',-1,1); }

void
output(GEN x)
{
  outbrute(x); pariputc('\n'); pariflush();
}

void
outmat(GEN x)
{
  matbrute(x,'g',-1); pariputc('\n'); pariflush();
}

void
outbeaut(GEN x)
{
  outsor(x); pariputc('\n'); pariflush();
}

void
outerr(GEN x)
{
  PariOUT *out = pariOut; pariOut = pariErr;
  output(x); pariOut = out;
}

void
outbeauterr(GEN x)
{
  PariOUT *out = pariOut; pariOut = pariErr;
  outbeaut(x); pariOut = out;
}

void
bruterr(GEN x,char format,long decimals)
{
  PariOUT *out = pariOut; pariOut = pariErr;
  bruteall(x,format,decimals,1); pariOut = out;
}

void
fprintferr(char* format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  va_start(args, format); vpariputs(format,args);
  va_end(args); pariOut = out;
}

/*******************************************************************/
/**                            FILES                              **/
/*******************************************************************/
/* stack of temporary files (includes all infiles + some output) */
static pariFILE *last_tmp_file = NULL;
/* stack of "permanent" (output) files */
static pariFILE *last_file = NULL;
#if defined(UNIX) || defined(__EMX__)
#  include <pwd.h>
#  ifdef __EMX__
#    include <process.h>
#  endif
#  define HAVE_PIPES
#endif

pariFILE *
newfile(FILE *f, char *name, int type)
{
  pariFILE *file = (pariFILE*) gpmalloc(strlen(name) + 1 + sizeof(pariFILE));
  file->type = type;
  file->name = strcpy((char*)(file+1), name);
  file->file = f;
  file->next = NULL;
  if (type & mf_PERM)
  {
    file->prev = last_file;
    last_file = file;
  }
  else
  {
    file->prev = last_tmp_file;
    last_tmp_file = file;
  }
  if (file->prev) (file->prev)->next = file;
  if (DEBUGFILES)
    fprintferr("I/O: opening file %s (code %d) \n",name,type);
  return file;
}

static void
pari_kill_file(pariFILE *f)
{
  if ((f->type & mf_PIPE) == 0)
  {
    if (fclose(f->file)) err(warnfile, "close", f->name);
  }
#ifdef HAVE_PIPES
  else
  {
    if (f->type & mf_FALSE)
    {
      if (fclose(f->file)) err(warnfile, "close", f->name);
      if (unlink(f->name)) err(warnfile, "delete", f->name);
    }
    else
      if (pclose(f->file) < 0) err(warnfile, "close pipe", f->name);
  }
#endif
  if (DEBUGFILES)
    fprintferr("I/O: closing file %s (code %d) \n",f->name,f->type);
  free(f);
}

void
pari_fclose(pariFILE *f)
{
  if (f->next) (f->next)->prev = f->prev; else last_tmp_file = f->prev;
  if (f->prev) (f->prev)->next = f->next;
  pari_kill_file(f);
}

pariFILE *
pari_fopen(char *s, char *mode)
{
  FILE *f = fopen(s, mode);
  if (!f) err(talker, "could not open requested file %s", s);
  if (DEBUGFILES)
    fprintferr("I/O: opening file %s (mode %s)\n", s, mode);
  return newfile(f,s,0);
}

void
pari_unlink(char *s)
{
  if (unlink(s)) err(warner, "I/O: can\'t remove file %s", s);
  else if (DEBUGFILES)
    fprintferr("I/O: removed file %s\n", s);
}

/* Remove one INFILE from the stack. Reset infile (to the most recent infile)
 * Return -1, if we're trying to pop out stdin itself; 0 otherwise
 * Check for leaked file handlers (temporary files)
 */
int
popinfile()
{
  pariFILE *f;

  filtre(NULL, f_ENDFILE);
  for (f = last_tmp_file; f; f = f->prev)
  {
    if (f->type & mf_IN) break;
    err(warner, "I/O: leaked file descriptor (%d): %s",
		f->type, f->name);
    pari_fclose(f);
  }
  last_tmp_file = f; if (!last_tmp_file) return -1;
  pari_fclose(last_tmp_file);
  for (f = last_tmp_file; f; f = f->prev)
    if (f->type & mf_IN) { infile = f->file; return 0; }
  infile = stdin; return 0;
}

static void
kill_file_stack(pariFILE **s)
{
  pariFILE *f = *s;
  while (f)
  {
    pariFILE *t = f->prev;
    pari_kill_file(f);
    *s = f = t; /* have to update *s in case of ^C */
  }
}

void
killallfiles(int leaving)
{
  if (leaving)
  {
    popinfile(); /* look for leaks */
    kill_file_stack(&last_file);
  }
  kill_file_stack(&last_tmp_file);
  infile = stdin;
}

pariFILE *
try_pipe(char *cmd, int flag)
{
#ifndef HAVE_PIPES
  err(archer); return NULL;
#else
  FILE *file;
  char *f;

#  ifdef __EMX__
  if (_osmode == DOS_MODE) /* no pipes under DOS */
  {
    char *s;
    if (flag & mf_OUT) err(archer);
    f = pari_unique_filename("pipe");
    s = gpmalloc(strlen(cmd)+strlen(f)+4);
    sprintf(s,"%s > %s",cmd,f);
    if (system(s)) file = NULL;
    else
    {
      file = (FILE *) fopen(f,"r");
      flag |= mf_FALSE;
    }
    free(s);
  }
  else
#  endif
  {
    file = (FILE *) popen(cmd, (flag & mf_OUT)? "w": "r");
    if (flag & mf_OUT) flag |= mf_PERM;
    f = "";
  }
  if (!file) err(talker,"%s failed !",cmd);
  return newfile(file, f, mf_PIPE|flag);
#endif
}
/*******************************************************************/
/**                                                               **/
/**                   GP STANDARD INPUT AND OUTPUT                **/
/**                                                               **/
/*******************************************************************/
static char *last_filename = NULL;
static char **dir_list = NULL;

/* expand tildes in filenames, return a malloc'ed buffer */
static char *
_expand_tilde(char *s)
{
#if !defined(UNIX) && !defined(__EMX__)
  return pari_strdup(s);
#else
  struct passwd *p;
  char *u;
  int len;

  if (*s != '~') return pari_strdup(s);
  s++; u = s; /* skip ~ */
  if (!*s || *s == '/') p = getpwuid(geteuid());
  else
  {
    char *tmp;
    while (*u && *u != '/') u++;
    len = u-s;
    tmp = strncpy(gpmalloc(len+1),s,len);
    tmp[len] = 0;
    p = getpwnam(tmp); free(tmp);
  }
  if (!p) err(talker2,"unknown user ",s,s-1);
  s = gpmalloc(strlen(p->pw_dir) + strlen(u) + 1);
  sprintf(s,"%s%s",p->pw_dir,u); return s;
#endif
}

/* expand environment variables in str, return a malloc'ed buffer
 * assume no \ remain and str can be freed */
static char *
_expand_env(char *str)
{
#if defined(WINCE) || defined(macintosh)
  return str;
#else
  long i, l, len = 0, xlen = 16, xnum = 0;
  char *s = str, *s0 = s, *env;
  char **x = (char **)gpmalloc(xlen * sizeof(char*));

  while (*s)
  {
    if (*s != '$') { s++; continue; }
    l = s - s0;
    if (l)
    {
      s0 = strncpy(gpmalloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    if (xnum > xlen - 3) /* need room for possibly two more elts */
    {
      long xnew = xlen << 1;
      x = (char **)gprealloc((void*)x, xlen * sizeof(char*),
                                       xnew * sizeof(char*));
      xlen = xnew;
    }

    s0 = ++s; /* skip $ */
    while (is_keyword_char(*s)) s++;
    l = s - s0;
    env = strncpy(gpmalloc(l+1), s0, l); env[l] = 0;
    s0 = getenv(env);
    if (!s0)
    {
      err(warner,"undefined environment variable: %s",env);
      s0 = "";
    }
    l = strlen(s0);
    if (l)
    {
      s0 = strncpy(gpmalloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    free(env); s0 = s;
  }
  l = s - s0;
  if (l)
  {
    s0 = strncpy(gpmalloc(l+1), s0, l); s0[l] = 0;
    x[xnum++] = s0; len += l;
  }

  s = gpmalloc(len+1); *s = 0;
  for (i = 0; i < xnum; i++) { (void)strcat(s, x[i]); free(x[i]); }
  free(str); free(x); return s;
#endif
}

char *
expand_tilde(char *s)
{
  return _expand_env(_expand_tilde(s));
}

#if defined __EMX__ || defined _WIN32
#  define PATH_SEPARATOR ';'
#else
#  define PATH_SEPARATOR ':'
#endif

void
gp_expand_path(char *v)
{
  char **path, **old, *s;
  int i, n = 0;

  v = pari_strdup(v);
  for (s=v; *s; s++)
    if (*s == PATH_SEPARATOR) { *s = 0; n++; }
  path = (char**) gpmalloc((n + 2)*sizeof(char *));

  for (s=v, i=0; i<=n; i++)
  {
    char *end = s + strlen(s), *f = end;
    while (f > s && *--f == '/') *f = 0;
    path[i] = expand_tilde(s);
    s = end + 1; /* next path component */
  }
  path[i] = NULL; old = dir_list; dir_list = path;
  if (old)
  {
    for (path=old; *path; path++) free(*path);
    free(old);
  }
}

/* name is a malloc'ed (existing) filename. Accept it as new infile
 * (unzip if needed). */
static FILE *
accept_file(char *name, FILE *file)
{
  if (! last_tmp_file)
  {  /* empty file stack, record this name */
    if (last_filename) free(last_filename);
    last_filename = pari_strdup(name);
  }
#ifdef ZCAT
  {
    long l = strlen(name);
    char *end = name + l-1;

    if (l > 2 && (!strncmp(end-1,".Z",2)
#ifdef GNUZCAT
               || !strncmp(end-2,".gz",3)
#endif
    ))
    { /* compressed file (compress or gzip) */
      char *cmd = gpmalloc(strlen(ZCAT) + l + 2);
      sprintf(cmd,"%s %s",ZCAT,name);
      fclose(file); infile = try_pipe(cmd, mf_IN)->file;
      free(cmd); return infile;
    }
  }
#endif
  return infile = newfile(file, name, mf_IN)->file;
}

/* If a file called "name" exists (possibly after appending ".gp")
 * record it in the file_stack (as a pipe if compressed).
 * name is malloc'ed, we free it before returning
 */
static FILE *
try_name(char *name)
{
  FILE *file = fopen(name, "r");
  if (file) return accept_file(name,file);

  { /* try appending ".gp" to name */
    char *s = gpmalloc(strlen(name)+4);
    sprintf(s, "%s.gp", name);
    file = fopen(s, "r");
    if (file) file = accept_file(s,file);
    free(s);
  }
  free(name); return file;
}

/* If name = "", re-read last file */
void
switchin(char *name0)
{
  char *s, *name;

  if (*name0)
    name = expand_tilde(name0);
  else
  {
    if (last_filename == NULL)
      err(talker,"You never gave me anything to read!");
    name0 = last_filename;
    name = pari_strdup(name0);
  }
  /* if name contains '/',  don't use dir_list */
  s=name; while (*s && *s != '/') s++;
  if (*s) { if (try_name(name)) return; }
  else
  {
    char **tmp = dir_list;
    for ( ; *tmp; tmp++)
    { /* make room for '/' and '\0', try_name frees it */
      s = gpmalloc(2 + strlen(*tmp) + strlen(name));
      sprintf(s,"%s/%s",*tmp,name);
      if (try_name(s)) return;
    }
  }
  err(openfiler,"input",name0);
}

void
switchout(char *name)
{
  if (name)
  {
    FILE *f = fopen(name, "a");
    if (!f) err(openfiler,"output",name);
    pari_outfile = f;
  }
  else if (pari_outfile != stdout)
  {
    fclose(pari_outfile);
    pari_outfile = stdout;
  }
}

/*******************************************************************/
/**                                                               **/
/**                       TEMPORARY FILES                         **/
/**                                                               **/
/*******************************************************************/
#ifdef __WIN32
#  include <process.h> /* for getpid */
#endif

#ifndef R_OK
#  define R_OK 4
#  define W_OK 2
#  define X_OK 1
#  define F_OK 0
#endif

#ifdef __EMX__
#include <io.h>
static int
unix_shell()
{
  char *base, *sh = getenv ("EMXSHELL");
  if (sh == NULL) sh = getenv ("COMSPEC");
  if (sh == NULL) return 0;
  base = _getname (sh);
  if (stricmp (base, "cmd.exe") == 0 || stricmp (base, "4os2.exe") == 0
      || stricmp (base, "command.com") == 0
      || stricmp (base, "4dos.com") == 0)
    return 0;
  return 1;
}
#endif

/* check if s has rwx permissions for us */
static int
pari_is_rwx(char *s)
{
#if defined(UNIX) || defined (__EMX__) /* TODO: ok for macintosh? */
  return access(s, R_OK | W_OK | X_OK) == 0;
#else
  return 1;
#endif
}

static int
pari_file_exists(char *s)
{
#if defined(UNIX) || defined (__EMX__)
  return access(s, F_OK) == 0;
#else
  return 0;
#endif
}

#ifndef macintosh
char *
env_ok(char *s)
{
#ifdef WINCE
	return NULL;
#else
  char *t = getenv(s);
  if (t && pari_is_rwx(t) == 0)
  {
    err(warner,"%s is set (%s), but is not writeable", s,t);
    t = NULL;
  }
  return t;
#endif
}
#endif

static char*
pari_tmp_dir()
{
#ifdef WINCE
	char *s;

	s = env_ok("TEMP"); if (s) return s;
	return "\\temp";
#else
#ifndef macintosh
  char *s;

  s = env_ok("GPTMPDIR"); if (s) return s;
  s = env_ok("TMPDIR"); if (s) return s;
#ifdef __EMX__
  s = env_ok("TMP"); if (s) return s;
  s = env_ok("TEMP"); if (s) return s;
#endif
#endif
#if defined(UNIX) || defined(__EMX__)
  if (pari_is_rwx("/var/tmp")) return "/var/tmp";
  if (pari_is_rwx("/tmp")) return "/tmp";
#endif
  return ".";
#endif
}

/* Return a "unique filename" built from the string s, possibly the user id
 * and the process pid (on Unix systems). A "temporary" directory name is
 * prepended. The name returned is stored in a static buffer (gpmalloc'ed
 * permanently). It is DOS-safe (s truncated to 8 chars)
 */
char*
pari_unique_filename(char *s)
{
  static char *buf, *pre, *post = NULL;

  if (!post || !s) /* initialize */
  {
    char suf[64];
    int lpre, lsuf;

    if (post) free(post);
    pre = pari_tmp_dir();
#ifdef UNIX
    sprintf(suf,".%ld.%ld", (long)getuid(), (long)getpid());
#else
    sprintf(suf,".gpa");
#endif
    lsuf = strlen(suf);
    lpre = strlen(pre);
    /* room for suffix + '\0 + prefix + '/' + s + suffix '\0' */
    /*          ^- post        ^- buf         ^- pre          */
    post = (char*) gpmalloc(lpre + 1 + 8 + 2*(lsuf + 1));
    strcpy(post, suf);
    buf = post + lsuf; *buf = 0; buf++;
    strcpy(buf, pre);
    if (buf[lpre-1] != '/') { (void)strcat(buf, "/"); lpre++; }
#ifdef __EMX__
    if (!unix_shell())
      for (pre=buf; *pre; pre++)
	if (*pre == '/') *pre = '\\';
#endif
#ifdef WINCE
	for (pre=buf; *pre; pre++) 
		if (*pre == '/') *pre = '\\';
#endif
    pre = buf + lpre; if (!s) return s;
  }
  sprintf(pre, "%.8s%s", s, post);
  if (pari_file_exists(buf))
  {
    char c, *end = buf + strlen(buf) - 1;
    for (c='a'; c<='z'; c++)
    {
      *end = c;
      if (! pari_file_exists(buf)) break;
    }
    if (c > 'z')
      err(talker,"couldn't find a suitable name for a tempfile (%s)",s);
  }
  return buf;
}
