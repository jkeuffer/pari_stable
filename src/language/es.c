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
/**                                                               **/
/**                 INPUT/OUTPUT SUBROUTINES                      **/
/**                                                               **/
/*******************************************************************/
#include "pari.h"
#include "anal.h"
extern char *type_name(long t);

void
hit_return(void)
{
  int c;
  if (GP_DATA && (GP_DATA->flags & (EMACS|TEXMACS))) return;
  pariputs("---- (type RETURN to continue) ----");
  /* if called from a readline callback, may be in a funny TTY mode,  */
  do c = fgetc(stdin); while (c >= 0 && c != '\n' && c != '\r' && c != ' ');
  pariputc('\n');
}

/********************************************************************/
/**                                                                **/
/**                        INPUT FILTER                            **/
/**                                                                **/
/********************************************************************/
#define ONE_LINE_COMMENT   2
#define MULTI_LINE_COMMENT 1
/* Filter F->s into F->t */
char *
filtre0(filtre_t *F)
{
  const int downcase = F->downcase;
  char c, *s = F->s, *t;

  if (!F->t) F->t = gpmalloc(strlen(s)+1);
  t = F->t;

  if (F->more_input == 1) F->more_input = 0;

  if (! (F->in_comment | F->in_string))
  {
    while (isspace((int)*s)) s++; /* Skip space */
    if (*s == LBRACE) { s++; F->more_input = 2; F->wait_for_brace = 1; }
  }

  while ((c = *s++))
  {
    if (F->in_string)
    {
      *t++ = c; /* copy verbatim */
      switch(c)
      {
        case '\\': /* in strings, \ is the escape character */
          if (*s) *t++ = *s++;
          break;

        case '"': F->in_string = 0;
      }
      continue;
    }

    if (F->in_comment)
    { /* look for comment's end */
      if (F->in_comment == MULTI_LINE_COMMENT)
      {
        while (c != '*' || *s != '/')
        {
          if (!*s) 
          {
            if (!F->more_input) F->more_input = 1;
            goto END;
          }
          c = *s++;
        }
        s++;
      }
      else
        while (c != '\n' && *s) c = *s++;
      F->in_comment = 0;
      continue;
    }

    /* weed out comments and spaces */
    if (c=='\\' && *s=='\\') { F->in_comment = ONE_LINE_COMMENT; continue; }
    if (isspace((int)c)) continue;
    *t++ = downcase? tolower(c): c;

    switch(c)
    {
      case '/':
        if (*s == '*') { t--; F->in_comment = MULTI_LINE_COMMENT; }
        break;

      case '\\':
        if (!*s) {
          if (t[-2] == '?') break; /* '?\' */
          t--;
          if (!F->more_input) F->more_input = 1;
          goto END;
        }
        if (*s == '\n') {
          if (t[-2] == '?') break; /* '?\' */
          t--; s++;
          if (!*s)
          {
            if (!F->more_input) F->more_input = 1;
            goto END;
          }
        } /* skip \<CR> */
        break;

      case '"': F->in_string = 1;
    }
  }

  if (t != F->t) /* non empty input */
  {
    c = t[-1]; /* = last input char */
    if (c == '=')                 F->more_input = 2;
    else if (! F->wait_for_brace) F->more_input = 0;
    else if (c == RBRACE)       { F->more_input = 0; t--; }
  }

END:
  F->end = t; *t = 0; return F->t;
}
#undef ONE_LINE_COMMENT
#undef MULTI_LINE_COMMENT

char *
filtre(char *s, int downcase)
{
  filtre_t T;
  T.s = s;    T.in_string = 0; T.more_input = 0;
  T.t = NULL; T.in_comment= 0; T.wait_for_brace = 0;
  T.downcase = downcase;
  return filtre0(&T);
}

GEN
lisGEN(FILE *fi)
{
  long size = 512, n = size;
  char *buf = gpmalloc(n), *s = buf;

  while (fgets(s, n, fi))
  {
    if (s[strlen(s)-1] == '\n')
    {
      GEN x = flisexpr(buf);
      free(buf); return x;
    }
    buf = gprealloc(buf, size<<1);
    s = buf + (size-1); n = size+1; size <<= 1;
  }
#if defined(UNIX) || defined(__EMX__)
  if (!feof(fi))
#endif
    err(talker, "failed read from file");
  return NULL;
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
normalOutS(const char *s)
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
normalErrS(const char *s)
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

/**                         GENERIC PRINTING                       **/
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
pariputs(const char *s) { pariOut->puts(s); }

void
pariflush(void) { pariOut->flush(); }

void
flusherr(void) { pariErr->flush(); }

/* format is standard printf format, except %Z is a GEN */
void
vpariputs(const char* format, va_list args)
{
  long nb = 0, bufsize = 1023;
  const char *f = format;
  char *buf, *str, *s, *t;
  
  /* replace each %Z (2 chars) by braced address format (8 chars) */
  s = str = gpmalloc(strlen(format)*4 + 1);
  while (*f)
  {
    if (*f != '%') *s++ = *f++;
    else
    {
      if (f[1] != 'Z') { *s++ = *f++; *s++ = *f++; }
      else
      {
        strcpy(s,"\003%020ld\003"); /* brace with unprobable characters */
        nb++; s += 8; f += 2; /* skip %Z */
      }
    }
  }
  *s = 0;
#ifdef HAS_VSNPRINTF
  for(;;)
  {
    int l;
    buf = gpmalloc(bufsize);
    l = vsnprintf(buf,bufsize,str,args);
    if (l < 0) l = bufsize<<1; else if (l < bufsize) break;
    free(buf); bufsize++;
  }
  buf[bufsize] = 0; /* just in case */
#else
  buf = gpmalloc(bufsize);
  (void)vsprintf(buf,str,args); /* pray it does fit */
#endif
  t = s = buf;
  if (nb)
    while (*t)
    {
      if (*t == '\003' && t[21] == '\003')
      {
        *t = 0; t[21] = 0; /* remove the bracing chars */
        pariOut->puts(s); bruteall((GEN)atol(t+1),'g',-1,1);
        t += 22; s = t;
        if (!--nb) break; 
      }
      else
        t++;
    }
  pariOut->puts(s); free(buf); free(str);
}

void
pariputsf(const char *format, ...)
{
  va_list args;

  va_start(args,format); vpariputs(format,args);
  va_end(args);
}

/* start printing in "color" c */
/* terminal has to support ANSI color escape sequences */
#ifdef ESC
#  undef ESC
#endif
#define ESC  (0x1f & '[') /* C-[ = escape */

void
term_color(int c)
{
  pariputs(term_get_color(c));
}

void
decode_color(int n, int *c)
{
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
    sprintf(s, "%c[0m",ESC); /* reset */
  else
  {
    decode_color(a,c);
    if (c[1]<8) c[1] += 30; else c[1] += 82;
    if (a & (1<<12)) /* transparent background */
      sprintf(s, "%c[%d;%dm", ESC, c[0], c[1]);
    else
    {
      if (c[2]<8) c[2] += 40; else c[2] += 92;
      sprintf(s, "%c[%d;%d;%dm", ESC, c[0], c[1], c[2]);
    }
  }
  return s;
}

/********************************************************************/
/**                                                                **/
/**                  PRINTING BASED ON SCREEN WIDTH                **/
/**                                                                **/
/********************************************************************/
static int col_index, lin_index, max_width, max_lin;
#ifdef HAS_TIOCGWINSZ
#  include <sys/termios.h>
#  include <sys/ioctl.h>
#endif

static int
term_width_intern(void)
{
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!(GP_DATA && (GP_DATA->flags & (EMACS|TEXMACS)))
     && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_col;
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
term_height_intern(void)
{
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!(GP_DATA && (GP_DATA->flags & (EMACS|TEXMACS)))
     && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_row;
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
term_width(void)
{
  int n = term_width_intern();
  return (n>1)? n: DFT_TERM_WIDTH;
}

int
term_height(void)
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
puts80(const char *s)
{
  while (*s) putc80(*s++);
}
PariOUT pariOut80= {putc80, puts80, normalOutF, NULL};

static void
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
puts_lim_lines(const char *s)
{
  long i,len;
  if (lin_index > max_lin) return;
  len = strlen(s);
  for(i=0; i<len; i++) putc_lim_lines(s[i]);
}

PariOUT pariOut_lim_lines= {putc_lim_lines, puts_lim_lines, normalOutF, NULL};

/* n = length of prefix already printed (print up to max lines) */
void
lim_lines_output(GEN z, pariout_t *fmt, long n, long max)
{
  PariOUT *tmp = pariOut;
  max_width = term_width();
  max_lin = max;
  lin_index = 1;
  col_index = n;
  pariOut = &pariOut_lim_lines;
  gen_output(z, fmt);
  pariOut = tmp;
}

#define is_blank_or_null(c) (!(c) || is_blank(c))
#define is_blank(c) ((c) == ' ' || (c) == '\n')
#define MAX_WORD_LEN 255

static void
_new_line(char *prefix)
{
  pariputc('\n'); if (prefix) pariputs(prefix);
}

static long
strlen_real(char *s)
{
  char *t = s, *t0;
  long ctrl_len = 0;
  while (*t)
  {
    t0 = t;
    if (*t++ == ESC && *t++ == '[')
    {
      while (*t && *t++ != 'm') /* empty */;
      ctrl_len += t - t0;
    }
  }
  return strlen(s) - ctrl_len;
}

/* output: <prefix>< s wrapped at EOL >
 *         <prefix>< ... > <str>
 *                         ^---  (no \n at the end)
 * If str is NULL, omit the arrow, assume the text doesn't contain ASCII
 * escape sequences and end the text with '\n'. If prefix is NULL, use ""
 */
void
print_prefixed_text(char *s, char *prefix, char *str)
{
  long prelen = prefix? strlen_real(prefix): 0;
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
      pariputs(oldword); *u++ = ' '; *u = 0;
      /* u-word = strlen(word) */
      oldwlen = str ? strlen_real(word): u - word;
      if (*s) { strcpy(oldword,word);  u = word; }
    }
  }
  if (!str)
  { /* add final period if needed */
    u--; while (u > word && is_blank_or_null(*u)) u--;
    if (u >= word && isalnum((int)*u)) { u[1] = '.'; u[2] = 0; }
  }
  else
    { *(u-2) = 0; oldwlen--; }
  linelen += oldwlen;
  if (linelen >= w) { _new_line(prefix); linelen = prelen + oldwlen; }
  pariputs(word);
  if (str)
  {
    long i,len = strlen_real(str);
    int space = (*str == ' ' && str[1]);
    if (linelen + len >= w)
    {
      _new_line(prefix); linelen = prelen;
      if (space) { str++; len--; space = 0; }
    }
    term_color(c_OUTPUT);
    pariputs(str); if (!len || str[len-1] != '\n') pariputc('\n');
    if (space) { linelen++; len--; }
    term_color(c_ERR);
    for (i=0; i<linelen; i++) pariputc(' ');
    pariputc('^');
    for (i=0; i<len; i++) pariputc('-');
  }
  else
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
    str->size = s + l + STEPSIZE; \
    str->string = gprealloc(str->string, str->size); \
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
outstr_puts(const char *s) { str_puts(OutStr, s); }
static void
errstr_puts(const char *s) { str_puts(ErrStr, s); }

static void
outstr_flush(void) { /* empty */ }
PariOUT pariOut2Str = {outstr_putc, outstr_puts, outstr_flush, NULL};
PariOUT pariErr2Str = {errstr_putc, errstr_puts, outstr_flush, NULL};
#undef STEPSIZE

char *
pari_strdup(const char *s)
{
  int n = strlen(s)+1;
  char *t = gpmalloc(n);
  memcpy(t,s,n); return t;
}

/* returns a malloc-ed string, which should be freed after usage */
char *
GENtostr0(GEN x, pariout_t *T, void (*do_out)(GEN, pariout_t*))
{
  PariOUT *tmp = pariOut;
  outString *tmps = OutStr, newStr;

  if (typ(x) == t_STR) return pari_strdup(GSTR(x));
  pariOut = &pariOut2Str;
  newStr.len   = 0;
  newStr.size  = 0;
  newStr.string= NULL; OutStr = &newStr;
  do_out(x, T);
  OutStr->string[OutStr->len] = 0;

  pariOut = tmp; OutStr = tmps; return newStr.string;
}

char *
GENtostr(GEN x) { return GENtostr0(x, NULL, &gen_output); }

/* Returns gpmalloc()ed string */
char *
GENtoTeXstr(GEN x) {
  pariout_t T = DFLT_OUTPUT;

  T.prettyp = f_TEX;
  T.fieldw = 0;
  return GENtostr0(x, &T, &gen_output);
}

/* see print0(). Returns gpmalloc()ed string */
char *
pGENtostr(GEN g, long flag) {
  pariout_t T = DFLT_OUTPUT;
  pari_sp av = avma;
  char *t, *t2;
  long i, tlen = 0, l = lg(g);
  GEN Ls, Ll;

  T.prettyp = flag;
  /* frequent special case */
  if (l == 2) return GENtostr0((GEN)g[1], &T, &gen_output);

  Ls = cgetg(l, t_VEC);
  Ll = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++)
  {
    char *s = GENtostr0((GEN)g[i], &T, &gen_output);
    Ls[i] = (long)s;
    Ll[i] = strlen(s);
    tlen += Ll[i];
  }
  t2 = t = gpmalloc(tlen + 1);
  for (i = 1; i < l; i++)
  {
    strcpy(t2, (char*)Ls[i]);
    t2 += Ll[i];
    free((void*)Ls[i]);
  }
  avma = av; return t;
}
GEN Str0(GEN g, long flag) {
  char *t = pGENtostr(g, flag);
  GEN z = STRtoGENstr(t);
  free(t); return z;
}
GEN Str(GEN g)    { return Str0(g, f_RAW); }
GEN Strtex(GEN g) { return Str0(g, f_TEX); }
GEN
Strexpand(GEN g) {
  char *s = pGENtostr(g, f_RAW), *t = expand_tilde(s);
  GEN z = STRtoGENstr(t);
  free(t); free(s); return z;
}

/********************************************************************/
/**                                                                **/
/**                         WRITE AN INTEGER                       **/
/**                                                                **/
/********************************************************************/
#define putsigne_nosp(x) pariputc((x>0)? '+' : '-')
#define putsigne(x) pariputs((x>0)? " + " : " - ")
#define sp_sign_sp(T,x) ((T)->sp? putsigne(x): putsigne_nosp(x))
#define comma_sp(T)     ((T)->sp? pariputs(", "): pariputc(','))
#define sp(T) STMT_START { if ((T)->sp) pariputc(' '); } STMT_END

/* convert integer --> base 10^9 [not memory clean] */
static long *
convi(GEN x, long *l)
{
  pari_sp av, lim;
  long lz = 3 + (long)((lgefint(x)-2) * (BITS_IN_LONG / (9*L2SL10)));
  GEN z, zd;

  zd = z = new_chunk(lz);
  av = avma; lim = stack_lim(av,1);
  for(;;)
  {
    x = diviu_rem(x, 1000000000, (ulong*)zd); zd++;
    if (!signe(x)) { if (l) *l = zd - z; return zd; }
    if (low_stack(lim, stack_lim(av,1))) x = gerepileuptoint(av, x);
  }
}

/* # of decimal digits, assume l > 0 */
static long
numdig(long l)
{
  if (l < 100000)
  {
    if (l < 100)    return (l < 10)? 1: 2;
    if (l < 10000)  return (l < 1000)? 3: 4;
    return 5;
  }
  if (l < 10000000)   return (l < 1000000)? 6: 7;
  if (l < 1000000000) return (l < 100000000)? 8: 9;
  return 10;
}

static void
blancs(long nb) { while (nb-- > 0) pariputc(' '); }

static void
zeros(long nb)  { while (nb-- > 0) pariputc('0'); }

static void
copart(char *s, long x, long start)
{
  char *p = s + start;
  for ( ; p > s; x /= 10) *--p = x%10 + '0';
}
static void
comid(char *s, long x) { copart(s,x,9); }

/* convert abs(x) != 0 to str. Prepend '-' if (minus) */
static char *
itostr(GEN x, int minus)
{
  long l, d, *res = convi(x, &l);
  char *s = (char*)new_chunk(l + minus + 1), *t = s;

  if (minus) *t++ = '-';
  d = numdig(*--res);
  copart(t, *res, d); t += d;
  while (--l > 0) { comid(t, *--res); t += 9; }
  *t = 0; return s;
}

/* x != 0 integer, write abs(x). Prepend '-' if (minus) */
static void
wr_intsgn(GEN x, int minus)
{
  pari_sp av = avma;
  pariputs( itostr(x, minus) ); avma = av;
}

/* write int. T->fieldw: field width (pad with ' ') */
static void
wr_int(pariout_t *T, GEN x, int nosign)
{
  long sx = signe(x);
  pari_sp av = avma;
  char *s;

  if (!sx) { blancs(T->fieldw - 1); pariputc('0'); return; }
  s = itostr(x, sx < 0 && !nosign);
  blancs( T->fieldw - strlen(s) );
  pariputs(s); avma = av;
}

static void
wr_vecsmall(pariout_t *T, GEN g)
{
  long i,l;
  pariputs("Vecsmall(["); l = lg(g);
  for (i=1; i<l; i++)
  {
    pariputsf("%ld", g[i]);
    if (i<l-1) comma_sp(T);
  }
  pariputs("])");
}
/********************************************************************/
/**                                                                **/
/**                        WRITE A REAL NUMBER                     **/
/**                                                                **/
/********************************************************************/
extern long pow10(int n);
extern GEN rpowsi(ulong a, GEN n, long prec);

/* e binary exponent, return exponent in base ten */
static long
ex10(long e) { return (long) ((e >= 0)? e*L2SL10: -(-e*L2SL10)-1); }

/* sss.ttt, assume 'point' < strlen(s) */
static void
wr_dec(char *s, long point)
{
  char *t = s + point, save = *t;
  *t = 0;    pariputs(s); pariputc('.'); /* integer part */
  *t = save; pariputs(t);
}
/* a.bbb En*/
static void
wr_exp(pariout_t *T, char *s, long n)
{
  wr_dec(s, 1); sp(T); pariputsf("E%ld", n);
}

static void
round_up(long *resd, long n, long *res)
{
  *resd += n;
  while (*resd >= 1000000000 && resd < res) { *resd++ = 0; *resd += 1; }
}

/* assume x != 0 and print |x| in floating point format */
static void
wr_float(pariout_t *T, GEN x, int f_format)
{
  long beta, l, ldec, dec0, decdig, d, dif, lx = lg(x), dec = T->sigd;
  GEN z, res, resd;
  char *s, *t;
  
  dif =  bit_accuracy(lx) - expo(x);
  if (dif <= 0) f_format = 0; /* write in E format */
  if (dec > 0)
  { /* reduce precision if possible */
    l = 3 + (dec * pariK1);
    if (lx > l) { x = rtor(x, l); lx = l; }
  }
  
  beta = ex10(dif);
  if (beta)
  {
    z = rpowsi(10UL, stoi(labs(beta)), lx+1);
    z = (beta > 0)? mulrr(x, z): divrr(x, z);
    setsigne(z, 1);
  }
  else z = mpabs(x);

  /* x ~ z / 10^beta, z in N */
  z = grndtoi(z, &l); /* l is junk */
  res = convi(z, &ldec);
  resd = res - 1; /* leading word */
  dec0 = numdig(*resd);
  decdig = 9 * (ldec-1) + dec0; /* number of significant decimal digits in z */

  /* Round properly; leading word may overflow to 10^9 after rounding */
  if (dec < 0 || decdig < dec)
    dec = decdig;
  else if (dec < dec0) /* ==> 0 < dec < 9 */
  {
    long p10 = pow10(dec0 - dec);
    if (*resd % p10 > (p10>>1)) *resd += p10; /* round up */
  }
  else if (dec < decdig)
  {
    l = dec - dec0; /* skip leading word */
    d = l % 9;
    resd -= l / 9;
    if (d)
    { /* cut resd[-1] to first d digits when printing */
      long p10 = pow10(9 - d);
      if (*--resd % p10 > (p10>>1)) round_up(resd, p10, res);
    }
    else if ((ulong)resd[-1] > 500000000) round_up(resd, 1, res);
  }

  s = t = (char*)new_chunk(decdig + 1);
  l = ldec;
  d = numdig(*--res);
  copart(t, *res, d); t += d;
  while (--l > 0) { comid(t, *--res); t += 9; }
  s[dec] = 0;

  decdig = d + 9*(ldec-1); /* recompute: d may be 1 more */
  dif = decdig - beta; /* # of decimal digits in integer part */
  if (!f_format || dif > dec) wr_exp(T,s, dif-1);
  else if (dif > 0) wr_dec(s, dif);
  else { pariputs("0."); zeros(-dif); pariputs(s); }
}

/* Write real number x.
 * format: e (exponential), f (floating point), g (as f unless x too small)
 *   if format isn't correct (one of the above) act as e.
 * sigd: number of sigd to print (all if <0).
 */
static void
wr_real(pariout_t *T, GEN x, int nosign)
{
  pari_sp av;
  long sx = signe(x), ex = expo(x);

  if (!sx) /* real 0 */
  {
    if (T->format == 'f')
    {
      long dec = T->sigd;
      if (dec < 0)
      {
        long d = 1 + ((-ex)>>TWOPOTBITS_IN_LONG);
        dec = (d <= 0)? 0: (long)(pariK*d);
      }
      pariputs("0."); zeros(dec);
    }
    else
      pariputsf("0.E%ld", ex10(ex) + 1);
    return;
  }
  if (!nosign && sx < 0) pariputc('-'); /* print sign if needed */
  av = avma;
  wr_float(T,x, (T->format == 'g' && ex >= -32) || T->format == 'f');
  avma = av;
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

static char
vsigne(GEN x)
{
  long s = signe(x);
  if (!s) return '0';
  return (s > 0) ? '+' : '-';
}

static void
voir2(GEN x, long nb, long bl)
{
  long tx,i,j,e,dx,lx;

  if (!x) { pariputs("NULL\n"); return; }
  tx = typ(x);
  if (tx == t_INT && x == gzero) { pariputs("gzero\n"); return; }
  if (tx == t_SMALL) {
    pariputs("[SMALL ");
    sorstring(VOIR_STRING2,(long)x);
    pariputs("]\n"); return;
  }
  sorstring(VOIR_STRING1,(ulong)x);
  
  lx = lg(x);
  pariputsf("%s(lg=%ld%s):",type_name(tx)+2,lx,isclone(x)? ",CLONE" : "");
  sorstring(VOIR_STRING2,x[0]);
  if (! is_recursive_t(tx)) /* t_SMALL, t_INT, t_REAL, t_STR, t_VECSMALL */
  {
    if (tx == t_STR) 
      pariputs("chars:");
    else if (tx == t_INT)
      pariputsf("(%c,lgef=%ld):", vsigne(x), lgefint(x));
    else if (tx == t_REAL)
      pariputsf("(%c,expo=%ld):", vsigne(x), expo(x));
    if (nb<0) nb = (tx==t_INT)? lgefint(x): lx;
    if (tx == t_VECSMALL) nb = lx;
    for (i=1; i < nb; i++) sorstring(VOIR_STRING2,x[i]);
    pariputc('\n'); return;
  }

  if (tx == t_PADIC)
    pariputsf("(precp=%ld,valp=%ld):", precp(x), valp(x));
  else if (tx == t_POL)
    pariputsf("(%c,varn=%ld,lgef=%ld):", vsigne(x), varn(x), lgef(x));
  else if (tx == t_SER)
    pariputsf("(%c,varn=%ld,prec=%ld,valp=%ld):",
               vsigne(x), varn(x),lg(x)-2, valp(x));
  else if (tx == t_LIST)
    pariputsf("(lgef=%ld):", lgef(x));
  
  if (tx == t_POL || tx == t_LIST) lx = lgef(x);
  for (i=1; i<lx; i++) sorstring(VOIR_STRING2,x[i]);
  bl+=2; pariputc('\n');
  switch(tx)
  {
    case t_INTMOD: case t_POLMOD:
    {
      const char *s = (tx==t_INTMOD)? "int = ": "pol = ";
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
    default: err(talker,"unknown type %ld",t);
      s = NULL; /* not reached */
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

static void
do_append(char **sp, char c, char *last, int count)
{
  if (*sp + count > last)
    err(talker, "TeX variable name too long");
  while (count--)
    *(*sp)++ = c;
}

static char *
get_texvar(long v, char *buf, unsigned int len)
{
  entree *ep = varentries[v];
  char *s, *t = buf, *e = buf + len - 1;

  if (!ep) err(talker, "this object uses debugging variables");
  s = ep->name;
  if (strlen(s) >= len) err(talker, "TeX variable name too long");
  while(isalpha((int)*s)) *t++ = *s++;
  *t = 0;
  if (isdigit((int)*s) || *s == '_') {
    int seen1 = 0, seen = 0;

    /* Skip until the first non-underscore */
    while (*s == '_') s++, seen++;

    /* Special-case integers and empty subscript */
    if (*s == 0 || isdigit((unsigned char)*s))
      seen++;

    do_append(&t, '_', e, 1);
    do_append(&t, '{', e, 1);
    do_append(&t, '[', e, seen - 1);
    while (1) {
      if (*s == '_')
        seen1++, s++;
      else {
        if (seen1) {
          do_append(&t, ']', e, (seen >= seen1 ? seen1 : seen) - 1);
          do_append(&t, ',', e, 1);
          do_append(&t, '[', e, seen1 - 1);
          if (seen1 > seen)
            seen = seen1;
          seen1 = 0;
        }
        if (*s == 0)
          break;
        do_append(&t, *s++, e, 1);
      }
    }
    do_append(&t, ']', e, seen - 1);
    do_append(&t, '}', e, 1);
    *t = 0;
  }
  return buf;
}

static void
monome(const char *v, long deg)
{
  if (deg)
  {
    pariputs(v);
    if (deg!=1) pariputsf("^%ld",deg);
  }
  else pariputc('1');
}

static void
texnome(const char *v, long deg)
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
  long nu, i, l, m;
  pari_sp av=avma;
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

  pariputsf(" %ld variable names used out of %d\n\n",manage_var(manage_var_next,NULL),MAXVARN);
  if (!n) return;

  if (n > (ulong)nu) n = nu;
  adr = (GEN)avma; adr1 = adr+n;
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
wr_monome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);

  if (sig) { sp_sign_sp(T,sig); monome(v,d); }
  else
  {
    sig = isfactor(a);
    if (sig) { sp_sign_sp(T,sig); bruti(a,T,sig); }
    else
    {
      sp_sign_sp(T,1); pariputc('('); bruti(a,T,sig); pariputc(')');
    }
    if (d) { pariputc('*'); monome(v,d); }
  }
}

static void
wr_texnome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);

  if (sig) { putsigne(sig); texnome(v,d); }
  else
  {
    sig = isfactor(a);
    if (sig) { putsigne(sig); texi(a,T,sig); }
    else
    {
      pariputs(" + \\left("); texi(a,T,sig); pariputs("\\right) ");
    }
    if (d)
    {
      if (GP_DATA && (GP_DATA->flags & TEXMACS)) pariputs("\\*");
      texnome(v,d);
    }
  }
}

static void
wr_lead_monome(pariout_t *T, GEN a,const char *v, long d, int nosign)
{
  long sig = isone(a);
  if (sig)
  {
    if (!nosign && sig<0) pariputc('-');
    monome(v,d);
  }
  else
  {
    if (isfactor(a)) bruti(a,T,nosign);
    else
    {
      pariputc('('); bruti(a,T,0); pariputc(')');
    }
    if (d) { pariputc('*'); monome(v,d); }
  }
}

static void
wr_lead_texnome(pariout_t *T, GEN a,const char *v, long d, int nosign)
{
  long sig = isone(a);
  if (sig)
  {
    if (!nosign && sig<0) pariputc('-');
    texnome(v,d);
  }
  else
  {
    if (isfactor(a)) texi(a,T,nosign);
    else
    {
      pariputs(" \\left("); texi(a,T,0); pariputs("\\right) ");
    }
    if (d)
    {
      if (GP_DATA && (GP_DATA->flags & TEXMACS)) pariputs("\\*");
      texnome(v,d);
    }
  }
}

void
bruti(GEN g, pariout_t *T, int nosign)
{
  long tg,l,i,j,r;
  GEN a,b;
  const char *v;
  char buf[32];

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
    case t_INT: wr_intsgn(g, !nosign && signe(g) < 0); break;
    case t_REAL: wr_real(T,g,nosign); break;

    case t_INTMOD: case t_POLMOD:
      pariputs(new_fun_set? "Mod(": "mod(");
      bruti((GEN)g[2],T,0); comma_sp(T);
      bruti((GEN)g[1],T,0); pariputc(')'); break;

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      r = isfactor((GEN)g[1]); if (!r) pariputc('(');
      bruti((GEN)g[1],T,nosign);
      if (!r) pariputc(')');
      pariputc('/');
      r = isdenom((GEN)g[2]); if (!r) pariputc('(');
      bruti((GEN)g[2],T,0);
      if (!r) pariputc(')');
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = (GEN)g[r+1]; b = (GEN)g[r+2]; v = r? "w": "I";
      if (isnull(a))
      {
        wr_lead_monome(T,b,v,1,nosign);
        return;
      }
      bruti(a,T,nosign);
      if (!isnull(b)) wr_monome(T,b,v,1);
      break;

    case t_POL: v = get_var(ordvar[varn(g)], buf);
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull((GEN)g[i])) i--;
      wr_lead_monome(T,(GEN)g[i],v,i,nosign);
      while (i--)
      {
        a = (GEN)g[i];
        if (!isnull_for_pol(a)) wr_monome(T,a,v,i);
      }
      break;

    case t_SER: v = get_var(ordvar[varn(g)], buf);
      i = valp(g);
      if (signe(g))
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g += (2-i);
        wr_lead_monome(T,(GEN)g[i],v,i,nosign);
        while (++i < l)
        {
          a = (GEN)g[i];
          if (!isnull_for_pol(a)) wr_monome(T,a,v,i);
        }
        sp_sign_sp(T,1);
      }
      pariputs("O("); monome(v,i); pariputc(')'); break;

    case t_PADIC:
    {
      GEN p = (GEN)g[2];
      pari_sp av = avma;
      char *ev;
      i = valp(g); l = precp(g)+i;
      g = (GEN)g[4]; ev = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_intsgn(a, 0); if (i) pariputc('*');
	  }
	  if (i) padic_nome(ev,i);
          sp_sign_sp(T,1);
	}
        if ((i & 0xff) == 0) g = gerepileuptoint(av,g);
      }
      pariputs("O("); padic_nome(ev,i); pariputc(')');
      free(ev); break;
    }

    case t_QFR: case t_QFI: r = (tg == t_QFR);
      if (new_fun_set) pariputs("Qfb("); else pariputs(r? "qfr(": "qfi(");
      bruti((GEN)g[1],T,0); comma_sp(T);
      bruti((GEN)g[2],T,0); comma_sp(T);
      bruti((GEN)g[3],T,0);
      if (r) { comma_sp(T); bruti((GEN)g[4],T,0); }
      pariputc(')'); break;

    case t_VEC: case t_COL:
      pariputc('['); l = lg(g);
      for (i=1; i<l; i++)
      {
        bruti((GEN)g[i],T,0);
        if (i<l-1) comma_sp(T);
      }
      pariputc(']'); if (tg==t_COL) pariputc('~');
      break;
    case t_VECSMALL: wr_vecsmall(T,g); break;

    case t_LIST:
      pariputs("List(["); l = lgef(g);
      for (i=2; i<l; i++)
      {
        bruti((GEN)g[i],T,0);
        if (i<l-1) comma_sp(T);
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
        if (r == 2) { bruti(gcoeff(g,1,1),T,0); pariputc(')'); return; }
      }
      pariputc('[');
      for (i=1; i<l; i++)
      {
	for (j=1; j<r; j++)
	{
	  bruti(gcoeff(g,i,j),T,0);
          if (j<r-1) comma_sp(T);
	}
	if (i<l-1) { pariputc(';'); sp(T); }
      }
      pariputc(']'); if (l==2) pariputc(')');
      break;

    default: sorstring(VOIR_STRING2,*g);
  }
}

void
matbruti(GEN g, pariout_t *T)
{
  long i,j,r,l;

  if (typ(g) != t_MAT) { bruti(g,T,0); return; }

  r=lg(g); if (r==1 || lg(g[1])==1) { pariputs("[;]\n"); return; }
  pariputc('\n'); l = lg(g[1]);
  for (i=1; i<l; i++)
  {
    pariputc('[');
    for (j=1; j<r; j++)
    {
      bruti(gcoeff(g,i,j),T,0); if (j<r-1) pariputc(' ');
    }
    if (i<l-1) pariputs("]\n\n"); else pariputs("]\n");
  }
}

static void
sor_monome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);
  if (sig) { putsigne(sig); monome(v,d); }
  else
  {
    sig = isfactor(a);
    if (sig) { putsigne(sig); if (sig < 0) a = gneg(a); }
    else pariputs(" + ");
    sori(a,T); if (d) { pariputc(' '); monome(v,d);}
  }
}

static void
sor_lead_monome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);
  if (sig)
  {
    if (sig < 0) pariputc('-');
    monome(v,d);
  }
  else
  {
    sori(a,T);
    if (d) { pariputc(' '); monome(v,d); }
  }
}

void
sori(GEN g, pariout_t *T)
{
  long tg=typ(g), i,j,r,l,close_paren;
  GEN a,b;
  const char *v;
  char buf[32];

  if (tg == t_INT) { wr_int(T,g,0); return; }
  if (tg != t_MAT && tg != t_COL) T->fieldw = 0;
  switch (tg)
  {
    case t_SMALL: pariputsf("%ld",smalltos(g)); return;
    case t_REAL: wr_real(T,g,0); return;
    case t_STR:
      pariputc('"'); pariputs(GSTR(g)); pariputc('"'); return;
    case t_LIST:
      pariputs("List(");
      for (i=2; i<lgef(g); i++)
      {
	sori((GEN)g[i], T); if (i<lgef(g)-1) pariputs(", ");
      }
      pariputs(")\n"); return;
  }
  close_paren=0;
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
      sori(a,T); pariputs(" mod "); sori(b,T); break;
	
    case t_FRAC: case t_FRACN:
      a=(GEN)g[1]; wr_int(T,a,1); pariputs(" /");
      b=(GEN)g[2]; wr_int(T,b,1); break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = (GEN)g[r+1]; b = (GEN)g[r+2]; v = r? "w": "I";
      if (isnull(a)) { sor_lead_monome(T,b,v,1); break; }
      sori(a,T); if (!isnull(b)) sor_monome(T,b,v,1);
      break;

    case t_PADIC:
    {
      GEN p = (GEN)g[2];
      char *ev;
      i = valp(g); l = precp(g)+i;
      g = (GEN)g[4]; ev = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int(T,a,1); pariputc(i? '*': ' ');
	  }
	  if (i) { padic_nome(ev,i); pariputc(' '); }
          pariputs("+ ");
	}
      }
      pariputs("O(");
      if (!i) pariputs(" 1)"); else padic_nome(ev,i);
      pariputc(')'); free(ev); break;
    }

    case t_POL:
      if (!signe(g)) { pariputc('0'); break; }
      v = get_var(ordvar[varn(g)],buf);
      i = degpol(g); g += 2; while (isnull((GEN)g[i])) i--;
      sor_lead_monome(T,(GEN)g[i],v,i);
      while (i--)
      {
        a = (GEN)g[i]; if (!isnull_for_pol(a)) sor_monome(T,a,v,i);
      }
      break;
	
    case t_SER: v = get_var(ordvar[varn(g)],buf);
      i = valp(g);
      if (signe(g))
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g += (2-i);
        sor_lead_monome(T,(GEN)g[i],v,i);
        while (++i < l)
        {
          a = (GEN)g[i]; if (!isnull_for_pol(a)) sor_monome(T,a,v,i);
        }
        pariputs(" + ");
      }
      pariputs("O(");
      if (!i) pariputs(" 1)"); else monome(v,i);
      pariputc(')'); break;

    case t_RFRAC: case t_RFRACN:
    if (T->initial)
    {
      char *v1, *v2;
      long sd = 0, sn = 0, d,n;
      long wd = term_width();

      T->initial = 0;
      v1 = GENtostr0((GEN)g[1], T, &sori); n = strlen(v1);
      v2 = GENtostr0((GEN)g[2], T, &sori); d = strlen(v2);

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
    pariputc('('); sori((GEN)g[1],T); pariputs(" / "); sori((GEN)g[2],T);
    pariputc(')'); return;
	
    case t_QFR: case t_QFI: pariputc('{');
      sori((GEN)g[1],T); pariputs(", ");
      sori((GEN)g[2],T); pariputs(", ");
      sori((GEN)g[3],T);
      if (tg == t_QFR) { pariputs(", "); sori((GEN)g[4],T); }
      pariputs("}\n"); break;
	
    case t_VEC: pariputc('[');
      for (i=1; i<lg(g); i++)
      {
	sori((GEN)g[i],T); if (i<lg(g)-1) pariputs(", ");
      }
      pariputc(']'); break;
    case t_VECSMALL: wr_vecsmall(T,g); break;

    case t_COL:
      if (lg(g)==1) { pariputs("[]\n"); return; }
      pariputc('\n');
      for (i=1; i<lg(g); i++)
      {
        pariputc('['); sori((GEN)g[i],T); pariputs("]\n");
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
	  sori(gcoeff(g,i,j),T); if (j<lx-1) pariputc(' ');
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
void
texi(GEN g, pariout_t *T, int nosign)
{
  long tg,i,j,l,r;
  GEN a,b;
  const char *v;
  char buf[67];

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
    case t_SMALL: pariputsf("%ld",smalltos(g)); break;
    case t_INT: wr_intsgn(g, !nosign && signe(g) < 0); break;
    case t_REAL: wr_real(T,g,nosign); break;

    case t_INTMOD: case t_POLMOD:
      texi((GEN)g[2],T,0); pariputs(" mod ");
      texi((GEN)g[1],T,0); break;

    case t_FRAC: case t_FRACN: case t_RFRAC: case t_RFRACN:
      texi((GEN)g[1],T,nosign); pariputs("\\over");
      texi((GEN)g[2],T,0); break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = (GEN)g[r+1]; b = (GEN)g[r+2]; v = r? "w": "I";
      if (isnull(a))
      {
        wr_lead_texnome(T,b,v,1,nosign);
        break;
      }
      texi(a,T,nosign);
      if (!isnull(b)) wr_texnome(T,b,v,1);
      break;

    case t_POL: v = get_texvar(ordvar[varn(g)], buf, sizeof(buf));
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull((GEN)g[i])) i--;
      wr_lead_texnome(T,(GEN)g[i],v,i,nosign);
      while (i--)
      {
        a = (GEN)g[i];
        if (!isnull_for_pol(a)) wr_texnome(T,a,v,i);
      }
      break;

    case t_SER: v = get_texvar(ordvar[varn(g)], buf, sizeof(buf));
      i = valp(g);
      if (signe(g))
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g += (2-i);
        wr_lead_texnome(T,(GEN)g[i],v,i,nosign);
        while (++i < l)
        {
          a = (GEN)g[i];
          if (!isnull_for_pol(a)) wr_texnome(T,a,v,i);
        }
        pariputs("+ ");
      }
      pariputs("O("); texnome(v,i); pariputc(')'); break;

    case t_PADIC:
    {
      GEN p = (GEN)g[2];
      char *ev;
      i = valp(g); l = precp(g)+i;
      g = (GEN)g[4]; ev = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_intsgn(a, 0); if (i) pariputs("\\cdot");
	  }
	  if (i) padic_texnome(ev,i);
	  pariputc('+');
	}
      }
      pariputs("O("); padic_texnome(ev,i); pariputc(')');
      free(ev); break;
    }
    case t_QFR: case t_QFI: r = (tg == t_QFR);
      if (new_fun_set) pariputs("Qfb("); else pariputs(r? "qfr(": "qfi(");
      texi((GEN)g[1],T,0); pariputs(", ");
      texi((GEN)g[2],T,0); pariputs(", ");
      texi((GEN)g[3],T,0);
      if (r) { pariputs(", "); texi((GEN)g[4],T,0); }
      pariputc(')'); break;

    case t_VEC:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi((GEN)g[i],T,0); if (i<lg(g)-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_LIST:
      pariputs("\\pmatrix{ "); l = lgef(g);
      for (i=2; i<l; i++)
      {
	texi((GEN)g[i],T,0); if (i<lgef(g)-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_COL:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi((GEN)g[i],T,0); pariputs("\\cr\n");
      }
      pariputc('}'); break;

    case t_STR:
    {
      char *s;
  
      pariputs("\\mbox{");
      s = GSTR(g);
      while (*s) {
	if (strchr("\\{}$_^%#&~", *s))
	  pariputc('\\');		/* What to do with \\ ? */
	pariputc(*s);
	if (strchr("^~", *s++))
	  pariputs("{}");
      }
      pariputc('}'); break;
    }
    case t_MAT:
      pariputs("\\pmatrix{\n "); r = lg(g);
      if (r>1)
      {
        l = lg(g[1]);
        for (i=1; i<l; i++)
        {
          for (j=1; j<r; j++)
          {
            texi(gcoeff(g,i,j),T,0); if (j<r-1) pariputc('&');
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
/**                          GP OUTPUT                            **/
/**                                                               **/
/*******************************************************************/

/* EXTERNAL PRETTYPRINTER */

/* Wait for prettinprinter to finish, to prevent new prompt from overwriting
 * the output.  Fill the output buffer, wait until it is read.
 * Better than sleep(2): give possibility to print */
static void
prettyp_wait(void)
{
  char *s = "                                                     \n";
  int i = 400;

  pariputs("\n\n"); pariflush(); /* start translation */
  while (--i) pariputs(s);
  pariputs("\n"); pariflush();
}

/* initialise external prettyprinter (tex2mail) */
static int
prettyp_init(void)
{
  gp_pp *pp = GP_DATA->pp;
  if (!pp->cmd) return 0;
  if (!pp->file)
    pp->file = try_pipe(pp->cmd, mf_OUT | mf_TEST);
  if (pp->file) return 1;

  err(warner,"broken prettyprinter: '%s'",pp->cmd);
  free(pp->cmd); pp->cmd = NULL; return 0;
}

/* n = history number. if n = 0 no history */
static int
tex2mail_output(GEN z, long n)
{
  pariout_t T = *(GP_DATA->fmt); /* copy */
  FILE *o_out;
  FILE *o_logfile = logfile;
  
  if (!prettyp_init()) return 0;
  o_out = pari_outfile; /* save state */

  /* Emit first: there may be lines before the prompt */
  if (n) term_color(c_OUTPUT);
  pariflush();
  pari_outfile = GP_DATA->pp->file->file;
  T.prettyp = f_TEX;
  logfile = NULL;

  /* history number */
  if (n)
  {
    char s[128];

    if (*term_get_color(c_HIST) || *term_get_color(c_OUTPUT))
    {
      char col1[80];
      strcpy(col1, term_get_color(c_HIST));
      sprintf(s, "\\LITERALnoLENGTH{%s}\\%%%ld =\\LITERALnoLENGTH{%s} ",
              col1, n, term_get_color(c_OUTPUT));
    }
    else
      sprintf(s, "\\%%%ld = ", n);
    pariputs_opt(s);
    if (o_logfile)
	fprintf(o_logfile, "%%%ld = ", n);
  }
  /* output */
  gen_output(z, &T);
  

  /* flush and restore */
  prettyp_wait();
  if (o_logfile) {
    pari_outfile = o_logfile;
    /* XXXX Maybe it is better to output in another format? */
    outbrute(z); pariputc('\n'); pariflush();
  }
  logfile = o_logfile;
  pari_outfile = o_out;
  if (n) term_color(c_NONE);
  return 1;
}

/* TEXMACS */

static void
texmacs_output(GEN z, long n)
{
  pariout_t T = *(GP_DATA->fmt); /* copy */
  char *sz;

  T.prettyp = f_TEX;
  T.fieldw = 0;
  sz = GENtostr0(z, &T, &gen_output);
  printf("%clatex:", DATA_BEGIN);
  if (n)
    printf("\\magenta\\%%%ld = $\\blue ", n);
  else
    printf("$\\blue ");
  printf("%s$%c", sz,DATA_END); free(sz);
  fflush(stdout);
}

/* REGULAR */

static void
normal_output(GEN z, long n)
{
  long l = 0;
  /* history number */
  if (n)
  {
    char s[64];
    term_color(c_HIST);
    sprintf(s, "%%%ld = ", n);
    pariputs_opt(s);
    l = strlen(s);
  }
  /* output */
  term_color(c_OUTPUT);
  if (GP_DATA->lim_lines)
    lim_lines_output(z, GP_DATA->fmt, l, GP_DATA->lim_lines);
  else
    gen_output(z, GP_DATA->fmt);
  term_color(c_NONE); pariputc('\n');
}

void
gp_output(GEN z, gp_data *G)
{
  if (G->flags & TEST) {
    init80(0);
    gen_output(z, G->fmt); pariputc('\n');
  }
  else if (G->flags & TEXMACS)
    texmacs_output(z, G->hist->total);
  else if (G->fmt->prettyp != f_PRETTY || !tex2mail_output(z, G->hist->total))
    normal_output(z, G->hist->total);
  pariflush();
}

/*******************************************************************/
/**                                                               **/
/**                        USER OUTPUT FUNCTIONS                  **/
/**                                                               **/
/*******************************************************************/

void
gen_output(GEN x, pariout_t *T)
{
  pari_sp av = avma;
  GEN y = changevar(x, polvar);
  if (!T) T = &DFLT_OUTPUT;
  T->initial = 1;
  switch(T->prettyp)
  {
    case f_PRETTYMAT: matbruti(y, T); break;
    case f_PRETTY:
    case f_PRETTYOLD: sori (y, T); break;
    case f_RAW      : bruti(y, T, 0); break;
    case f_TEX      : texi (y, T, 0); break;
  }
  avma = av;
}

static void
_initout(pariout_t *T, char f, long sigd, long sp, long fieldw, int prettyp)
{
  T->format = f;
  T->sigd = sigd;
  T->sp = sp;
  T->fieldw = fieldw;
  T->initial = 1;
  T->prettyp = prettyp;
}

void
bruteall(GEN g, char f, long d, long sp)
{
  pariout_t T; _initout(&T,f,d,sp,0, f_RAW);
  gen_output(g, &T);
}

void
matbrute(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,1,0, f_PRETTYMAT);
  gen_output(g, &T);
}

void
sor(GEN g, char f, long d, long c)
{
  pariout_t T; _initout(&T,f,d,1,c, f_PRETTYOLD);
  gen_output(g, &T);
}

void
texe(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,0,0, f_TEX);
  gen_output(g, &T);
}

void
brute(GEN g, char f, long d) { bruteall(g,f,d,1); }

void
outbrute(GEN g) { bruteall(g,'g',-1,1); }

void
outsor(GEN g) { sor(g,'g',-1,1); }

void
outtex(GEN g) { texe(g,'g',-1); }

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
bruterr(GEN x,char format,long sigd)
{
  PariOUT *out = pariOut; pariOut = pariErr;
  bruteall(x,format,sigd,1); pariOut = out;
}

void
fprintferr(const char* format, ...)
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
#  include <fcntl.h>
#  include <sys/stat.h>
#  include <pwd.h>
#  ifdef __EMX__
#    include <process.h>
#  endif
#  define HAVE_PIPES
#endif
#ifndef O_RDONLY
#  define O_RDONLY 0
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
  if (f->next) (f->next)->prev = f->prev;
  else if (f == last_tmp_file) last_tmp_file = f->prev;
  else if (f == last_file) last_file = f->prev;
  if (f->prev) (f->prev)->next = f->next;
  pari_kill_file(f);
}

static pariFILE *
pari_open_file(FILE *f, char *s, char *mode)
{
  if (!f) err(talker, "could not open requested file %s", s);
  if (DEBUGFILES)
    fprintferr("I/O: opening file %s (mode %s)\n", s, mode);
  return newfile(f,s,0);
}

pariFILE *
pari_fopen(char *s, char *mode)
{
  return pari_open_file(fopen(s, mode), s, mode);
}

#ifdef UNIX
/* open tmpfile s (a priori for writing) avoiding symlink attacks */
pariFILE *
pari_safefopen(char *s, char *mode)
{
  long fd = open(s, O_CREAT|O_EXCL|O_RDWR, S_IRUSR|S_IWUSR);

  if (fd == -1) err(talker,"tempfile %s already exists",s);
  return pari_open_file(fdopen(fd, mode), s, mode);
}
#else
pariFILE *
pari_safefopen(char *s, char *mode)
{
  return pari_fopen(s, mode);
}
#endif

void
pari_unlink(char *s)
{
  if (unlink(s)) err(warner, "I/O: can\'t remove file %s", s);
  else if (DEBUGFILES)
    fprintferr("I/O: removed file %s\n", s);
}

void
check_filtre(filtre_t *T)
{
  if (T && T->in_string)
  {
    err(warner,"run-away string. Closing it");
    T->in_string = 0;
  }
  if (T && T->in_comment)
  {
    err(warner,"run-away comment. Closing it");
    T->in_comment = 0;
  }
}

/* Remove one INFILE from the stack. Reset infile (to the most recent infile)
 * Return -1, if we're trying to pop out stdin itself; 0 otherwise
 * Check for leaked file handlers (temporary files)
 */
int
popinfile()
{
  pariFILE *f;
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

static int
ok_pipe(FILE *f)
{
  if (DEBUGFILES) fprintferr("I/O: checking output pipe...\n");
  CATCH(CATCH_ALL) {
    CATCH_RELEASE(); return 0;
  }
  TRY {
    int i;
    fprintf(f,"\n\n"); fflush(f);
    for (i=1; i<1000; i++) fprintf(f,"                  \n");
    fprintf(f,"\n"); fflush(f);
  } ENDCATCH;
  return 1;
}

pariFILE *
try_pipe(char *cmd, int fl)
{
#ifndef HAVE_PIPES
  err(archer); return NULL;
#else
  FILE *file;
  char *f;
  int flag = fl;

#  ifdef __EMX__
  if (_osmode == DOS_MODE) /* no pipes under DOS */
  {
    char *s;
    if (flag & mf_OUT) err(archer);
    f = pari_unique_filename("pipe");
    s = gpmalloc(strlen(cmd)+strlen(f)+4);
    sprintf(s,"%s > %s",cmd,f);
    file = system(s)? NULL: (FILE *) fopen(f,"r");
    flag |= mf_FALSE; free(s);
  }
  else
#  endif
  {
    file = (FILE *) popen(cmd, (flag & mf_OUT)? "w": "r");
    if (flag & mf_OUT) flag |= mf_PERM;
    if ((flag & (mf_TEST | mf_OUT)) && !ok_pipe(file)) return NULL;
    f = cmd;
  }
  if (!file) err(talker,"[pipe:] '%s' failed",cmd);
  return newfile(file, f, mf_PIPE|flag);
#endif
}

void
os_close(long fd)
{
#ifdef WINCE
  CloseHandle((HANDLE)fd);
#else
  close(fd);
#endif
}

void
(*os_signal(int sig, void (*f)(int)))(int)
{
#ifdef WINCE
  return SIG_IGN;
#else
  return signal(sig,f);
#endif
}

void
os_read(long fd, char ch[], long s)
{
#ifdef WINCE
  DWORD chRead;
  ReadFile((HANDLE)fd, ch, s, &chRead, NULL);
#else
  (void)read(fd,ch,s);
#endif
}

long
os_open(char *s, int mode)
{
  long fd;
#ifdef WINCE
  HANDLE h;
  short ws[256];
  if (mode != O_RDONLY) err(impl,"generic open for Windows");
  MultiByteToWideChar(CP_ACP, 0, s, strlen(s)+1, ws, 256);
  h = CreateFile(ws,GENERIC_READ,FILE_SHARE_READ,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);
  fd = (h == INVALID_HANDLE_VALUE)? (long)-1: (long)h;
#else
  fd = open(s,mode);
#endif
  return fd;
}

char *
os_getenv(char *s)
{
#if defined(WINCE) || defined(macintosh)
  return NULL;
#else
  return getenv(s);
#endif
}

/*******************************************************************/
/**                                                               **/
/**                   GP STANDARD INPUT AND OUTPUT                **/
/**                                                               **/
/*******************************************************************/
static char *last_filename = NULL;

#ifdef HAS_OPENDIR
#  include <dirent.h>
#endif
/* slow, but more portable than stat + S_I[FS]DIR */
int
pari_is_dir(char *name)
{
#ifdef HAS_OPENDIR
  DIR *d = opendir(name);
  if (d) { (void)closedir(d); return 1; }
#endif
  return 0;
}

/* expand tildes in filenames, return a malloc'ed buffer */
static char *
_expand_tilde(const char *s)
{
#if !defined(UNIX) && !defined(__EMX__)
  return pari_strdup(s);
#else
  struct passwd *p;
  const char *u;
  char *ret;
  int len;

  if (*s != '~') return pari_strdup(s);
  s++; u = s; /* skip ~ */
  if (!*s || *s == '/')
  {
    p = getpwuid(geteuid());
    if (!p) 
    { /* host badly configured, don't kill session on startup
       * (when expanding path) */
      err(warner,"can't expand ~");
      return pari_strdup(s);
    }
  }
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
  ret = gpmalloc(strlen(p->pw_dir) + strlen(u) + 1);
  sprintf(ret,"%s%s",p->pw_dir,u); return ret;
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
      xlen <<= 1;
      x = (char **)gprealloc((void*)x, xlen * sizeof(char*));
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
expand_tilde(const char *s)
{
  return _expand_env(_expand_tilde(s));
}

void
delete_dirs(gp_path *p)
{
  char **v = p->dirs, **dirs;
  if (v)
  {
    p->dirs = NULL; /* in case of error */
    for (dirs = v; *dirs; dirs++) free(*dirs);
    free(v);
  }
}

#if defined __EMX__ || defined _WIN32
#  define PATH_SEPARATOR ';'
#else
#  define PATH_SEPARATOR ':'
#endif

void
gp_expand_path(gp_path *p)
{
  char **dirs, *s, *v = p->PATH;
  int i, n = 0;

  delete_dirs(p);
  v = pari_strdup(v);
  for (s=v; *s; s++)
    if (*s == PATH_SEPARATOR) { *s = 0; n++; }
  dirs = (char**) gpmalloc((n + 2)*sizeof(char *));

  for (s=v, i=0; i<=n; i++)
  {
    char *end = s + strlen(s), *f = end;
    while (f > s && *--f == '/') *f = 0;
    dirs[i] = expand_tilde(s);
    s = end + 1; /* next path component */
  }
  free((void*)v);
  dirs[i] = NULL; p->dirs = dirs;
}

/* name is a malloc'ed (existing) filename. Accept it as new infile
 * (unzip if needed). */
static FILE *
accept_file(char *name, FILE *file)
{
  if (pari_is_dir(name))
  {
    err(warner,"skipping directory %s",name);
    return NULL;
  }
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
  if (file) file = accept_file(name,file);
  if (!file)
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
switchin(const char *name0)
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
  s=name; while (*s && *s != '/' && *s != '\\') s++;
  if (*s) { if (try_name(name)) return; }
  else if (GP_DATA)
  {
    char **tmp = GP_DATA->path->dirs;
    for ( ; *tmp; tmp++)
    { /* make room for '/' and '\0', try_name frees it */
      s = gpmalloc(2 + strlen(*tmp) + strlen(name));
      sprintf(s,"%s/%s",*tmp,name);
      if (try_name(s)) return;
    }
  }
  err(openfiler,"input",name0);
}

static int is_magic_ok(FILE *f);

void
switchout(char *name)
{
  if (name)
  {
    FILE *f = fopen(name, "r");
    if (f)
    {
      if (is_magic_ok(f))
        err(talker,"%s is a GP binary file. Please use writebin", name);
      fclose(f);
    }
    f = fopen(name, "a");
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
/**                    I/O IN BINARY FORM                         **/
/**                                                               **/
/*******************************************************************/
#define _fwrite(a,b,c,d) \
  if (fwrite((a),(b),(c),(d)) < (c)) err(talker,"write failed")
#define _fread(a,b,c,d) \
  if (fread((a),(b),(c),(d)) < (c)) err(talker,"read failed")
#define _lfread(a,b,c) _fread((a),sizeof(long),(b),(c))
#define _cfread(a,b,c) _fread((a),sizeof(char),(b),(c))
#define _lfwrite(a,b,c) _fwrite((a),sizeof(long),(b),(c))
#define _cfwrite(a,b,c) _fwrite((a),sizeof(char),(b),(c))

#define BIN_GEN 0
#define NAM_GEN 1

static long
rd_long(FILE *f)
{
  long L;
  _lfread(&L, 1UL, f); return L;
}
static void
wr_long(long L, FILE *f)
{
  _lfwrite(&L, 1UL, f);
}

/* append x to file f */
static void
wrGEN(GEN x, FILE *f)
{
  GENbin *p = copy_bin(x);
  size_t L = p->len;

  wr_long(L,f);
  wr_long((long)p->x,f);
  wr_long((long)p->base,f);
  _lfwrite(GENbase(p), L,f);
  free((void*)p);
}

static void
wrstr(char *s, FILE *f)
{
  size_t L = strlen(s)+1;
  wr_long(L,f);
  _cfwrite(s, L, f);
}

static char *
rdstr(FILE *f)
{
  size_t L = (size_t)rd_long(f);
  char *s;
  if (!L) return NULL;
  s = gpmalloc(L);
  _cfread(s, L, f); return s;
}

void
writeGEN(GEN x, FILE *f)
{
  fputc(BIN_GEN,f);
  wrGEN(x, f);
}

void
writenamedGEN(GEN x, char *s, FILE *f)
{
  fputc(NAM_GEN,f);
  wrstr(s, f);
  wrGEN(x, f);
}

/* read a GEN from file f */
static GEN
rdGEN(FILE *f)
{
  size_t L = (size_t)rd_long(f);
  GENbin *p;

  if (!L) return NULL;
  p = (GENbin*)gpmalloc(sizeof(GENbin) + L*sizeof(long));
  p->len  = L;
  p->x    = (GEN)rd_long(f);
  p->base = (GEN)rd_long(f);
  _lfread(GENbase(p), L,f);
  return bin_copy(p);
}

GEN
readobj(FILE *f, int *ptc)
{
  int c = fgetc(f);
  GEN x = NULL;
  switch(c)
  {
    case BIN_GEN:
      x = rdGEN(f);
      if (!x) err(talker,"malformed binary file (no GEN)");
      break;
    case NAM_GEN:
    {
      char *s = rdstr(f);
      if (!s) err(talker,"malformed binary file (no name)");
      x = rdGEN(f);
      if (!x) err(talker,"malformed binary file (no GEN)");
      fprintferr("setting %s\n",s);
      changevalue(fetch_named_var(s,0), x);
      break;
    }
    case EOF: break;
    default: err(talker,"unknown code in readobj");
  }
  *ptc = c; return x;
}

#define MAGIC "\020\001\022\011-\007\020" /* ^P^A^R^I-^G^P */
#ifdef LONG_IS_64BIT
#  define ENDIAN_CHECK 0x0102030405060708L
#else
#  define ENDIAN_CHECK 0x01020304L
#endif
const long BINARY_VERSION = 0;

static int
is_magic_ok(FILE *f)
{
  size_t L = strlen(MAGIC);
  char *s = gpmalloc(L);
  int r = (fread(s,1,L, f) == L && strncmp(s,MAGIC,L) == 0);
  free(s); return r;
}

static int
is_sizeoflong_ok(FILE *f)
{
  char c;
  return (fread(&c,1,1, f) == 1 && c == (char)sizeof(long));
}

static int
is_long_ok(FILE *f, long L)
{
  long c;
  return (fread(&c,sizeof(long),1, f) == 1 && c == L);
}

static void
check_magic(const char *name, FILE *f)
{
  if (!is_magic_ok(f))
    err(talker, "%s is not a GP binary file",name);
  if (!is_sizeoflong_ok(f))
    err(talker, "%s not written for a %ld bit architecture",
               name, sizeof(long)*8);
  if (!is_long_ok(f, ENDIAN_CHECK))
    err(talker, "unexpected endianness in %s",name);
  if (!is_long_ok(f, BINARY_VERSION))
    err(talker, "%s written by an incompatible version of GP",name);
}

static void
write_magic(FILE *f)
{
  fprintf(f, MAGIC);
  fprintf(f, "%c", (char)sizeof(long));
  wr_long(ENDIAN_CHECK, f);
  wr_long(BINARY_VERSION, f);
}

int
file_is_binary(FILE *f)
{
  int c = fgetc(f); ungetc(c,f);
  return (c != EOF && isprint(c) == 0 && isspace(c) == 0);
}

void
writebin(char *name, GEN x)
{
  FILE *f = fopen(name,"r");
  int already = f? 1: 0;
  
  if (f) { check_magic(name,f); fclose(f); }
  f = fopen(name,"a");
  if (!f) err(openfiler,"binary output",name);
  if (!already) write_magic(f);

  if (x) writeGEN(x,f);
  else
  {
    long v, maxv = manage_var(manage_var_next,NULL);
    for (v=0; v<maxv; v++)
    {
      entree *ep = varentries[v];
      if (!ep) continue;
      writenamedGEN((GEN)ep->value,ep->name,f);
    }
  }
  fclose(f);
}

/* read all objects in f. If f contains BIN_GEN that would be silently ignored
 * [i.e f contains more than one objet, not all of them 'named GENs'], return
 * them all in a vector with clone bit set (special marker). */
GEN
readbin(const char *name, FILE *f)
{
  pari_sp av = avma;
  GEN x,y,z;
  int cx,cy;
  check_magic(name,f); x = y = z = NULL;
  cx = 0; /* gcc -Wall */
  while ((y = readobj(f, &cy)))
  {
    if (x && cx == BIN_GEN) z = z? concatsp(z, _vec(x)): _vec(x);
    x = y; cx = cy;
  }
  if (z)
  {
    if (x && cx == BIN_GEN) z = z? concatsp(z, _vec(x)): _vec(x);
    if (DEBUGLEVEL)
      err(warner,"%ld unnamed objects read. Returning then in a vector",
          lg(z)-1);
    x = gerepilecopy(av, z);
    setisclone(x); /* HACK */
  }
  return x;
}

/*******************************************************************/
/**                                                               **/
/**                             GP I/O                            **/
/**                                                               **/
/*******************************************************************/
/* print a vector of GENs */
void
print0(GEN g, long flag)
{
  pariout_t T = GP_DATA? *(GP_DATA->fmt): DFLT_OUTPUT; /* copy */
  long i, l = lg(g);
  T.prettyp = flag;
  for (i = 1; i < l; i++)
    if (flag != f_TEX && typ(g[i])==t_STR)
      pariputs(GSTR(g[i])); /* text surrounded by "" otherwise */
    else
      gen_output((GEN)g[i], &T);
}

#define PR_NL() {added_newline = 1; pariputc('\n'); pariflush(); }
#define PR_NO() {added_newline = 0; pariflush(); }
void print   (GEN g) { print0(g, f_RAW);       PR_NL(); }
void printp  (GEN g) { print0(g, f_PRETTYOLD); PR_NL(); }
void printtex(GEN g) { print0(g, f_TEX);       PR_NL(); }
void print1  (GEN g) { print0(g, f_RAW);       PR_NO(); }
void printp1 (GEN g) { print0(g, f_PRETTYOLD); PR_NO(); }

void error0(GEN g) { err(user, g); }

static char *
wr_check(const char *s) {
  char *t = expand_tilde(s);
  if (GP_DATA && GP_DATA->flags & SECURE)
  {
    fprintferr("[secure mode]: about to write to '%s'. OK ? (^C if not)\n",t);
    hit_return();
  }
  return t;
}

static void wr_init(const char *s) { char *t=wr_check(s); switchout(t); free(t);}
void gpwritebin(char *s, GEN x) { char *t=wr_check(s); writebin(t, x); free(t);}

#define WR_NL() {pariputc('\n'); pariflush(); switchout(NULL); }
#define WR_NO() {pariflush(); switchout(NULL); }
void write0  (const char *s, GEN g) { wr_init(s); print0(g, f_RAW); WR_NL(); }
void writetex(const char *s, GEN g) { wr_init(s); print0(g, f_TEX); WR_NL(); }
void write1  (const char *s, GEN g) { wr_init(s); print0(g, f_RAW); WR_NO(); }

/*******************************************************************/
/**                                                               **/
/**                       HISTORY HANDLING                        **/
/**                                                               **/
/*******************************************************************/
/* history management function:
 *   p > 0, called from %p
 *   p <= 0, called from %` (p backquotes, possibly 0) */
GEN
gp_history(gp_hist *H, long p, char *old, char *entry)
{
  GEN z;

  if (p <= 0) p += H->total; /* count |p| entries starting from last */
  if ((ulong)p > H->total)
    err(talker2, "I can't see into the future", old, entry);

  z = H->res[ (p-1) % H->size ];
  if (!z || p <= 0 || p <= (long)(H->total - H->size))
    err(talker2, "I can't remember before the big bang", old, entry);
  return z;
}

GEN
set_hist_entry(gp_hist *H, GEN x)
{
  int i = H->total % H->size;
  H->total++;
  if (H->res[i]) gunclone(H->res[i]);
  return H->res[i] = gclone(x);
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
  char *base, *sh = getenv("EMXSHELL");
  if (sh == NULL) sh = getenv("COMSPEC");
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

char *
env_ok(char *s)
{
  char *t = os_getenv(s);
  if (t && !pari_is_rwx(t))
  {
    err(warner,"%s is set (%s), but is not writeable", s,t);
    t = NULL;
  }
  if (t && !pari_is_dir(t))
  {
    err(warner,"%s is set (%s), but is not a directory", s,t);
    t = NULL;
  }
  return t;
}

static char*
pari_tmp_dir(void)
{
  char *s;
#ifdef WINCE
  s = env_ok("TEMP"); if (s) return s;
  return "\\temp";
#endif
  s = env_ok("GPTMPDIR"); if (s) return s;
  s = env_ok("TMPDIR"); if (s) return s;
#ifdef __EMX__
  s = env_ok("TMP"); if (s) return s;
  s = env_ok("TEMP"); if (s) return s;
#endif
#if defined(UNIX) || defined(__EMX__)
  if (pari_is_rwx("/tmp")) return "/tmp";
  if (pari_is_rwx("/var/tmp")) return "/var/tmp";
#endif
  return ".";
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
#endif
#if defined(__EMX__) || defined(WINCE)
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
