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
#include "paripriv.h"
#include "anal.h"

void
hit_return(void)
{
  int c;
  if (GP_DATA->flags & (EMACS|TEXMACS)) return;
  pariputs("---- (type RETURN to continue) ----");
  /* if called from a readline callback, may be in a funny TTY mode,  */
  do c = fgetc(stdin); while (c >= 0 && c != '\n' && c != '\r');
  pariputc('\n');
}

/********************************************************************/
/**                                                                **/
/**                        INPUT FILTER                            **/
/**                                                                **/
/********************************************************************/
#define ONE_LINE_COMMENT   2
#define MULTI_LINE_COMMENT 1
#define LBRACE '{'
#define RBRACE '}'
/* Filter F->s into F->t */
static char *
filtre0(filtre_t *F)
{
  const int downcase = F->downcase;
  const char *s = F->s;
  char *t;
  char c;

  if (!F->t) F->t = (char*)gpmalloc(strlen(s)+1);
  t = F->t;

  if (F->more_input == 1) F->more_input = 0;

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
    *t++ = downcase? tolower((int)c): c;

    switch(c)
    {
      case '/':
	if (*s == '*') { t--; F->in_comment = MULTI_LINE_COMMENT; }
	break;

      case '\\':
	if (!*s) {
	  if (t-2 >= F->t && t[-2] == '?') break; /* '?\' */
	  t--;
	  if (!F->more_input) F->more_input = 1;
	  goto END;
	}
	if (*s == '\r') s++; /* DOS */
	if (*s == '\n') {
	  if (t-2 >= F->t && t[-2] == '?') break; /* '?\' */
	  t--; s++;
	  if (!*s)
	  {
	    if (!F->more_input) F->more_input = 1;
	    goto END;
	  }
	} /* skip \<CR> */
	break;

      case '"': F->in_string = 1;
	break;

      case LBRACE:
	t--;
	if (F->wait_for_brace) pari_err(impl,"embedded braces (in parser)");
	F->more_input = 2;
	F->wait_for_brace = 1;
	break;

      case RBRACE:
	if (!F->wait_for_brace) pari_err(talker,"unexpected closing brace");
	F->more_input = 0; t--;
	F->wait_for_brace = 0;
	break;
    }
  }

  if (t != F->t) /* non empty input */
  {
    c = t[-1]; /* = last input char */
    if (c == '=')                 F->more_input = 2;
    else if (! F->wait_for_brace) F->more_input = 0;
    else if (c == RBRACE)       { F->more_input = 0; t--; F->wait_for_brace--;}
  }

END:
  F->end = t; *t = 0; return F->t;
}
#undef ONE_LINE_COMMENT
#undef MULTI_LINE_COMMENT

char *
filtre(const char *s, int downcase)
{
  filtre_t T;
  T.s = s;    T.in_string = 0; T.more_input = 0;
  T.t = NULL; T.in_comment= 0; T.wait_for_brace = 0;
  T.downcase = downcase;
  return filtre0(&T);
}

void
init_filtre(filtre_t *F, Buffer *buf)
{
  F->buf = buf;
  F->in_string  = 0;
  F->in_comment = 0;
  F->downcase = 0;
}

/********************************************************************/
/**                                                                **/
/**                        INPUT METHODS                           **/
/**                                                                **/
/********************************************************************/
/* create */
Buffer *
new_buffer(void)
{
  Buffer *b = (Buffer*) gpmalloc(sizeof(Buffer));
  b->len = 1024;
  b->buf = (char*)gpmalloc(b->len);
  return b;
}
/* delete */
void
delete_buffer(Buffer *b)
{
  if (!b) return;
  gpfree((void*)b->buf); gpfree((void*)b);
}
/* resize */
void
fix_buffer(Buffer *b, long newlbuf)
{
  b->len = newlbuf;
  b->buf = (char*)gprealloc((void*)b->buf, b->len);
}

static int
gp_read_stream_buf(FILE *fi, Buffer *b)
{
  input_method IM;
  filtre_t F;

  init_filtre(&F, b);

  IM.file = fi;
  IM.fgets= &fgets;
  IM.getline= &file_input;
  IM.free = 0;
  return input_loop(&F,&IM);
}

GEN
gp_read_stream(FILE *fi)
{
  Buffer *b = new_buffer();
  GEN x = gp_read_stream_buf(fi, b)? readseq(b->buf): gnil;
  delete_buffer(b); return x;
}

GEN
gp_read_file(char *s)
{
  GEN x = gnil;
  switchin(s);
  if (file_is_binary(pari_infile)) {
    int junk;
    x = readbin(s,pari_infile, &junk);
  } else {
    Buffer *b = new_buffer();
    x = gnil;
    for (;;) {
      if (!gp_read_stream_buf(pari_infile, b)) break;
      if (*(b->buf)) x = readseq(b->buf);
    }
    delete_buffer(b);
  }
  popinfile(); return x;
}

GEN
gp_readvec_stream(FILE *fi)
{
  pari_sp ltop = avma;
  Buffer *b = new_buffer();
  long i = 1, n = 16;
  GEN z = cgetg(n+1,t_VEC);
  for(;;)
  {
    if (!gp_read_stream_buf(fi, b)) break;
    if (!*(b->buf)) continue;
    if (i>n)
    {
      if (DEBUGLEVEL) fprintferr("gp_readvec_stream: reaching %ld entries\n",n);
      n <<= 1;
      z = vec_lengthen(z,n);
    }
    gel(z,i++) = readseq(b->buf);
  }
  if (DEBUGLEVEL) fprintferr("gp_readvec_stream: found %ld entries\n",i-1);
  setlg(z,i); delete_buffer(b);
  return gerepilecopy(ltop,z);
}

GEN
gp_readvec_file(char *s)
{
  GEN x = NULL;
  switchin(s);
  if (file_is_binary(pari_infile)) {
    int junk;
    x = readbin(s,pari_infile,&junk);
  } else
    x = gp_readvec_stream(pari_infile);
  popinfile(); return x;
}

/* Read from file (up to '\n' or EOF) and copy at s0 (points in b->buf) */
char *
file_input(char **s0, int junk, input_method *IM, filtre_t *F)
{
  Buffer *b = (Buffer*)F->buf;
  int first = 1;
  char *s = *s0;
  ulong used0, used = s - b->buf;

  (void)junk;
  used0 = used;
  for(;;)
  {
    ulong left = b->len - used, l;

    if (left < 512)
    {
      fix_buffer(b, b->len << 1);
      left = b->len - used;
      *s0 = b->buf + used0;
    }
    s = b->buf + used;
    if (! IM->fgets(s, left, IM->file))
      return first? NULL: *s0; /* EOF */

    l = strlen(s); first = 0;
    if (l+1 < left || s[l-1] == '\n') return *s0; /* \n */
    used += l;
  }
}

/* Read a "complete line" and filter it. Return: 0 if EOF, 1 otherwise */
int
input_loop(filtre_t *F, input_method *IM)
{
  Buffer *b = (Buffer*)F->buf;
  char *to_read, *s = b->buf;

  /* read first line */
  if (! (to_read = IM->getline(&s,1, IM, F)) ) { check_filtre(F); return 0; }

  /* buffer is not empty, init filter */
  F->in_string = 0;
  F->more_input= 0;
  F->wait_for_brace = 0;
  for(;;)
  {
    F->s = to_read;
    F->t = s;
    (void)filtre0(F); /* pre-processing of line, read by previous call to IM->getline */
    if (IM->free) gpfree(to_read);
    if (! F->more_input) break;

    /* read continuation line */
    s = F->end;
    to_read = IM->getline(&s,0, IM, F);
    if (!to_read) break;
  }
  return 1;
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
  if (pari_logfile) putc(c, pari_logfile);
}
static void
normalOutS(const char *s)
{
  fputs(s, pari_outfile);
  if (pari_logfile) { fputs(s, pari_logfile); }
}
static void
normalOutF(void)
{
  fflush(pari_outfile);
  if (pari_logfile) fflush(pari_logfile);
}
PariOUT defaultOut = {normalOutC, normalOutS, normalOutF, NULL};

static void
normalErrC(char c)
{
  putc(c, pari_errfile);
  if (pari_logfile) putc(c, pari_logfile);
}
static void
normalErrS(const char *s)
{
  fputs(s, pari_errfile);
  if (pari_logfile) fputs(s, pari_logfile);
}
static void
normalErrF(void)
{
  fflush(pari_errfile);
  if (pari_logfile) fflush(pari_logfile);
}
PariOUT defaultErr = {normalErrC, normalErrS, normalErrF, NULL};

/**                         GENERIC PRINTING                       **/
void
initout(int initerr)
{
  pari_infile = stdin; pari_outfile = stdout; pari_errfile = stderr;
  pariOut = &defaultOut;
  if (initerr) pariErr = &defaultErr;
}

static int last_was_newline = 0;

void
pariputc(char c) {
  last_was_newline = (c == '\n');
  pariOut->putch(c);
}

void
pariputs(const char *s) {
  if (*s) {
    last_was_newline = s[strlen(s)-1] == '\n';
    pariOut->puts(s);
  } else
    last_was_newline = 0;
}

int
pari_last_was_newline(void) { return last_was_newline; }
void
pari_set_last_newline(int last) { last_was_newline = last; }

void
pariflush(void) { pariOut->flush(); }

void
flusherr(void) { pariErr->flush(); }

static void
_initout(pariout_t *T, char f, long sigd, long sp, long fieldw, int prettyp)
{
  T->format = f;
  T->sigd = sigd;
  T->sp = sp;
  T->fieldw = fieldw;
  T->prettyp = prettyp;
}

static void
printGEN(GEN x, pariout_t *T)
{
  if (typ(x)==t_STR)
    pariputs(GSTR(x)); /* text surrounded by "" otherwise */
  else
    gen_output(x, T);
}

/* FIXME: OLD VERSION */
/* format is standard printf format, except %Z is a GEN */
void
vpariputs(const char* format, va_list args)
{
  long nb = 0, bufsize = 1023;
  const char *f = format;
  char *buf, *str, *s, *t;

  /* replace each %Z (2 chars) by braced address format (8 chars) */
  s = str = (char*)gpmalloc(strlen(format)*4 + 1);
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
  for(;;) /* loop to find a buffer size long enough */
  {
    int l;
    buf = (char*)gpmalloc(bufsize);
    l = vsnprintf(buf,bufsize,str,args);
    if (l < 0)
      l = bufsize<<1;
    else if (l < bufsize)
      break;
    gpfree(buf); bufsize = l + 1;
  }
  buf[bufsize-1] = 0; /* just in case */
#else
  buf = (char*)gpmalloc(bufsize);
  (void)vsprintf(buf,str,args); /* pray it does fit */
#endif
  t = s = buf;
  if (nb)
  {
    pariout_t T = *(GP_DATA->fmt); /* copy */
    T.prettyp = f_RAW;
    for(;;)
    {
      if (*t == '\003' && t[21] == '\003')
      {
        *t = 0; t[21] = 0; /* remove the bracing chars */
        pariputs(s); printGEN((GEN)atol(t+1), &T);
        t += 22; s = t;
        if (!--nb) break;
      }
      else t++;
    }
  }
  pariputs(s); gpfree(buf); gpfree(str);
}

/* e binary exponent, return exponent in base ten */
static long
ex10(long e) { return (long) ((e >= 0)? e*L2SL10: -(-e*L2SL10)-1); }

static char *
zeros(char *b, long nb) { while (nb-- > 0) *b++ = '0'; *b = 0; return b; }

/* # of decimal digits, assume l > 0 */
static long
numdig(ulong l)
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
copart(char *s, ulong x, long start)
{
  char *p = s + start;
  while (p > s)
  {
    ulong q = x/10;
    *--p = (x - q*10) + '0';
    x = q;
  }
}

/* convert abs(x) != 0 to str. Prepend '-' if (sx < 0) */
static char *
itostr_sign(GEN x, int sx, long *len)
{
  long l, d;
  ulong *res = convi(x, &l);
  char *s = (char*)new_chunk(nchar2nlong(l*9 + (sx<0) + 1)), *t = s;

  if (sx < 0) *t++ = '-';
  d = numdig(*--res);
  copart(t, *res, d); t += d;
  while (--l > 0) { copart(t, *--res, 9); t += 9; }
  *t = 0; *len = t - s; return s;
}

/********************************************************************/
/**                                                                **/
/**                        WRITE A REAL NUMBER                     **/
/**                                                                **/
/********************************************************************/
/* 19 digits (if 64 bits, at most 2^60-1) + 1 sign */
static const long MAX_EXPO_LEN = 20;

/* FIXME: to be eventually deleted */
#define PB
#undef PB
/* FIXME: to be deleted */
static THREAD const char *saved_format = NULL;

/* sss.ttt, assume 'point' < ls = strlen(s) */
static char *
wr_dec(char *buf, char *s, size_t ls, long point)
{
  if (ls)
  {
    strncpy(buf, s, point); /* integer part */
    buf += point;
    s   += point;
    ls  -= point;
  }
  *buf++ = '.';
  strcpy(buf, s);
  buf += ls; *buf = 0; return buf;
}

static char *
zerotostr() 
{
  char *s = (char*)new_chunk(1);
  s[0] = '0';
  s[1] = 0; return s;
}

/* Return t_REAL |x| in floating point format.
 * Allocate freely, the caller must clean the stack.
 *   FORMAT: E/e (exponential), f (floating point), G/g
 *   wanted_dec: number of significant digits to print (all if < 0).
 *   width_frac: number of digits in fractional part (< 0 if unset) */
static char *
absrtostr(GEN x, int sp, char FORMAT, long wanted_dec, int width_frac)
{
  const char format = tolower(FORMAT), exp_char = (format == FORMAT)? 'e': 'E';
  long sx = signe(x), ex = expo(x);
  char *s, *buf, *buf0;
  long beta, ls, df2, lx;
  GEN z;

  if (!sx) { /* real 0 */
    if (format == 'f') {
      long dec;
      if (width_frac == 0) return zerotostr();
      if (width_frac > 0)
        dec = width_frac;
      else
      {
        dec = wanted_dec;
        if (dec < 0) dec = (ex >= 0)? 0: (long)(-ex * L2SL10);
      }
      buf0 = buf = stackmalloc(dec + 3);
      *buf++ = '0';
      *buf++ = '.';
      (void)zeros(buf, dec);
    } else {
      buf0 = buf = stackmalloc(3 + MAX_EXPO_LEN + 1);
      *buf++ = '0';
      *buf++ = '.';
      *buf++ = exp_char;
      sprintf(buf, "%ld", ex10(ex) + 1);
    }
    return buf0;
  } /* string for a zero */

  /* x != 0 */
  lx = lg(x);
  if (wanted_dec >= 0)
  { /* reduce precision if possible */
    long w = ndec2prec(wanted_dec); /* digits -> pari precision in words */
    if (lx > w) lx = w; /* truncature with guard, no rounding */
  }
  if (width_frac >= 0)
    beta = width_frac;
  else
    beta = ex10( bit_accuracy(lx) - expo(x) );

  if (beta)
  { /* z = |x| 10^beta, 10^b = 5^b * 2^b, 2^b goes into exponent */
    if (beta > 0)
      z = mulrr(x, rpowuu(5UL, (ulong)beta, lx+1));
    else
      z = divrr(x, rpowuu(5UL, (ulong)-beta, lx+1));
    z[1] = evalsigne(1) | evalexpo(expo(z) + beta);
  }
  else
    z = x;
  z = grndtoi(z, &ls); /* round; ls is junk */
  s = itostr_sign(z, 1, &ls);

  if (wanted_dec < 0)
    wanted_dec = ls;
  else if (width_frac < 0 && ls > wanted_dec)
  {
    beta -= ls - wanted_dec;
    ls = wanted_dec;
    if (s[ls] >= '5') /* round up */
    {
      long i;
      for (i = ls-1; i >= 0; s[i--] = '0')
      {
        s[i]++;
        if (s[i] <= '9') break;
      }
      if (i < 0) { s[0] = '1'; beta--; }
    }
    s[ls] = 0;
  }

  /* '.', " E", exponent, trailing \0 */
  buf0 = buf = stackmalloc( ls + 1+2+MAX_EXPO_LEN+1 );
  df2 = ls - beta; /* position of . in s; < 0 or > 0 */
  if (width_frac < 0 &&
     (beta < 0 || format == 'e' || (format == 'g' && ex < -32)))
  { /* e format */
    buf = wr_dec(buf, s, ls, 1);
    if (sp) *buf++ = ' ';
    *buf++ = exp_char;
    sprintf(buf, "%ld", df2-1);
  }
  else if (df2 > 0) /* f format, write integer_part.fractional_part */
    (void)wr_dec(buf, s, ls, df2);
  else { /* f format, df2 <= 0, fractional part must be written */
    *buf++ = '0';
    *buf++ = '.';
    buf = zeros(buf, -df2);
    strcpy(buf, s);
  }
  return buf0;
}

/* This vsnprintf implementation is adapted from snprintf.c to be found at
 *
 * http://www.nersc.gov/~scottc/misc/docs/snort-2.1.1-RC1/snprintf_8c-source.html
 * The original code was
 *   Copyright (C) 1998-2002 Martin Roesch <roesch@sourcefire.com>
 * available under the terms of the GNU GPL version 2 or later. It
 * was itself adapted from an original version by Patrick Powell.
*/

/* Modifications for format %Z: R.Butel IMB/CNRS 2007/12/03 */

static THREAD const char *DoprEnd; /* ending of the output buffer */
static THREAD int SnprfOverflow; /* counts number of overflows out of the output buffer */
static THREAD char *z_output; /* the current writing place in the output buffer */

static void
dopr_outch(int c)
{
  if (z_output < DoprEnd)
    *z_output++ = c;
  else
    SnprfOverflow++;
}

/* print chars 1 by 1 to prevent overflow and count them */
static void
dostr(const char *str)
{
  while (*str) dopr_outch(*str++);
}
static void
dostrcut(const char *str, int cut)
{
  if (cut < 0) dostr(str);
  else {
    while (*str && cut-- > 0) dopr_outch(*str++);
  }
}

/* lbuf = strlen(buf), len < 0: unset */
static void
outpad(const char *buf, long lbuf, int sign, long ljust, long len, long zpad)
{
  long padlen = len - lbuf;
  if (padlen < 0) padlen = 0;
  if (ljust) padlen = -padlen;
  if (zpad && padlen > 0) {
    if (sign) { dopr_outch(sign); --padlen; }
    while (padlen > 0) { dopr_outch('0'); --padlen; }
  }
  else
  {
    if (sign) --padlen;
    while (padlen > 0) { dopr_outch(' '); --padlen; }
    if (sign) dopr_outch(sign);
  }
  dostr(buf);
  while (padlen < 0) { dopr_outch(' '); ++padlen; }
}

/* len < 0 or maxwidth < 0: unset */
static void
fmtstr(const char *buf, int ljust, int len, int maxwidth)
{
  int padlen, lbuf = strlen(buf);

  if (maxwidth >= 0 && lbuf > maxwidth) lbuf = maxwidth;

  padlen = len - lbuf;
  if (padlen < 0) padlen = 0;
  if (ljust) padlen = -padlen;
  while (padlen > 0) { dopr_outch(' '); --padlen; }
  dostrcut(buf, maxwidth);
  while (padlen < 0) { dopr_outch(' '); ++padlen; }
}

/* abs(base) is 8, 10, 16. If base < 0, some "alternate" form
 * -- print hex in uppercase
 * -- prefix octal with 0
 * signvalue = -1: unsigned, otherwise ' ' or '+' */
static void
fmtnum(long lvalue, GEN gvalue, int base, int signvalue,
       int ljust, int len, int zpad)
{
  int caps;
  char *buf0, *buf;
  long lbuf, mxl;
  GEN uvalue = NULL;
  ulong ulvalue = 0;
  pari_sp av = avma;

  if (gvalue)
  {
    long vz, s;
    if (typ(gvalue) != t_INT) {
      long i, j, h, l = lg(gvalue);
      switch(typ(gvalue))
      {
        case t_VEC:
          dopr_outch('[');
          for (i = 1; i < l; i++)
          {
            fmtnum(0, gel(gvalue,i), base, signvalue, ljust,len,zpad);
            if (i < l-1) dopr_outch(',');
          }
          dopr_outch(']');
          return;
        case t_COL:
          dopr_outch('[');
          for (i = 1; i < l; i++)
          {
            fmtnum(0, gel(gvalue,i), base, signvalue, ljust,len,zpad);
            if (i < l-1) dopr_outch(',');
          }
          dopr_outch(']');
          dopr_outch('~');
          return;
        case t_MAT:
          if (l == 1)
            dostr("[;]");
          else
          {
            h = lg(gvalue[1]);
            for (i=1; i<l; i++)
            {
              dopr_outch('[');
              for (j=1; j<h; j++)
              {
                fmtnum(0, gcoeff(gvalue,i,j), base, signvalue, ljust,len,zpad);
                if (j<h-1) dopr_outch(' ');
              }
              dopr_outch(']');
              dopr_outch('\n');
              if (i<l-1) dopr_outch('\n');
            }
          }
          return;
      }
      gvalue = gfloor( simplify_i(gvalue) );
      if (typ(gvalue) != t_INT)
        pari_err(talker,"not a t_INT in integer format conversion: %Z", gvalue);
    }
    s = signe(gvalue);
    if (!s) { lbuf = 1; buf = zerotostr(); goto END; }

    uvalue = gvalue;
    if (signvalue < 0)
    {
      if (s < 0) uvalue = addii(int2n(bit_accuracy(lgefint(gvalue))), gvalue);
      signvalue = 0;
    }
    else
    {
      if (s < 0) { signvalue = '-'; uvalue = absi(uvalue); }
    }
    vz = sizedigit(gvalue) + 1;
    mxl = vz * 2 + 10; /* 2 needed for octal, 1 is enough otherwise */
  } else {
    double vz;
    ulvalue = lvalue;
    if (signvalue < 0)
      signvalue = 0;
    else
      if (lvalue < 0) { signvalue = '-'; ulvalue = - lvalue; }
    vz = log(ulvalue) / log(10);
    mxl = (long)vz * 2 + 1;
  }
  if (base > 0) caps = 0; else { caps = 1; base = -base; }

  buf0 = buf = stackmalloc(mxl) + mxl; /* fill from the right */
  *--buf = 0; /* trailing \0 */
  if (gvalue) {
    if (base == 10) {
      long i, l, cnt;
      ulong *larray = convi(uvalue, &l);
      larray -= l;
      for (i = 0; i < l; i++) {
        cnt = 0;
        ulvalue = larray[i];
        do {
          *--buf = '0' + ulvalue%10;
          ulvalue = ulvalue / 10;
          cnt++;
        } while (ulvalue);
        if (i + 1 < l)
          for (;cnt<9;cnt++) *--buf = '0';
      }
    } else if (base == 16) {
      long i, l = lgefint(uvalue);
      GEN up = int_LSW(uvalue);
      for (i = 2; i < l; i++, up = int_nextW(up)) {
        ulong ucp = (ulong)*up;
        long j;
        for (j=0; j < BITS_IN_LONG/4; j++) {
          unsigned char cv = ucp & 0xF;
          *--buf = (caps? "0123456789ABCDEF":"0123456789abcdef")[cv];
          ucp >>= 4;
          if (ucp == 0 && i+1 == l) break;
        }
      } /* loop on hex digits in word */
    } else if (base == 8) {
      long i, l = lgefint(uvalue);
      GEN up = int_LSW(uvalue);
      ulong rem = 0;
      int shift = 0;
      int mask[3] = {0, 1, 3};
      for (i = 2; i < l; i++, up = int_nextW(up)) {
        ulong ucp = (ulong)*up;
        long j, ldispo = BITS_IN_LONG;
        if (shift) { /* 0, 1 or 2 */
          unsigned char cv = ((ucp & mask[shift]) <<(3-shift)) + rem;
          *--buf = "01234567"[cv];
          ucp >>= shift;
          ldispo -= shift;
        };
        shift = (shift + 3 - BITS_IN_LONG % 3) % 3;
        for (j=0; j < BITS_IN_LONG/3; j++) {
          unsigned char cv = ucp & 0x7;
          if (ucp == 0 && i+1 == l) { rem = 0; break; };
          *--buf = "01234567"[cv];
          ucp >>= 3;
          ldispo -= 3;
          rem = ucp;
          if (ldispo < 3) break;
        }
      } /* loop on hex digits in word */
      if (rem) *--buf = "01234567"[rem];
    }
  } else { /* not a gvalue, thus a standard integer */
    do {
      *--buf = (caps? "0123456789ABCDEF":"0123456789abcdef")[ulvalue % (unsigned)base ];
      ulvalue /= (unsigned)base;
    } while (ulvalue);
  }
  /* leading 0 if octal and alternate # form */
  if (caps && base == 8) *--buf = '0';
  lbuf = (buf0 - buf) - 1;
END:
  outpad(buf, lbuf, signvalue, ljust, len, zpad);
  avma = av;
}

static GEN
v_get_arg(GEN arg_vector, int *index)
{
  if (*index >= lg(arg_vector))
    pari_err(talker, "missing arg %d for printf format '%s'", *index, saved_format);
  return gel(arg_vector, (*index)++);
}

static int
dosign(int blank, int plus)
{
  if (plus) return('+');
  if (blank) return(' ');
  return 0;
}

/* x * 10 + 'digit whose char value is ch'. Do not check for overflow */
static int
shift_add(int x, int ch)
{
  if (x < 0) /* was unset */
    x = ch - '0';
  else
    x = x*10 + ch - '0';
  return x;
}

static void
fmtreal(GEN gvalue, int space, int signvalue, int FORMAT,
        long sigd, int maxwidth, int ljust, int len, int zpad)
{
  pari_sp av = avma;
  char *buf;
  if (typ(gvalue) != t_REAL)
  {
    long i, j, h, l = lg(gvalue);
    switch(typ(gvalue))
    {
      case t_VEC:
        dopr_outch('[');
        for (i = 1; i < l; i++)
        {
          fmtreal(gel(gvalue,i), space, signvalue, FORMAT, sigd,
                  maxwidth, ljust,len,zpad);
          if (i < l-1) dopr_outch(',');
        }
        dopr_outch(']');
        return;
      case t_COL:
        dopr_outch('[');
        for (i = 1; i < l; i++)
        {
          fmtreal(gel(gvalue,i), space, signvalue, FORMAT, sigd,
                  maxwidth, ljust,len,zpad);
          if (i < l-1) dopr_outch(',');
        }
        dopr_outch(']');
        dopr_outch('~');
        return;
      case t_MAT:
        if (l == 1)
          dostr("[;]");
        else
        {
          h = lg(gvalue[1]);
          for (i=1; i<l; i++)
          {
            dopr_outch('[');
            for (j=1; j<h; j++)
            {
              fmtreal(gcoeff(gvalue,i,j), space, signvalue, FORMAT, sigd,
                      maxwidth, ljust,len,zpad);
              if (j<h-1) dopr_outch(' ');
            }
            dopr_outch(']');
            dopr_outch('\n');
            if (i<l-1) dopr_outch('\n');
          }
        }
        return;
    }
    gvalue = gtofp(gvalue, ndec2prec(sigd));
    if (typ(gvalue) != t_REAL)
      pari_err(talker,"impossible conversion to t_REAL: %Z",gvalue);
  }
  buf = absrtostr(gvalue, space, FORMAT, sigd, maxwidth);
  if (signe(gvalue) < 0) signvalue = '-';
  outpad(buf, strlen(buf), signvalue, ljust, len, zpad);
  avma = av;
}
/* format handling "inspired" by the standard draf at 
-- http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1124.pdf pages 274ff
Some conversions not implemented */
static void
sm_dopr(pariout_t *T, char *buffer, const char *format, int is_a_list,
        va_list args)
{
  int longflag = 0, pointflag = 0, print_a_plus, print_a_blank, with_sharp;
  int ch, ljust, len, maxwidth, zpad;
  char *strvalue;
  long lvalue;
  int index = 1;
  GEN gvalue, arg_vector = is_a_list? NULL: va_arg(args, GEN);
  const char *recall = NULL;

  SnprfOverflow = 0;
  saved_format = format;

  while ((ch = *format++) != '\0') {
    switch(ch) {
      case '%':
        ljust = zpad = 0;
        len = maxwidth = -1;
        longflag = pointflag = 0;
        recall = format - 1; /* '%' was skipped */
        print_a_plus = print_a_blank = with_sharp = 0;
nextch:
        ch = *format++;
        switch(ch) {
          case 0:
            pari_err(talker, "printf: end of format");
/*------------------------------------------------------------------------
                             -- flags
------------------------------------------------------------------------*/
          case '-':
            ljust = 1;
            goto nextch;
          case '+':
            print_a_plus = 1;
            goto nextch;
          case '#':
            with_sharp = 1;
            goto nextch;
          case ' ':
            print_a_blank = 1;
            goto nextch;
          case '0':
            /* appears as a flag: set zero padding */
            if (len < 0 && !pointflag) { zpad = '0'; goto nextch; }

            /* else part of a field width or precision */
            /* fall through */
/*------------------------------------------------------------------------
                       -- maxwidth or precision
------------------------------------------------------------------------*/
          case '1':
          case '2':
          case '3':
          case '4':
          case '5':
          case '6':
          case '7':
          case '8':
          case '9':
            if (pointflag)
              maxwidth = shift_add(maxwidth, ch);
            else
              len = shift_add(len, ch);
            goto nextch;

          case '*':
          {
            int *t = pointflag? &maxwidth: &len;
            if (is_a_list)
              *t = va_arg(args, int);
            else
              *t = (int)gtolong( v_get_arg(arg_vector, &index) );
            goto nextch;
          }
          case '.':
            if (pointflag)
              pari_err(talker, "printf: two '.' in conversion specification");
            pointflag = 1;
            goto nextch;
/*------------------------------------------------------------------------
                       -- length modifiers
------------------------------------------------------------------------*/
          case 'l':
            longflag = 1;
            goto nextch;
          case 'h': /* dummy: va_arg promotes short into int */
            goto nextch;
/*------------------------------------------------------------------------
                       -- conversions
------------------------------------------------------------------------*/
          case 'u': /* not a signed conversion: print_a_(blank|plus) ignored */
            if (is_a_list) {
              lvalue = longflag? va_arg(args, long): va_arg(args, int);
              gvalue = NULL;
            } else {
              lvalue = 0;
              gvalue = v_get_arg(arg_vector, &index);
            }
            fmtnum(lvalue, gvalue, 10, -1, ljust, len, zpad);
            break;
          case 'o': /* not a signed conversion: print_a_(blank|plus) ignored */
            if (is_a_list) {
              lvalue = longflag? va_arg(args, long): va_arg(args, int);
              gvalue = NULL;
            } else {
              lvalue = 0;
              gvalue = v_get_arg(arg_vector, &index);
            }
            fmtnum(lvalue, gvalue, with_sharp? -8: 8, -1, ljust, len, zpad);
            break;
          case 'd':
          case 'i':
            if (is_a_list) {
              lvalue = longflag? va_arg(args, long): va_arg(args, int);
              gvalue = NULL;
            } else {
              lvalue = 0;
              gvalue = v_get_arg(arg_vector, &index);
            }
            fmtnum(lvalue, gvalue, 10,
                   dosign(print_a_blank, print_a_plus), ljust, len, zpad);
            break;
          case 'p':
            dopr_outch('0'); dopr_outch('x');
            if (is_a_list)
              lvalue = longflag? va_arg(args, long): va_arg(args, int);
            else
              lvalue = (long)v_get_arg(arg_vector, &index);
            fmtnum(lvalue, NULL, 16, -1, ljust, len, zpad);
            break;
          case 'x': /* not a signed conversion: print_a_(blank|plus) ignored */
            if (with_sharp) { dopr_outch('0'); dopr_outch('x'); }
            if (is_a_list) {
              lvalue = longflag? va_arg(args, long): va_arg(args, int);
              gvalue = NULL;
            } else {
              lvalue = 0;
              gvalue = v_get_arg(arg_vector, &index);
            }
            fmtnum(lvalue, gvalue, 16, -1, ljust, len, zpad);
            break;
          case 'X': /* not a signed conversion: print_a_(blank|plus) ignored */
            if (with_sharp) { dopr_outch('0'); dopr_outch('X'); }
            if (is_a_list) {
              lvalue = longflag? va_arg(args, long): va_arg(args, int);
              gvalue = NULL;
            } else {
              gvalue = v_get_arg(arg_vector, &index);
              lvalue = 0;
            }
            fmtnum(lvalue, gvalue,-16, -1, ljust, len, zpad);
            break;
          case 'Z': //-- %Z IS HERE. FIXME.
          {
            char *plus;
            if (is_a_list)
              gvalue = va_arg(args, GEN);
            else
              gvalue = v_get_arg(arg_vector, &index);
            if (len >= 0 || maxwidth >= 0) {
              pariout_t Tcopy;
              /*_initout(pariout_t *T, char f, long sigd, long sp, long fieldw, int prettyp) */
              /* char format; e,f,g */
              /* long fieldw; field width */
              /* long sigd;  -1 (all) or number of significant digits printed */
              /* int sp;   0 = suppress whitespace from output */
              /* int prettyp; output style: raw, prettyprint, etc */
              _initout(&Tcopy,tolower(ch),len,1,maxwidth, f_RAW);
              plus = GENtostr0(gvalue, &Tcopy, &gen_output);
            } else
              plus = GENtostr(gvalue);
            dostr(plus); free(plus);
            break;
          }
          case 's':
          {
            int to_free;
            if (is_a_list) {
              strvalue = va_arg(args, char *);
              to_free = 0;
            } else {
              gvalue = v_get_arg(arg_vector, &index);
              strvalue = GENtostr(gvalue);
              to_free = 1;
            }
            fmtstr(strvalue, ljust, len, maxwidth);
            if (to_free) gpfree(strvalue);
            break;
          }
          case 'c':
            if (is_a_list) ch = va_arg(args, int);
            else {
              gvalue = v_get_arg(arg_vector, &index);
              ch = (int)gtolong(gvalue);
            }
            dopr_outch(ch);
            break;

          case '%':
            dopr_outch(ch);
            continue;
          case 'g':
          case 'G':
          case 'e':
          case 'E':
          case 'f':
            if (is_a_list) {
              char work[256], subfmt[256];
              double dvalue = va_arg(args, double);

              strncpy(subfmt, recall, format - recall);
              subfmt[format - recall] = 0;
              sprintf(work, subfmt, dvalue);
            } else {
              long sigd = prec2ndec(precreal);

              gvalue = v_get_arg(arg_vector, &index);
              gvalue = simplify_i(gvalue);
              if (maxwidth >= 0) switch(tolower(ch))
              {
                case 'e': sigd = maxwidth+1; maxwidth = -1; break;
                case 'f': sigd = ex10(gexpo(gvalue)) + 1 + maxwidth; break;
                case 'g': sigd = maxwidth; maxwidth = -1; break;
              }
              fmtreal(gvalue, T->sp, dosign(print_a_blank, print_a_plus), ch,
                      sigd, maxwidth, ljust, len, zpad);

            }
            break;
          default:
            pari_err(talker, "invalid conversion or specification %c in format `%s'", ch, saved_format);
        } /* second switch on ch */
        break;
      default:
        dopr_outch(ch);
        break;
    } /* first switch on ch */
  } /* while loop on ch */
  *z_output = 0;
}

/* format is standard printf format, except %Z is a GEN; C call */
static GEN
v3pariputs(const char* format, int is_a_list, int return_string, ...)
{
  char *s = NULL;
  long bsiz = 1023;
  va_list args;
  GEN res = NULL;

  for(;;) {
    va_start(args,return_string);
    s = (char*)gprealloc(s, bsiz + 1);
    z_output = s;
    DoprEnd = s + bsiz;
    sm_dopr(GP_DATA->fmt, s, format, is_a_list, args);
    if (SnprfOverflow == 0) break;
    if (SnprfOverflow < bsiz)
      bsiz <<= 1;
    else
      bsiz += SnprfOverflow + 10;
    s = (char*)gprealloc(s, bsiz + 1);
  }
  va_end(args);
  if (return_string) res = strtoGENstr(s); else pariputs(s);
  gpfree(s);
  return res;
}

void
pariprintf(const char *format, ...)
{
  va_list args;

  va_start(args,format); vpariputs(format,args);
  va_end(args);
}

/* start printing in "color" c */
/* terminal has to support ANSI color escape sequences */
void
term_color(long c)
{
  FILE *o_logfile = pari_logfile;

  if (logstyle != logstyle_color) pari_logfile = 0; /* Ugly hack */
  /* _not_ pariputs, because of last_was_newline */
  pariOut->puts(term_get_color(c));
  pari_logfile = o_logfile;
}

void
decode_color(long n, long *c)
{
  c[1] = n & 0xf; n >>= 4; /* foreground */
  c[2] = n & 0xf; n >>= 4; /* background */
  c[0] = n & 0xf; /* attribute */
}

#ifdef ESC
#  undef ESC
#endif
#define ESC  (0x1f & '[') /* C-[ = escape */

const char *
term_get_color(long n)
{
  static char s[16];
  long c[3], a;

  if (disable_color) return "";
  if (n == c_NONE || (a = gp_colors[n]) == c_NONE)
    sprintf(s, "%c[0m",ESC); /* reset */
  else
  {
    decode_color(a,c);
    if (c[1]<8) c[1] += 30; else c[1] += 82;
    if (a & (1<<12)) /* transparent background */
      sprintf(s, "%c[%ld;%ldm", ESC, c[0], c[1]);
    else
    {
      if (c[2]<8) c[2] += 40; else c[2] += 92;
      sprintf(s, "%c[%ld;%ld;%ldm", ESC, c[0], c[1], c[2]);
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
#undef larg /* problems with SCO Unix headers (ioctl_arg) */
#ifdef HAS_TIOCGWINSZ
#  include <sys/termios.h>
#  include <sys/ioctl.h>
#endif

static int
term_width_intern(void)
{
  if (GP_DATA->flags & TEST) return 0;
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!(GP_DATA->flags & (EMACS|TEXMACS))
     && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_col;
  }
#endif
  {
    char *str;
    if ((str = os_getenv("COLUMNS"))) return atoi(str);
  }
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
  if (GP_DATA->flags & TEST) return 0;
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!(GP_DATA->flags & (EMACS|TEXMACS))
     && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_row;
  }
#endif
  {
    char *str;
    if ((str = os_getenv("LINES"))) return atoi(str);
  }
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
  if (c == '\n') col_index = 0;
  else if (col_index == MAX_WIDTH) { normalOutC('\n'); col_index = 1; }
  else col_index++;
  normalOutC(c);
}
#undef MAX_WIDTH
static void
puts80(const char *s)
{
  while (*s) putc80(*s++);
}
PariOUT pariOut80= {putc80, puts80, normalOutF, NULL};

void
init80col(long n) { col_index = n; pariOut = &pariOut80; }

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
_new_line(const char *prefix)
{
  pariputc('\n'); if (prefix) pariputs(prefix);
}

static long
strlen_real(const char *s)
{
  const char *t = s, *t0;
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
print_prefixed_text(const char *s, const char *prefix, const char *str)
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
static outString *OutStr, *ErrStr = NULL; /* %%%%%% THREAD ? */

#define STEPSIZE 1024
#define check_output_length(str,l) { \
  const ulong s = str->size; \
  if (str->len + l >= s) { \
    str->size = s + l + STEPSIZE; \
    str->string = (char*)gprealloc((void*)str->string, str->size); \
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
stack_strdup(const char *s)
{
  long n = strlen(s)+1;
  char *t = stackmalloc(n);
  memcpy(t,s,n); return t;
}

char *
pari_strdup(const char *s)
{
  long n = strlen(s)+1;
  char *t = (char*)gpmalloc(n);
  memcpy(t,s,n); return t;
}

char *
pari_strndup(const char *s, long n)
{
  char *t = (char*)gpmalloc(n+1);
  memcpy(t,s,n); t[n] = 0; return t;
}

/* returns a malloc-ed string, which should be freed after usage */
char *
GENtostr0(GEN x, pariout_t *T, void (*do_out)(GEN, pariout_t*))
{
  PariOUT *tmp = pariOut;
  outString *tmps = OutStr, newStr;
  int last = pari_last_was_newline();

  if (typ(x) == t_STR) return pari_strdup(GSTR(x));
  pariOut = &pariOut2Str;
  newStr.len   = 0;
  newStr.size  = 0;
  newStr.string= NULL; OutStr = &newStr;
  do_out(x, T);
  OutStr->string[OutStr->len] = 0;
  pari_set_last_newline(last);

  pariOut = tmp; OutStr = tmps; return newStr.string;
}

char *
GENtostr(GEN x) { return GENtostr0(x, NULL, &gen_output); }

/* Returns gpmalloc()ed string */
char *
GENtoTeXstr(GEN x) {
  pariout_t T = *(GP_DATA->fmt);

  T.prettyp = f_TEX;
  T.fieldw = 0;
  return GENtostr0(x, &T, &gen_output);
}

/* see print0(). Returns gpmalloc()ed string */
char *
pGENtostr(GEN g, long flag) {
  pariout_t T = *(GP_DATA->fmt);
  pari_sp av = avma;
  char *t, *t2;
  long i, tlen = 0, l = lg(g);
  GEN Ls, Ll;

  T.prettyp = flag;
  /* frequent special case */
  if (l == 2) return GENtostr0(gel(g,1), &T, &gen_output);

  Ls = cgetg(l, t_VEC);
  Ll = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++)
  {
    char *s = GENtostr0(gel(g,i), &T, &gen_output);
    gel(Ls,i) = (GEN)s;
    Ll[i] = strlen(s);
    tlen += Ll[i];
  }
  t2 = t = (char*)gpmalloc(tlen + 1);
  *t = 0;
  for (i = 1; i < l; i++)
  {
    strcpy(t2, (char*)Ls[i]);
    t2 += Ll[i];
    gpfree((void*)Ls[i]);
  }
  avma = av; return t;
}
GEN Str0(GEN g, long flag) {
  char *t = pGENtostr(g, flag);
  GEN z = strtoGENstr(t);
  gpfree(t); return z;
}
GEN Str(GEN g)    { return Str0(g, f_RAW); }
GEN Strtex(GEN g) { return Str0(g, f_TEX); }
GEN
Strexpand(GEN g) {
  char *s = pGENtostr(g, f_RAW), *t = expand_tilde(s);
  GEN z = strtoGENstr(t);
  gpfree(t); gpfree(s); return z;
}

GEN
GENtoGENstr(GEN x)
{
  pariout_t T = *(GP_DATA->fmt);
  char *s;
  GEN z;
  T.prettyp = f_RAW;
  s = GENtostr0(x, &T, &gen_output);
  z = strtoGENstr(s); gpfree(s); return z;
}

GEN
GENtocanonicalstr(GEN x)
{
  pariout_t T = *(GP_DATA->fmt);
  char *s;
  GEN z;
  T.prettyp = f_RAW;
  T.sp = 0;
  s = GENtostr0(x, &T, &gen_output);
  z = strtoGENstr(s); gpfree(s); return z;
}

static char
ltoc(long n) {
  if (n <= 0 || n > 255)
    pari_err(talker, "out of range in integer -> character conversion (%ld)", n);
  return (char)n;
}
static char
itoc(GEN x) { return ltoc(gtos(x)); }

GEN
Strchr(GEN g)
{
  long i, l, len, t = typ(g);
  char *s;
  GEN x;
  if (is_vec_t(t)) {
    l = lg(g); len = nchar2nlong(l);
    x = cgetg(len+1, t_STR); s = GSTR(x);
    for (i=1; i<l; i++) *s++ = itoc(gel(g,i));
  }
  else if (t == t_VECSMALL)
  {
    l = lg(g); len = nchar2nlong(l);
    x = cgetg(len+1, t_STR); s = GSTR(x);
    for (i=1; i<l; i++) *s++ = ltoc(g[i]);
  }
  else
  {
    x = cgetg(2, t_STR); s = GSTR(x);
    *s++ = itoc(g);
  }
  *s = 0; return x;
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

static void
blancs(long nb) { while (nb-- > 0) pariputc(' '); }

char *
itostr(GEN x) {
  long sx = signe(x), l;
  return sx? itostr_sign(x, sx, &l): zerotostr();
}

/* x != 0 integer, write abs(x). Prepend '-' if (minus) */
static void
wr_int_sign(GEN x, int sx)
{
  pari_sp av = avma;
  long l;
  pariputs( itostr_sign(x, sx, &l) ); avma = av;
}

/* write integer. T->fieldw: field width (pad with ' ') */
static void
wr_int(pariout_t *T, GEN x, int addsign)
{
  long sx = signe(x), l;
  pari_sp av = avma;
  char *s;

  if (!sx) { blancs(T->fieldw - 1); pariputc('0'); return; }
  s = itostr_sign(x, addsign?sx:1, &l);
  blancs(T->fieldw - l);
  pariputs(s); avma = av;
}

static void
wr_vecsmall(pariout_t *T, GEN g)
{
  long i,l;
  pariputs("Vecsmall(["); l = lg(g);
  for (i=1; i<l; i++)
  {
    pariprintf("%ld", g[i]);
    if (i<l-1) comma_sp(T);
  }
  pariputs("])");
}

/********************************************************************/
/**                                                                **/
/**                       HEXADECIMAL OUTPUT                       **/
/**                                                                **/
/********************************************************************/
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

const char *
type_name(long t)
{
  const char *s;
  switch(t)
  {
    case t_INT    : s="t_INT";     break;
    case t_REAL   : s="t_REAL";    break;
    case t_INTMOD : s="t_INTMOD";  break;
    case t_FRAC   : s="t_FRAC";    break;
    case t_FFELT  : s="t_FFELT";   break;
    case t_COMPLEX: s="t_COMPLEX"; break;
    case t_PADIC  : s="t_PADIC";   break;
    case t_QUAD   : s="t_QUAD";    break;
    case t_POLMOD : s="t_POLMOD";  break;
    case t_POL    : s="t_POL";     break;
    case t_SER    : s="t_SER";     break;
    case t_RFRAC  : s="t_RFRAC";   break;
    case t_QFR    : s="t_QFR";     break;
    case t_QFI    : s="t_QFI";     break;
    case t_VEC    : s="t_VEC";     break;
    case t_COL    : s="t_COL";     break;
    case t_MAT    : s="t_MAT";     break;
    case t_LIST   : s="t_LIST";    break;
    case t_STR    : s="t_STR";     break;
    case t_VECSMALL:s="t_VECSMALL";break;
    case t_CLOSURE: s="t_CLOSURE"; break;
    default: pari_err(talker,"unknown type %ld",t);
      s = NULL; /* not reached */
  }
  return s;
}

static char
vsigne(GEN x)
{
  long s = signe(x);
  if (!s) return '0';
  return (s > 0) ? '+' : '-';
}

#ifndef LONG_IS_64BIT
#  define VOIR_STRING1 "[&=%08lx] "
#  define VOIR_STRING2 "%08lx  "
#else
#  define VOIR_STRING1 "[&=%016lx] "
#  define VOIR_STRING2 "%016lx  "
#endif

/* bl: indent level */
static void
dbg(GEN x, long nb, long bl)
{
  long tx,i,j,e,dx,lx;

  if (!x) { pariputs("NULL\n"); return; }
  tx = typ(x);
  if (tx == t_INT && x == gen_0) { pariputs("gen_0\n"); return; }
  pariprintf(VOIR_STRING1,(ulong)x);

  lx = lg(x);
  pariprintf("%s(lg=%ld%s):",type_name(tx)+2,lx,isclone(x)? ",CLONE" : "");
  pariprintf(VOIR_STRING2,x[0]);
  if (! is_recursive_t(tx)) /* t_INT, t_REAL, t_STR, t_VECSMALL */
  {
    if (tx == t_STR)
      pariputs("chars:");
    else if (tx == t_INT)
    {
      lx = lgefint(x);
      pariprintf("(%c,lgefint=%ld):", vsigne(x), lx);
    }
    else if (tx == t_REAL)
      pariprintf("(%c,expo=%ld):", vsigne(x), expo(x));
    if (nb < 0) nb = lx;
    for (i=1; i < nb; i++) pariprintf(VOIR_STRING2,x[i]);
    pariputc('\n'); return;
  }

  if (tx == t_PADIC)
    pariprintf("(precp=%ld,valp=%ld):", precp(x), valp(x));
  else if (tx == t_POL)
    pariprintf("(%c,varn=%ld):", vsigne(x), varn(x));
  else if (tx == t_SER)
    pariprintf("(%c,varn=%ld,prec=%ld,valp=%ld):",
	       vsigne(x), varn(x), lgpol(x), valp(x));
  else if (tx == t_LIST)
  {
    pariprintf("(lmax=%ld):", list_nmax(x));
    x = list_data(x); lx = x? lg(x): 1;
  } else if (tx == t_CLOSURE)
    pariprintf("(arity=%ld):", x[1]);
  for (i=1; i<lx; i++) pariprintf(VOIR_STRING2,x[i]);
  bl+=2; pariputc('\n');
  switch(tx)
  {
    case t_INTMOD: case t_POLMOD:
    {
      const char *s = (tx==t_INTMOD)? "int = ": "pol = ";
      blancs(bl);
      pariputs("mod = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pariputs(s);        dbg(gel(x,2),nb,bl);
      break;
    }
    case t_FRAC: case t_RFRAC:
      blancs(bl); pariputs("num = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pariputs("den = "); dbg(gel(x,2),nb,bl);
      break;

    case t_FFELT:
      blancs(bl); pariputs("pol = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pariputs("mod = "); dbg(gel(x,3),nb,bl);
      blancs(bl); pariputs("p   = "); dbg(gel(x,4),nb,bl);
      break;

    case t_COMPLEX:
      blancs(bl); pariputs("real = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pariputs("imag = "); dbg(gel(x,2),nb,bl);
      break;

    case t_PADIC:
      blancs(bl);
		  pariputs("  p : "); dbg(gel(x,2),nb,bl);
      blancs(bl); pariputs("p^l : "); dbg(gel(x,3),nb,bl);
      blancs(bl); pariputs("  I : "); dbg(gel(x,4),nb,bl);
      break;

    case t_QUAD:
      blancs(bl); pariputs("pol = ");  dbg(gel(x,1),nb,bl);
      blancs(bl); pariputs("real = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pariputs("imag = "); dbg(gel(x,3),nb,bl);
      break;

    case t_POL: case t_SER:
      e = (tx==t_SER)? valp(x): 0;
      for (i=2; i<lx; i++)
      {
	blancs(bl); pariprintf("coef of degree %ld = ",e);
	e++; dbg(gel(x,i),nb,bl);
      }
      break;

    case t_LIST:
      x = list_data(x); lx = x ? lg(x): 1;
    case t_QFR: case t_QFI: case t_VEC: case t_COL:
      for (i=1; i<lx; i++)
      {
	blancs(bl); pariprintf("%ld%s component = ",i,eng_ord(i));
	dbg(gel(x,i),nb,bl);
      }
      break;

    case t_CLOSURE:
      blancs(bl); pariputs("code = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pariputs("operand = "); dbg(gel(x,3),nb,bl);
      blancs(bl); pariputs("data = "); dbg(gel(x,4),nb,bl);
      if (lg(x)>=6)
      {
        blancs(bl); pariputs("text = "); dbg(gel(x,5),nb,bl);
        if (lg(x)>=7)
        {
          blancs(bl); pariputs("frame = "); dbg(gel(x,6),nb,bl);
        }
      }
      break;

    case t_MAT:
    {
      GEN c = gel(x,1);
      if (lx == 1) return;
      if (typ(c) == t_VECSMALL)
      {
	for (i = 1; i < lx; i++)
	{
	  blancs(bl); pariprintf("%ld%s column = ",i,eng_ord(i));
	  dbg(gel(x,i),nb,bl);
	}
      }
      else
      {
	dx = lg(c);
	for (i=1; i<dx; i++)
	  for (j=1; j<lx; j++)
	  {
	    blancs(bl); pariprintf("mat(%ld,%ld) = ",i,j);
	    dbg(gcoeff(x,i,j),nb,bl);
	  }
      }
    }
  }
}

void
dbgGEN(GEN x, long nb) { dbg(x,nb,0); }

static void
print_entree(entree *ep, long hash)
{
  pariprintf(" %s ",ep->name); pariprintf(VOIR_STRING1,(ulong)ep);
  pariprintf(":\n   hash = %3ld, menu = %2ld, code = %-10s",
	    hash, ep->menu, ep->code? ep->code: "NULL");
  if (ep->next)
  {
    pariprintf("next = %s ",(ep->next)->name);
    pariprintf(VOIR_STRING1,(ulong)(ep->next));
  }
  pariputs("\n");
}

/* s = digit n : list of entrees in functions_hash[n] (s = $: last entry)
 *   = range m-n: functions_hash[m..n]
 *   = identifier: entree for that identifier */
void
print_functions_hash(const char *s)
{
  long m, n, Max, Total;
  entree *ep;

  if (isdigit((int)*s) || *s == '$')
  {
    m = functions_tblsz-1; n = atol(s);
    if (*s=='$') n = m;
    if (m<n) pari_err(talker,"invalid range in print_functions_hash");
    while (isdigit((int)*s)) s++;

    if (*s++ != '-') m = n;
    else
    {
      if (*s !='$') m = min(atol(s),m);
      if (m<n) pari_err(talker,"invalid range in print_functions_hash");
    }

    for(; n<=m; n++)
    {
      pariprintf("*** hashcode = %lu\n",n);
      for (ep=functions_hash[n]; ep; ep=ep->next)
	print_entree(ep,n);
    }
    return;
  }
  if (is_keyword_char((int)*s))
  {
    ep = is_entry_intern(s,functions_hash,&n);
    if (!ep) pari_err(talker,"no such function");
    print_entree(ep,n); return;
  }
  if (*s=='-')
  {
    for (n=0; n<functions_tblsz; n++)
    {
      m=0;
      for (ep=functions_hash[n]; ep; ep=ep->next) m++;
      pariprintf("%3ld:%3ld ",n,m);
      if (n%9 == 8) pariputc('\n');
    }
    pariputc('\n'); return;
  }
  Max = Total = 0;
  for (n=0; n<functions_tblsz; n++)
  {
    long cnt = 0;
    for (ep=functions_hash[n]; ep; ep=ep->next)
    {
      print_entree(ep,n);
      cnt++;
    }
    Total += cnt;
    if (cnt > Max) Max = cnt;
  }
  pariprintf("Total: %ld, Max: %ld\n", Total, Max);
}

/********************************************************************/
/**                                                                **/
/**                        FORMATTED OUTPUT                        **/
/**                                                                **/
/********************************************************************/
/* forward declarations. Maybe these should be static ? */
void bruti(GEN g, pariout_t *T, int nosign);
void sori(GEN g, pariout_t *T);
void texi(GEN g, pariout_t *T, int nosign);

static const char *
get_var(long v, char *buf)
{
  entree *ep = varentries[v];

  if (ep) return (char*)ep->name;
  if (v==MAXVARN) return "#";
  sprintf(buf,"#<%d>",(int)v); return buf;
}

static void
do_append(char **sp, char c, char *last, int count)
{
  if (*sp + count > last)
    pari_err(talker, "TeX variable name too long");
  while (count--)
    *(*sp)++ = c;
}

static char *
get_texvar(long v, char *buf, unsigned int len)
{
  entree *ep = varentries[v];
  char *t = buf, *e = buf + len - 1;
  const char *s;

  if (!ep) pari_err(talker, "this object uses debugging variables");
  s = ep->name;
  if (strlen(s) >= len) pari_err(talker, "TeX variable name too long");
  while (isalpha((int)*s)) *t++ = *s++;
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

void
etatpile(void)
{
  long nu, l, u, s;
  pari_sp av = avma;
  GEN adr;
  double r;

  nu = (top-avma)/sizeof(long);
  l = (top-bot)/sizeof(long);
  r = 100.0*nu/l;
  pariprintf("\n Top : %lx   Bottom : %lx   Current stack : %lx\n",
	    top, bot, avma);

  pariprintf(" Used :                         %ld  long words  (%ld K)\n",
	    nu, nu/1024*sizeof(long));

  pariprintf(" Available :                    %ld  long words  (%ld K)\n",
	   (l-nu), (l-nu)/1024*sizeof(long));

  pariprintf(" Occupation of the PARI stack : %6.2f percent\n",r);

  adr = getheap();
  pariprintf(" %ld objects on heap occupy %ld long words\n\n",
	    itos(gel(adr,1)), itos(gel(adr,2)));
  avma = av;
  u = pari_var_next();
  s = MAXVARN - pari_var_next_temp();
  pariprintf(" %ld variable names used (%ld user + %ld private) out of %d\n\n",
	     u+s, u, s, MAXVARN);
}

#define isnull_for_pol(g)  ((typ(g)==t_INTMOD)? !signe(g[2]): isnull(g))

/* is to be printed as '0' */
static long
isnull(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_INT:
      return !signe(g);
    case t_COMPLEX:
      return isnull(gel(g,1)) && isnull(gel(g,2));
    case t_FFELT:
      return FF_cmp0(g);
    case t_QUAD:
      return isnull(gel(g,2)) && isnull(gel(g,3));
    case t_FRAC: case t_RFRAC:
      return isnull(gel(g,1));
    case t_POLMOD:
      return isnull(gel(g,2));
    case t_POL:
      for (i=lg(g)-1; i>1; i--)
	if (!isnull(gel(g,i))) return 0;
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
    case t_INT:
      return (signe(g) && is_pm1(g))? signe(g): 0;
    case t_COMPLEX:
      return isnull(gel(g,2))? isone(gel(g,1)): 0;
    case t_QUAD:
      return isnull(gel(g,3))? isone(gel(g,2)): 0;
    case t_FRAC: case t_RFRAC:
      return isone(gel(g,1)) * isone(gel(g,2));
    case t_POL:
      if (!signe(g)) return 0;
      for (i=lg(g)-1; i>2; i--)
	if (!isnull(gel(g,i))) return 0;
      return isone(gel(g,2));
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
    case t_FRAC: case t_RFRAC:
      return isfactor(gel(g,1));
    case t_FFELT:
      return isfactor(FF_to_FpXQ_i(g));
    case t_COMPLEX:
      if (isnull(gel(g,1))) return isfactor(gel(g,2));
      if (isnull(gel(g,2))) return isfactor(gel(g,1));
      return 0;
    case t_PADIC:
      return !signe(gel(g,4));
    case t_QUAD:
      if (isnull(gel(g,2))) return isfactor(gel(g,3));
      if (isnull(gel(g,3))) return isfactor(gel(g,2));
      return 0;
    case t_POL: deja = 0; sig = 1;
      for (i=lg(g)-1; i>1; i--)
	if (!isnull_for_pol(gel(g,i)))
	{
	  if (deja) return 0;
	  sig=isfactor(gel(g,i)); deja=1;
	}
      return sig? sig: 1;
    case t_SER:
      for (i=lg(g)-1; i>1; i--)
	if (!isnull(gel(g,i))) return 0;
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
    case t_FRAC: case t_RFRAC:
      return 0;
    case t_COMPLEX: return isnull(gel(g,2));
    case t_PADIC: return !signe(gel(g,4));
    case t_QUAD: return isnull(gel(g,3));

    case t_POL: deja = 0;
      for (i=lg(g)-1; i>1; i--)
	if (!isnull(gel(g,i)))
	{
	  if (deja) return 0;
	  if (i==2) return isdenom(gel(g,2));
	  if (!isone(gel(g,i))) return 0;
	  deja=1;
	}
      return 1;
    case t_SER:
      for (i=lg(g)-1; i>1; i--)
	if (!isnull(gel(g,i))) return 0;
  }
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                           RAW OUTPUT                           **/
/**                                                                **/
/********************************************************************/
/* ^e */
static void
texexpo(long e)
{
  if (e != 1) {
    if (e >= 0 && e < 10)
      pariprintf("^%ld",e);
    else
      pariprintf("^{%ld}",e);
  }
}
static void
wrexpo(long e)
{
  if (e != 1) pariprintf("^%ld",e);
}

/* v^e */
#define VpowE(v,e)    STMT_START {pariputs(v); wrexpo(e);}  STMT_END
#define texVpowE(v,e) STMT_START {pariputs(v); texexpo(e);} STMT_END
static void
monome(const char *v, long e)
{
  if (e) VpowE(v, e); else pariputc('1');
}
static void
texnome(const char *v, long e)
{
  if (e) texVpowE(v, e); else pariputc('1');
}

/* ( a ) */
static void
paren(pariout_t *T, GEN a)
{
  pariputc('('); bruti(a,T,1); pariputc(')');
}
static void
texparen(pariout_t *T, GEN a)
{
  if (T->TeXstyle & TEXSTYLE_PAREN) pariputs(" ("); else pariputs(" \\left(");
  texi(a,T,1);
  if (T->TeXstyle & TEXSTYLE_PAREN) pariputs(") "); else pariputs("\\right) ");
}

/* * v^d */
static void
times_texnome(const char *v, long d)
{
  if (d)
  {
    if (GP_DATA->flags & TEXMACS) pariputs("\\*");
    else pariputc(' ');
    texnome(v,d);
  }
}
static void
times_monome(const char *v, long d)
{
  if (d) { pariputc('*'); monome(v,d); }
}

/* write a * v^d */
static void
wr_monome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);

  if (sig) {
    sp_sign_sp(T,sig); monome(v,d);
  } else {
    sig = isfactor(a);
    if (sig) { sp_sign_sp(T,sig); bruti(a,T,0); }
    else { sp_sign_sp(T,1); paren(T, a); }
    times_monome(v, d);
  }
}
static void
wr_texnome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);

  pariputc('\n'); /* Avoid TeX buffer overflow */
  if (T->TeXstyle & TEXSTYLE_BREAK) pariputs("\\PARIbreak ");

  if (sig) {
    putsigne(sig); texnome(v,d);
  } else {
    sig = isfactor(a);
    if (sig) { putsigne(sig); texi(a,T,0); }
    else { pariputs(" +"); texparen(T, a); }
    times_texnome(v, d);
  }
}
static void
sor_monome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);
  if (sig) {
    putsigne(sig); monome(v,d);
  } else {
    sig = isfactor(a);
    if (sig) { putsigne(sig); if (sig < 0) a = gneg(a); }
    else pariputs(" + ");
    sori(a,T); if (d) { pariputc(' '); monome(v,d);}
  }
}

static void
wr_lead_monome(pariout_t *T, GEN a,const char *v, long d, int addsign)
{
  long sig = isone(a);
  if (sig) {
    if (addsign && sig<0) pariputc('-');
    monome(v,d);
  } else {
    if (isfactor(a)) bruti(a,T,addsign);
    else paren(T, a);
    times_monome(v, d);
  }
}
static void
wr_lead_texnome(pariout_t *T, GEN a,const char *v, long d, int addsign)
{
  long sig = isone(a);
  if (sig) {
    if (addsign && sig<0) pariputc('-');
    texnome(v,d);
  } else {
    if (isfactor(a)) texi(a,T,addsign);
    else texparen(T, a);
    times_texnome(v, d);
  }
}
static void
sor_lead_monome(pariout_t *T, GEN a, const char *v, long d)
{
  long sig = isone(a);
  if (sig) {
    if (sig < 0) pariputc('-');
    monome(v,d);
  } else {
    sori(a,T);
    if (d) { pariputc(' '); monome(v,d); }
  }
}

static void
prints(GEN g, pariout_t *T, int addsign)
{
  (void)T; (void)addsign;
  pariprintf("%ld", (long)g);
}
static void
sors(GEN g, pariout_t *T)
{
  (void)T;
  pariprintf("%ld", (long)g);
}

static void
quote_string(char *s)
{
  pariputc('"');
  while (*s)
  {
    char c=*s++;
    if (c=='\\' || c=='"' || c=='\033' || c=='\n' || c=='\t')
    {
      pariputc('\\');
      switch(c)
      {
      case '\\': case '"': break;
      case '\n':   c='n'; break;
      case '\033': c='e'; break;
      case '\t':   c='t'; break;
      }
    }
    pariputc(c);
  }
  pariputc('"');
}

static int
print_0_or_pm1(GEN g, int addsign)
{
  long r;
  if (!g) { pariputs("NULL"); return 1; }
  if (isnull(g)) { pariputc('0'); return 1; }
  r = isone(g);
  if (r)
  {
    if (addsign && r<0) pariputc('-');
    pariputc('1'); return 1;
  }
  return 0;
}

static void
bruti_intern(GEN g, pariout_t *T, int addsign)
{
  long l,i,j,r, tg = typ(g);
  GEN a,b;
  const char *v;
  char buf[32];

  switch(tg)
  {
    case t_INT: wr_int_sign(g, addsign?signe(g):1); break;
    case t_REAL:
    {
      pari_sp av = avma;
      if (addsign && signe(g) < 0) pariputc('-');
      pariputs( absrtostr(g, T->sp, toupper(T->format), T->sigd, -1) );
      avma = av; break;
    }

    case t_INTMOD: case t_POLMOD:
      pariputs(new_fun_set? "Mod(": "mod(");
      bruti(gel(g,2),T,1); comma_sp(T);
      bruti(gel(g,1),T,1); pariputc(')'); break;

    case t_FFELT:
      bruti(FF_to_FpXQ_i(g),T,addsign);
      break;

    case t_FRAC: case t_RFRAC:
      r = isfactor(gel(g,1)); if (!r) pariputc('(');
      bruti(gel(g,1),T,addsign);
      if (!r) pariputc(')');
      pariputc('/');
      r = isdenom(gel(g,2)); if (!r) pariputc('(');
      bruti(gel(g,2),T,1);
      if (!r) pariputc(')');
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = gel(g,r+1); b = gel(g,r+2); v = r? "w": "I";
      if (isnull(a))
      {
	wr_lead_monome(T,b,v,1,addsign);
	return;
      }
      bruti(a,T,addsign);
      if (!isnull(b)) wr_monome(T,b,v,1);
      break;

    case t_POL: v = get_var(varn(g), buf);
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      wr_lead_monome(T,gel(g,i),v,i,addsign);
      while (i--)
      {
	a = gel(g,i);
	if (!isnull_for_pol(a)) wr_monome(T,a,v,i);
      }
      break;

    case t_SER: v = get_var(varn(g), buf);
      i = valp(g);
      if (lgpol(g))
      { /* hack: we want g[i] = coeff of degree i. */
	l = i + lgpol(g); g -= i-2;
	wr_lead_monome(T,gel(g,i),v,i,addsign);
	while (++i < l)
	{
	  a = gel(g,i);
	  if (!isnull_for_pol(a)) wr_monome(T,a,v,i);
	}
	sp_sign_sp(T,1);
      }
      pariputs("O("); monome(v,i); pariputc(')'); break;

    case t_PADIC:
    {
      GEN p = gel(g,2);
      pari_sp av = avma;
      char *ev;
      i = valp(g); l = precp(g)+i;
      g = gel(g,4); ev = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int_sign(a, 1); if (i) pariputc('*');
	  }
	  if (i) VpowE(ev,i);
	  sp_sign_sp(T,1);
	}
	if ((i & 0xff) == 0) g = gerepileuptoint(av,g);
      }
      pariputs("O("); VpowE(ev,i); pariputc(')');
      gpfree(ev); break;
    }

    case t_QFR: case t_QFI: r = (tg == t_QFR);
      if (new_fun_set) pariputs("Qfb("); else pariputs(r? "qfr(": "qfi(");
      bruti(gel(g,1),T,1); comma_sp(T);
      bruti(gel(g,2),T,1); comma_sp(T);
      bruti(gel(g,3),T,1);
      if (r) { comma_sp(T); bruti(gel(g,4),T,1); }
      pariputc(')'); break;

    case t_VEC: case t_COL:
      pariputc('['); l = lg(g);
      for (i=1; i<l; i++)
      {
	bruti(gel(g,i),T,1);
	if (i<l-1) comma_sp(T);
      }
      pariputc(']'); if (tg==t_COL) pariputc('~');
      break;
    case t_VECSMALL: wr_vecsmall(T,g); break;

    case t_LIST:
      pariputs("List([");
      g = list_data(g);
      l = g? lg(g): 1;
      for (i=1; i<l; i++)
      {
	bruti(gel(g,i),T,1);
	if (i<l-1) comma_sp(T);
      }
      pariputs("])"); break;

    case t_STR:
      quote_string(GSTR(g)); break;

    case t_CLOSURE:
      if (lg(g)>=6)
      {
        if (typ(g[5])==t_STR)
          pariputs(GSTR(gel(g,5)));
        else
          pariprintf("(%s)->%s",GSTR(gmael(g,5,1)),GSTR(gmael(g,5,2)));
      }
      else
        pariprintf("{\"%s\",%Z,%Z}",GSTR(gel(g,2)),gel(g,3),gel(g,4));
      break;

    case t_MAT:
    {
      void (*print)(GEN, pariout_t *, int);
      r = lg(g); if (r==1) { pariputs("[;]"); return; }
      l = lg(g[1]);
      if (l==1)
      {
	pariprintf(new_fun_set? "matrix(0,%ld)":"matrix(0,%ld,j,k,0)", r-1);
	return;
      }
      print = (typ(g[1]) == t_VECSMALL)? prints: bruti;
      if (l==2)
      {
	pariputs(new_fun_set? "Mat(": "mat(");
	if (r == 2) { print(gcoeff(g,1,1),T,1); pariputc(')'); return; }
      }
      pariputc('[');
      for (i=1; i<l; i++)
      {
	for (j=1; j<r; j++)
	{
	  print(gcoeff(g,i,j),T,1);
	  if (j<r-1) comma_sp(T);
	}
	if (i<l-1) { pariputc(';'); if (T->sp) pariputc(' '); }
      }
      pariputc(']'); if (l==2) pariputc(')');
      break;
    }

    default: pariprintf(VOIR_STRING2,*g);
  }
}

void
bruti(GEN g, pariout_t *T, int addsign)
{
  if (!print_0_or_pm1(g, addsign))
    bruti_intern(g, T, addsign);
}

void
matbruti(GEN g, pariout_t *T)
{
  long i, j, r, l;
  void (*print)(GEN, pariout_t *, int);

  if (typ(g) != t_MAT) { bruti(g,T,1); return; }

  r=lg(g); if (r==1 || lg(g[1])==1) { pariputs("[;]\n"); return; }
  l = lg(g[1]); pariputc('\n');
  print = (typ(g[1]) == t_VECSMALL)? prints: bruti;
  for (i=1; i<l; i++)
  {
    pariputc('[');
    for (j=1; j<r; j++)
    {
      print(gcoeff(g,i,j),T,1); if (j<r-1) pariputc(' ');
    }
    if (i<l-1) pariputs("]\n\n"); else pariputs("]\n");
  }
}

void
sori(GEN g, pariout_t *T)
{
  long tg=typ(g), i,j,r,l,close_paren;
  GEN a,b;
  const char *v;
  char buf[32];

  if (tg == t_INT) { wr_int(T,g,1); return; }
  if (tg != t_MAT && tg != t_COL) T->fieldw = 0;
  switch (tg)
  {
    case t_REAL: case t_STR: case t_CLOSURE:
      bruti_intern(g, T, 1); return;
    case t_FFELT:
      sori(FF_to_FpXQ_i(g),T); return;
    case t_LIST:
      pariputs("List([");
      g = list_data(g);
      l = g? lg(g): 1;
      for (i=1; i<l; i++)
      {
	sori(gel(g,i), T); if (i < l-1) pariputs(", ");
      }
      pariputs("])\n"); return;
  }
  close_paren = 0;
  if (!is_graphicvec_t(tg))
  {
    if (tg == t_FRAC && gsigne(g) < 0) pariputc('-');
    pariputc('('); close_paren = 1;
  }
  switch(tg)
  {
    case t_INTMOD: case t_POLMOD:
      a = gel(g,2); b = gel(g,1);
      if (tg == t_INTMOD && signe(a) < 0) a = addii(a,b);
      sori(a,T); pariputs(" mod "); sori(b,T); break;

    case t_FRAC:
      a=gel(g,1); wr_int(T,a,0); pariputs(" /");
      b=gel(g,2); wr_int(T,b,0); break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = gel(g,r+1); b = gel(g,r+2); v = r? "w": "I";
      if (isnull(a)) { sor_lead_monome(T,b,v,1); break; }
      sori(a,T); if (!isnull(b)) sor_monome(T,b,v,1);
      break;

    case t_PADIC:
    {
      GEN p = gel(g,2);
      char *ev;
      i = valp(g); l = precp(g)+i;
      g = gel(g,4); ev = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int(T,a,1); pariputc(i? '*': ' ');
	  }
	  if (i) { VpowE(ev,i); pariputc(' '); }
	  pariputs("+ ");
	}
      }
      pariputs("O(");
      if (!i) pariputs(" 1)"); else VpowE(ev,i);
      pariputc(')'); gpfree(ev); break;
    }

    case t_POL:
      if (!signe(g)) { pariputc('0'); break; }
      v = get_var(varn(g),buf);
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      sor_lead_monome(T,gel(g,i),v,i);
      while (i--)
      {
	a = gel(g,i); if (!isnull_for_pol(a)) sor_monome(T,a,v,i);
      }
      break;

    case t_SER: v = get_var(varn(g),buf);
      i = valp(g);
      if (lgpol(g))
      { /* hack: we want g[i] = coeff of degree i. */
	l = i + lgpol(g); g -= i-2;
	sor_lead_monome(T,gel(g,i),v,i);
	while (++i < l)
	{
	  a = gel(g,i); if (!isnull_for_pol(a)) sor_monome(T,a,v,i);
	}
	pariputs(" + ");
      }
      pariputs("O(");
      if (!i) pariputs(" 1)"); else monome(v,i);
      pariputc(')'); break;

    case t_RFRAC:
      sori(gel(g,1),T); pariputs(" / "); sori(gel(g,2),T);
      break;

    case t_QFR: case t_QFI: pariputc('{');
      sori(gel(g,1),T); pariputs(", ");
      sori(gel(g,2),T); pariputs(", ");
      sori(gel(g,3),T);
      if (tg == t_QFR) { pariputs(", "); sori(gel(g,4),T); }
      pariputs("}\n"); break;

    case t_VEC: pariputc('[');
      for (i=1; i<lg(g); i++)
      {
	sori(gel(g,i),T); if (i<lg(g)-1) pariputs(", ");
      }
      pariputc(']'); break;
    case t_VECSMALL: wr_vecsmall(T,g); break;

    case t_COL:
      if (lg(g)==1) { pariputs("[]\n"); return; }
      pariputc('\n');
      for (i=1; i<lg(g); i++)
      {
	pariputc('['); sori(gel(g,i),T); pariputs("]\n");
      }
      break;

    case t_MAT:
    {
      void (*print)(GEN, pariout_t *);
      long lx = lg(g);

      if (lx==1 || lg(g[1]) == 1) { pariputs("[;]\n"); return; }
      l = lg(g[1]); pariputc('\n');
      print = (typ(g[1]) == t_VECSMALL)? sors: sori;
      for (i=1; i<l; i++)
      {
	pariputc('[');
	for (j=1; j<lx; j++)
	{
	  print(gcoeff(g,i,j),T); if (j<lx-1) pariputc(' ');
	}
	pariputs("]\n"); if (i<l-1) pariputc('\n');
      }
      break;
    }
    default: pariprintf(VOIR_STRING2,*g);
  }
  if (close_paren) pariputc(')');
}

/********************************************************************/
/**                                                                **/
/**                           TeX OUTPUT                           **/
/**                                                                **/
/********************************************************************/
/* this follows bruti */
void
texi(GEN g, pariout_t *T, int addsign)
{
  long tg,i,j,l,r;
  GEN a,b;
  const char *v;
  char buf[67];

  if (print_0_or_pm1(g, addsign)) return;

  tg = typ(g);
  switch(tg)
  {
    case t_INT: case t_REAL: case t_QFR: case t_QFI:
      bruti_intern(g, T, addsign); break;

    case t_INTMOD: case t_POLMOD:
      texi(gel(g,2),T,1); pariputs(" mod ");
      texi(gel(g,1),T,1); break;

    case t_FRAC:
      if (addsign && isfactor(gel(g,1)) < 0) pariputc('-');
      pariputs("\\frac{");
      texi(gel(g,1),T,0);
      pariputs("}{");
      texi(gel(g,2),T,0);
      pariputs("}"); break;

    case t_RFRAC:
      pariputs("\\frac{");
      texi(gel(g,1),T,1); /* too complicated otherwise */
      pariputs("}{");
      texi(gel(g,2),T,1);
      pariputs("}"); break;

    case t_FFELT:
      bruti(FF_to_FpXQ_i(g),T,addsign);
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = gel(g,r+1); b = gel(g,r+2); v = r? "w": "I";
      if (isnull(a))
      {
	wr_lead_texnome(T,b,v,1,addsign);
	break;
      }
      texi(a,T,addsign);
      if (!isnull(b)) wr_texnome(T,b,v,1);
      break;

    case t_POL: v = get_texvar(varn(g), buf, sizeof(buf));
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      wr_lead_texnome(T,gel(g,i),v,i,addsign);
      while (i--)
      {
	a = gel(g,i);
	if (!isnull_for_pol(a)) wr_texnome(T,a,v,i);
      }
      break;

    case t_SER: v = get_texvar(varn(g), buf, sizeof(buf));
      i = valp(g);
      if (lgpol(g))
      { /* hack: we want g[i] = coeff of degree i. */
	l = i + lgpol(g); g -= i-2;
	wr_lead_texnome(T,gel(g,i),v,i,addsign);
	while (++i < l)
	{
	  a = gel(g,i);
	  if (!isnull_for_pol(a)) wr_texnome(T,a,v,i);
	}
	pariputs("+ ");
      }
      pariputs("O("); texnome(v,i); pariputc(')'); break;

    case t_PADIC:
    {
      GEN p = gel(g,2);
      char *ev;
      i = valp(g); l = precp(g)+i;
      g = gel(g,4); ev = GENtostr(p);
      for (; i<l; i++)
      {
	g = dvmdii(g,p,&a);
	if (signe(a))
	{
	  if (!i || !is_pm1(a))
	  {
	    wr_int_sign(a, 1); if (i) pariputs("\\cdot");
	  }
	  if (i) texVpowE(ev,i);
	  pariputc('+');
	}
      }
      pariputs("O("); texVpowE(ev,i); pariputc(')');
      gpfree(ev); break;
    }

    case t_VEC:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi(gel(g,i),T,1); if (i < l-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_LIST:
      pariputs("\\pmatrix{ ");
      g = list_data(g);
      l = g? lg(g): 1;
      for (i=1; i<l; i++)
      {
	texi(gel(g,i),T,1); if (i < l-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_COL:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi(gel(g,i),T,1); pariputs("\\cr\n");
      }
      pariputc('}'); break;

    case t_VECSMALL:
      pariputs("\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	pariprintf("%ld", g[i]);
	if (i < l-1) pariputc('&');
      }
      pariputs("\\cr}\n"); break;

    case t_STR:
    {
#if 0 /* This makes it impossible to print reliably. What it I want to
	 printtex("$$", x, "$$") ? */
      char *s = GSTR(g);
      pariputs("\\hbox{");
      while (*s) {
	if (strchr("\\{}$_^%#&~", *s)) pariputc('\\');
	pariputc(*s);
	if (strchr("^~", *s++)) pariputs("{}");
      }
      pariputc('}'); break;
#else
      pariputs(GSTR(g)); break;
#endif
    }

    case t_CLOSURE:
      if (lg(g)>=6)
      {
        if (typ(g[5])==t_STR)
          pariputs(GSTR(gel(g,5)));
        else
          pariprintf("(%s)\\mapsto %s",GSTR(gmael(g,5,1)),GSTR(gmael(g,5,2)));
      }
      else
        pariprintf("\\{\"%s\",%Z,%Z\\}",GSTR(gel(g,2)),gel(g,3),gel(g,4));
      break;

    case t_MAT:
    {
      void (*print)(GEN, pariout_t *, int);

      pariputs("\\pmatrix{\n "); r = lg(g);
      if (r>1)
      {
	print = (typ(g[1]) == t_VECSMALL)? prints: texi;
	l = lg(g[1]);
	for (i=1; i<l; i++)
	{
	  for (j=1; j<r; j++)
	  {
	    print(gcoeff(g,i,j),T,1); if (j<r-1) pariputc('&');
	  }
	  pariputs("\\cr\n ");
	}
      }
      pariputc('}'); break;
    }
  }
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
  if (!T) T = GP_DATA->fmt;
  switch(T->prettyp)
  {
    case f_PRETTYMAT: matbruti(x, T); break;
    case f_PRETTY:
    case f_PRETTYOLD: sori(x, T); break;
    case f_RAW      : bruti(x, T, 1); break;
    case f_TEX      : texi(x, T, 1); break;
  }
  avma = av;
}

void
brute(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,0,0, f_RAW);
  gen_output(g, &T);
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
outbrute(GEN g) { brute(g,'g',-1); }

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
bruterr(GEN x,char format,long sigd)
{
  PariOUT *out = pariOut; pariOut = pariErr;
  brute(x,format,sigd); pariOut = out;
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
/* to cache '~' expansion */
static char *homedir = NULL;
/* last file read successfully from try_name() */
static char *last_filename = NULL;
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
newfile(FILE *f, const char *name, int type)
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
    fprintferr("I/O: new pariFILE %s (code %d) \n",name,type);
  return file;
}

static void
pari_kill_file(pariFILE *f)
{
  if ((f->type & mf_PIPE) == 0)
  {
    if (fclose(f->file)) pari_warn(warnfile, "close", f->name);
  }
#ifdef HAVE_PIPES
  else
  {
    if (f->type & mf_FALSE)
    {
      if (fclose(f->file)) pari_warn(warnfile, "close", f->name);
      if (unlink(f->name)) pari_warn(warnfile, "delete", f->name);
    }
    else
      if (pclose(f->file) < 0) pari_warn(warnfile, "close pipe", f->name);
  }
#endif
  if (DEBUGFILES)
    fprintferr("I/O: closing file %s (code %d) \n",f->name,f->type);
  gpfree(f);
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
pari_open_file(FILE *f, const char *s, const char *mode)
{
  if (!f) pari_err(talker, "could not open requested file %s", s);
  if (DEBUGFILES)
    fprintferr("I/O: opening file %s (mode %s)\n", s, mode);
  return newfile(f,s,0);
}

pariFILE *
pari_fopen(const char *s, const char *mode)
{
  return pari_open_file(fopen(s, mode), s, mode);
}

#ifdef UNIX
/* open tmpfile s (a priori for writing) avoiding symlink attacks */
pariFILE *
pari_safefopen(const char *s, const char *mode)
{
  long fd = open(s, O_CREAT|O_EXCL|O_RDWR, S_IRUSR|S_IWUSR);

  if (fd == -1) pari_err(talker,"tempfile %s already exists",s);
  return pari_open_file(fdopen(fd, mode), s, mode);
}
#else
pariFILE *
pari_safefopen(const char *s, const char *mode)
{
  return pari_fopen(s, mode);
}
#endif

void
pari_unlink(const char *s)
{
  if (unlink(s)) pari_warn(warner, "I/O: can\'t remove file %s", s);
  else if (DEBUGFILES)
    fprintferr("I/O: removed file %s\n", s);
}

void
check_filtre(filtre_t *T)
{
  if (T && T->in_string)
  {
    pari_warn(warner,"run-away string. Closing it");
    T->in_string = 0;
  }
  if (T && T->in_comment)
  {
    pari_warn(warner,"run-away comment. Closing it");
    T->in_comment = 0;
  }
}

/* Remove one INFILE from the stack. Reset pari_infile (to the most recent pari_infile)
 * Return -1, if we're trying to pop out stdin itself; 0 otherwise
 * Check for leaked file handlers (temporary files)
 */
int
popinfile(void)
{
  pariFILE *f;
  for (f = last_tmp_file; f; f = f->prev)
  {
    if (f->type & mf_IN) break;
    pari_warn(warner, "I/O: leaked file descriptor (%d): %s",
		f->type, f->name);
    pari_fclose(f);
  }
  last_tmp_file = f; if (!last_tmp_file) return -1;
  pari_fclose(last_tmp_file);
  for (f = last_tmp_file; f; f = f->prev)
    if (f->type & mf_IN) { pari_infile = f->file; return 0; }
  pari_infile = stdin; return 0;
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
    if (last_filename) gpfree(last_filename);
    if (homedir) gpfree(homedir);
    if (pari_logfile) { fclose(pari_logfile); pari_logfile = NULL; }
  }
  kill_file_stack(&last_tmp_file);
  pari_infile = stdin;
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
try_pipe(const char *cmd, int fl)
{
#ifndef HAVE_PIPES
  pari_err(archer); return NULL;
#else
  FILE *file;
  const char *f;
  VOLATILE int flag = fl;

#  ifdef __EMX__
  if (_osmode == DOS_MODE) /* no pipes under DOS */
  {
    pari_sp av = avma;
    char *s;
    if (flag & mf_OUT) pari_err(archer);
    f = pari_unique_filename("pipe");
    s = stackmalloc(strlen(cmd)+strlen(f)+4);
    sprintf(s,"%s > %s",cmd,f);
    file = system(s)? NULL: fopen(f,"r");
    flag |= mf_FALSE; gpfree(f); avma = av;
  }
  else
#  endif
  {
    file = (FILE *) popen(cmd, (flag & mf_OUT)? "w": "r");
    if (flag & mf_OUT) {
      if (!ok_pipe(file)) return NULL;
      flag |= mf_PERM;
    }
    f = cmd;
  }
  if (!file) pari_err(talker,"[pipe:] '%s' failed",cmd);
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
typedef void (*pari_sighandler_t)(int);

pari_sighandler_t
os_signal(int sig, pari_sighandler_t f)
{
#ifdef HAS_SIGACTION
  struct sigaction sa, oldsa;

  sa.sa_handler = f;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_NODEFER;

  if (sigaction(sig, &sa, &oldsa)) return NULL;
  return oldsa.sa_handler;
#elif defined(WINCE)
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
os_open(const char *s, int mode)
{
  long fd;
#ifdef WINCE
  HANDLE h;
  short ws[256];
  if (mode != O_RDONLY) pari_err(impl,"generic open for Windows");
  MultiByteToWideChar(CP_ACP, 0, s, strlen(s)+1, ws, 256);
  h = CreateFile(ws,GENERIC_READ,FILE_SHARE_READ,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);
  fd = (h == INVALID_HANDLE_VALUE)? (long)-1: (long)h;
#else
  fd = open(s,mode);
#endif
  return fd;
}

char *
os_getenv(const char *s)
{
#ifdef HAS_GETENV
  return getenv(s);
#else
  return NULL;
#endif
}

/*******************************************************************/
/**                                                               **/
/**                   GP STANDARD INPUT AND OUTPUT                **/
/**                                                               **/
/*******************************************************************/
#ifdef HAS_OPENDIR
/* slow, but more portable than stat + S_ISDIR */
#  include <dirent.h>
static int
is_dir_opendir(const char *name)
{
  DIR *d = opendir(name);
  if (d) { (void)closedir(d); return 1; }
  return 0;
}
#endif

#ifdef HAS_STAT
#include <sys/stat.h>
static int
is_dir_stat(const char *name)
{
  struct stat buf;
  if (stat(name, &buf)) return 0;
  return S_ISDIR(buf.st_mode);
}
#endif

/* Does name point to a directory? */
int
pari_is_dir(const char *name)
{
#ifdef HAS_STAT
  return is_dir_stat(name);
#else
#  ifdef HAS_OPENDIR
  return is_dir_opendir(name);
#  else
  return 0;
#  endif
#endif
}

/* Does name point to a regular file? */
/* If unknown, assume that it is indeed regular. */
int
pari_is_file(const char *name)
{
#ifdef HAS_STAT
  struct stat buf;
  if (stat(name, &buf)) return 1;
  return S_ISREG(buf.st_mode);
#else
  return 1;
#endif
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
  char *ret, *dir = NULL, *user = NULL;
  int len;

  if (*s != '~') return pari_strdup(s);
  s++; u = s; /* skip ~ */
  if (!*s || *s == '/')
  {
    if (homedir) dir = homedir;
    else
    {
      p = getpwuid(geteuid());
      if (p)
      {
        dir = p->pw_dir;
        homedir = pari_strdup(dir);
      }
    }
  }
  else
  {
    while (*u && *u != '/') u++;
    len = u-s; user = (char*)gpmalloc(len+1);
    (void)strncpy(user,s,len);
    user[len] = 0;
    p = getpwnam(user);
    if (p) dir = p->pw_dir;
  }
  if (!dir)
  { /* don't kill session on startup (when expanding path) */
    pari_warn(warner,"can't expand ~%s", user? user: "");
    ret =  pari_strdup(s);
  }
  else
  {
    ret = (char*)gpmalloc(strlen(dir) + strlen(u) + 1);
    sprintf(ret,"%s%s",dir,u);
  }
  if (user) free(user);
  return ret;
#endif
}

/* expand environment variables in str, return a malloc'ed buffer
 * assume no \ remain and str can be freed */
static char *
_expand_env(char *str)
{
  long i, l, len = 0, xlen = 16, xnum = 0;
  char *s = str, *s0 = s, *env;
  char **x = (char **)gpmalloc(xlen * sizeof(char*));

  while (*s)
  {
    if (*s != '$') { s++; continue; }
    l = s - s0;
    if (l)
    {
      s0 = strncpy((char*)gpmalloc(l+1), s0, l); s0[l] = 0;
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
    env = strncpy((char*)gpmalloc(l+1), s0, l); env[l] = 0;
    s0 = os_getenv(env);
    if (!s0)
    {
      pari_warn(warner,"undefined environment variable: %s",env);
      s0 = (char*)"";
    }
    l = strlen(s0);
    if (l)
    {
      s0 = strncpy((char*)gpmalloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    gpfree(env); s0 = s;
  }
  l = s - s0;
  if (l)
  {
    s0 = strncpy((char*)gpmalloc(l+1), s0, l); s0[l] = 0;
    x[xnum++] = s0; len += l;
  }

  s = (char*)gpmalloc(len+1); *s = 0;
  for (i = 0; i < xnum; i++) { (void)strcat(s, x[i]); gpfree(x[i]); }
  gpfree(str); gpfree(x); return s;
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
    for (dirs = v; *dirs; dirs++) gpfree(*dirs);
    gpfree(v);
  }
}

#if defined(__EMX__) || defined(_WIN32) || defined(__CYGWIN32__)
#  define PATH_SEPARATOR ';' /* beware DOSish 'C:' disk drives */
#else
#  define PATH_SEPARATOR ':'
#endif

const char *
pari_default_path(void) {
#if PATH_SEPARATOR == ';'
  return ".;C:;C:/gp";
#elif defined(UNIX)
  return ".:~:~/gp";
#else
  return ".";
#endif
}

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
  gpfree((void*)v);
  dirs[i] = NULL; p->dirs = dirs;
}

/* name is a malloc'ed (existing) filename. Accept it as new pari_infile
 * (unzip if needed). */
static pariFILE *
pari_get_infile(char *name, FILE *file)
{
#ifdef ZCAT
  long l = strlen(name);
  char *end = name + l-1;

  if (l > 2 && (!strncmp(end-1,".Z",2)
#ifdef GNUZCAT
	     || !strncmp(end-2,".gz",3)
#endif
  ))
  { /* compressed file (compress or gzip) */
    char *cmd = stackmalloc(strlen(ZCAT) + l + 2);
    sprintf(cmd,"%s \"%s\"",ZCAT,name);
    fclose(file);
    return try_pipe(cmd, mf_IN);
  }
#endif
  return newfile(file, name, mf_IN);
}

/* input s must have 'alloc size' >= strlen(s) + 3 (to append .gz) */
pariFILE *
pari_fopengz(char *s)
{
  FILE *f = fopen(s, "r");
  if (!f) { (void)sprintf(s + strlen(s), ".gz"); f = fopen(s, "r"); }
  return f ? pari_get_infile(s, f): NULL;
}

static FILE*
try_open(char *s)
{
  if (!pari_is_dir(s)) return fopen(s, "r");
  pari_warn(warner,"skipping directory %s",s);
  return NULL;
}

/* If a file called "name" exists (possibly after appending ".gp")
 * record it in the file_stack (as a pipe if compressed).
 * name is malloc'ed, we free it before returning
 */
static FILE *
try_name(char *name)
{
  pari_sp av = avma;
  char *s = name;
  FILE *file = try_open(name);

  if (!file)
  { /* try appending ".gp" to name */
    s = stackmalloc(strlen(name)+4);
    sprintf(s, "%s.gp", name);
    file = try_open(s);
  }
  if (file)
  {
    if (! last_tmp_file)
    {  /* empty file stack, record this name */
      if (last_filename) gpfree(last_filename);
      last_filename = pari_strdup(s);
    }
    file = pari_infile = pari_get_infile(s,file)->file;
  }
  gpfree(name); avma = av;
  return file;
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
      pari_err(talker,"You never gave me anything to read!");
    name0 = last_filename;
    name = pari_strdup(name0);
  }
  /* if name contains '/',  don't use dir_list */
  s=name; while (*s && *s != '/' && *s != '\\') s++;
  if (*s) { if (try_name(name)) return; }
  else
  {
    char **tmp = GP_DATA->path->dirs;
    for ( ; *tmp; tmp++)
    { /* make room for '/' and '\0', try_name frees it */
      s = (char*)gpmalloc(2 + strlen(*tmp) + strlen(name));
      sprintf(s,"%s/%s",*tmp,name);
      if (try_name(s)) return;
    }
  }
  pari_err(openfiler,"input",name0);
}

static int is_magic_ok(FILE *f);

void
switchout(const char *name)
{
  if (name)
  {
    FILE* f;

    /* Only do the read-check for ordinary files
     * (to avoid blocking on pipes for example). */
    if (pari_is_file(name))
    {
      f = fopen(name, "r");
      if (f)
      {
        if (is_magic_ok(f))
	  pari_err(talker,"%s is a GP binary file. Please use writebin", name);
        fclose(f);
      }
    }
    f = fopen(name, "a");
    if (!f) pari_err(openfiler,"output",name);
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
  if (fwrite((a),(b),(c),(d)) < (c)) pari_err(talker,"write failed")
#define _fread(a,b,c,d) \
  if (fread((a),(b),(c),(d)) < (c)) pari_err(talker,"read failed")
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
  GENbin *p = copy_bin_canon(x);
  size_t L = p->len;

  wr_long(L,f);
  if (L)
  {
    wr_long((long)p->x,f);
    wr_long((long)p->base,f);
    _lfwrite(GENbase(p), L,f);
  }
  gpfree((void*)p);
}

static void
wrstr(const char *s, FILE *f)
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
  s = (char*)gpmalloc(L);
  _cfread(s, L, f); return s;
}

void
writeGEN(GEN x, FILE *f)
{
  fputc(BIN_GEN,f);
  wrGEN(x, f);
}

void
writenamedGEN(GEN x, const char *s, FILE *f)
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

  if (!L) return gen_0;
  p = (GENbin*)gpmalloc(sizeof(GENbin) + L*sizeof(long));
  p->len  = L;
  p->x    = (GEN)rd_long(f);
  p->base = (GEN)rd_long(f);
  p->canon= 1;
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
      break;
    case NAM_GEN:
    {
      char *s = rdstr(f);
      if (!s) pari_err(talker,"malformed binary file (no name)");
      x = rdGEN(f);
      fprintferr("setting %s\n",s);
      changevalue(fetch_named_var(s), x);
      break;
    }
    case EOF: break;
    default: pari_err(talker,"unknown code in readobj");
  }
  *ptc = c; return x;
}

#define MAGIC "\020\001\022\011-\007\020" /* ^P^A^R^I-^G^P */
#ifdef LONG_IS_64BIT
#  define ENDIAN_CHECK 0x0102030405060708L
#else
#  define ENDIAN_CHECK 0x01020304L
#endif
static const long BINARY_VERSION = 1; /* since 2.2.9 */

static int
is_magic_ok(FILE *f)
{
  pari_sp av = avma;
  size_t L = strlen(MAGIC);
  char *s = stackmalloc(L);
  int r = (fread(s,1,L, f) == L && strncmp(s,MAGIC,L) == 0);
  avma = av; return r;
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
    pari_err(talker, "%s is not a GP binary file",name);
  if (!is_sizeoflong_ok(f))
    pari_err(talker, "%s not written for a %ld bit architecture",
	       name, sizeof(long)*8);
  if (!is_long_ok(f, ENDIAN_CHECK))
    pari_err(talker, "unexpected endianness in %s",name);
  if (!is_long_ok(f, BINARY_VERSION))
    pari_err(talker, "%s written by an incompatible version of GP",name);
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
writebin(const char *name, GEN x)
{
  FILE *f = fopen(name,"r");
  int already = f? 1: 0;

  if (f) { check_magic(name,f); fclose(f); }
  f = fopen(name,"a");
  if (!f) pari_err(openfiler,"binary output",name);
  if (!already) write_magic(f);

  if (x) writeGEN(x,f);
  else
  {
    long v, maxv = pari_var_next();
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
 * them all in a vector and set 'vector'. */
GEN
readbin(const char *name, FILE *f, int *vector)
{
  pari_sp av = avma;
  GEN x,y,z;
  int cx,cy;
  check_magic(name,f); x = y = z = NULL;
  cx = 0; /* gcc -Wall */
  while ((y = readobj(f, &cy)))
  {
    if (x && cx == BIN_GEN) z = z? shallowconcat(z, mkvec(x)): mkvec(x);
    x = y; cx = cy;
  }
  if (z)
  {
    if (x && cx == BIN_GEN) z = z? shallowconcat(z, mkvec(x)): mkvec(x);
    if (DEBUGLEVEL)
      pari_warn(warner,"%ld unnamed objects read. Returning then in a vector",
	  lg(z)-1);
    x = gerepilecopy(av, z);
    *vector = 1;
  }
  else
    *vector = 0;
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
  pariout_t T = *(GP_DATA->fmt); /* copy */
  long i, l = lg(g);
  T.prettyp = flag;
  for (i = 1; i < l; i++) printGEN(gel(g,i), &T);
}

void
printf0(GEN gfmt, GEN args)
{ (void)v3pariputs((const char*)gfmt,0,0,args); }

GEN
Strprintf(GEN gfmt, GEN args)
{ return v3pariputs((const char *)gfmt,0,1,args); }

void
printf1(GEN gfmt, va_list args) /* the va_list version of printf0 */
{ (void)v3pariputs((const char *)gfmt,1,0,args); }

GEN
Strprintf1(GEN gfmt, va_list args) /* the va_list version of Strprintf */
{ return v3pariputs((const char *)gfmt,1,1,args); }

/* the va_list version of fprintf0 (FIXME: fprintf0 not yet available) */
void
fprintf1(FILE *file, GEN gfmt, va_list args)
{
  pari_sp ltop = avma;
  GEN res = v3pariputs((const char *)gfmt,1,1,args);
  fputs(GSTR(res), file);
  avma = ltop;
}

#define PR_NL() {pariputc('\n'); pariflush(); }
#define PR_NO() pariflush()
void print   (GEN g) { print0(g, f_RAW);       PR_NL(); }
void printp  (GEN g) { print0(g, f_PRETTYOLD); PR_NL(); }
void printtex(GEN g) { print0(g, f_TEX);       PR_NL(); }
void print1  (GEN g) { print0(g, f_RAW);       PR_NO(); }
void printp1 (GEN g) { print0(g, f_PRETTYOLD); PR_NO(); }

void error0(GEN g) { pari_err(user, g); }

static char *
wr_check(const char *s) {
  char *t = expand_tilde(s);
  if (GP_DATA->flags & SECURE)
  {
    fprintferr("[secure mode]: about to write to '%s'. OK ? (^C if not)\n",t);
    hit_return();
  }
  return t;
}

/* Store last_was_newline before writing to restore it after writing. */
static int wr_last_was_newline;

/* Start writing to file s */
static void wr_init(const char *s)
{
  char *t=wr_check(s);
  switchout(t);
  gpfree(t);
  wr_last_was_newline = pari_last_was_newline();
}

/* End writing to file s, go back to stdout */
static void wr_finish()
{
  pariflush();
  switchout(NULL);
  pari_set_last_newline(wr_last_was_newline);
}

#define WR_NL() pariputc('\n'); wr_finish()
#define WR_NO() wr_finish()

void write0  (const char *s, GEN g) { wr_init(s); print0(g, f_RAW); WR_NL(); }
void writetex(const char *s, GEN g) { wr_init(s); print0(g, f_TEX); WR_NL(); }
void write1  (const char *s, GEN g) { wr_init(s); print0(g, f_RAW); WR_NO(); }

void gpwritebin(const char *s, GEN x) { char *t=wr_check(s); writebin(t, x); gpfree(t);}

/*******************************************************************/
/**                                                               **/
/**                       HISTORY HANDLING                        **/
/**                                                               **/
/*******************************************************************/
/* history management function:
 *   p > 0, called from %p
 *   p <= 0, called from %` (|p| backquotes, possibly 0) */
GEN
gp_history(gp_hist *H, long p, char *old, char *entry)
{
  ulong t = H->total, s = H->size;
  GEN z;

  if (!t) pari_err(talker2, "The result history is empty", old, entry);

  if (p <= 0) p += t; /* count |p| entries starting from last */
  if (p <= 0 || p <= (long)(t - s) || (ulong)p > t)
  {
    char *str = stackmalloc(128);
    long pmin = (long)(t - s) + 1;
    if (pmin <= 0) pmin = 1;
    sprintf(str, "History result %%%ld not available [%%%ld-%%%ld]", p,pmin,t);
    pari_err(talker2, str, old, entry);
  }
  z = H->res[ (p-1) % s ];
  if (!z)
  {
    char *str = stackmalloc(128);
    sprintf(str, "History result %%%ld has been deleted (histsize changed)", p);
    pari_err(talker2, str, old, entry);
  }
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
unix_shell(void)
{
  char *base, *sh = getenv("EMXSHELL");
  if (!sh) {
    sh = getenv("COMSPEC");
    if (!sh) return 0;
  }
  base = _getname(sh);
  return (stricmp (base, "cmd.exe") && stricmp (base, "4os2.exe")
       && stricmp (base, "command.com") && stricmp (base, "4dos.com"));
}
#endif

/* check if s has rwx permissions for us */
static int
pari_is_rwx(const char *s)
{
#if defined(UNIX) || defined (__EMX__)
  return access(s, R_OK | W_OK | X_OK) == 0;
#else
  return 1;
#endif
}

#if defined(UNIX) || defined (__EMX__)
#include <sys/types.h>
#include <sys/stat.h>

static int
pari_file_exists(const char *s)
{
  int id = open(s, O_CREAT|O_EXCL|O_RDWR, S_IRUSR|S_IWUSR);
  return id < 0 || close(id);
}
static int
pari_dir_exists(const char *s) { return mkdir(s, 0777); }
#else
static int
pari_file_exists(const char *s) { return 0; }
static int
pari_dir_exists(const char *s) { return 0; }
#endif

char *
env_ok(const char *s)
{
  char *t = os_getenv(s);
  if (t && !pari_is_rwx(t))
  {
    pari_warn(warner,"%s is set (%s), but is not writeable", s,t);
    t = NULL;
  }
  if (t && !pari_is_dir(t))
  {
    pari_warn(warner,"%s is set (%s), but is not a directory", s,t);
    t = NULL;
  }
  return t;
}

static const char*
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

/* loop through 26^2 variants [suffix 'aa' to 'zz'] */
static int
get_file(char *buf, int test(const char *))
{
  char c, d, *end = buf + strlen(buf) - 1;
  for (d = 'a'; d <= 'z'; d++)
  {
    end[-1] = d;
    for (c = 'a'; c <= 'z'; c++)
    {
      *end = c;
      if (! test(buf)) return 1;
    }
  }
  return 0;
}

static void
swap_slash(char *s)
{
#ifdef __EMX__
    if (!unix_shell())
#endif
#if defined(__EMX__) || defined(WINCE)
    {
      char *t;
      for (t=s; *t; t++)
	if (*t == '/') *t = '\\';
    }
#endif
}

static char *
init_unique(const char *s)
{
  const char *pre = pari_tmp_dir();
  char *buf, suf[64];
  size_t lpre, lsuf;
#ifdef UNIX
  sprintf(suf,".%ld.%ld", (long)getuid(), (long)getpid());
#else
  sprintf(suf,".gpa");
#endif
  lsuf = strlen(suf);
  lpre = strlen(pre);
  /* room for prefix + '/' + s + suffix '\0' */
  buf = (char*) gpmalloc(lpre + 1 + 8 + lsuf + 1);
  strcpy(buf, pre);
  if (buf[lpre-1] != '/') { (void)strcat(buf, "/"); lpre++; }
  swap_slash(buf);

  sprintf(buf + lpre, "%.8s%s", s, suf);
  return buf;
}

/* Return a "unique filename" built from the string s, possibly the user id
 * and the process pid (on Unix systems). A "temporary" directory name is
 * prepended. The name returned is gpmalloc'ed. It is DOS-safe
 * (s truncated to 8 chars) */
char*
pari_unique_filename(const char *s)
{
  char *buf = init_unique(s);

  if (pari_file_exists(buf) && !get_file(buf, pari_file_exists))
    pari_err(talker,"couldn't find a suitable name for a tempfile (%s)",s);
  return buf;
}

/* Create a "unique directory" and return its name built from the string
 * s, the user id and process pid (on Unix systems). A "temporary"
 * directory name is prepended. The name returned is gpmalloc'ed.
 * It is DOS-safe (truncated to 8 chars)
 */
char*
pari_unique_dir(const char *s)
{
  char *buf = init_unique(s);
  if (pari_dir_exists(buf) && !get_file(buf, pari_dir_exists))
    pari_err(talker,"couldn't find a suitable name for a tempdir (%s)",s);
  return buf;
}
