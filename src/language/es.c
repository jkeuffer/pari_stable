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

typedef struct outString {
  char *string; /* start of the output buffer */
  char *end;    /* end of the output buffer */
  char *cur;   /* current writing place in the output buffer */
  size_t size; /* buffer size */
} outString;

typedef void (*OUT_FUN)(GEN, pariout_t *, outString *);

static void bruti_sign(GEN g, pariout_t *T, outString *S, int addsign);
static void matbruti(GEN g, pariout_t *T, outString *S);
static void texi_sign(GEN g, pariout_t *T, outString *S, int addsign);
static char *GENtostr_fun(GEN x, pariout_t *T, OUT_FUN out);

static void bruti(GEN g, pariout_t *T, outString *S)
{ bruti_sign(g,T,S,1); }
static void texi(GEN g, pariout_t *T, outString *S)
{ texi_sign(g,T,S,1); }

void
hit_return(void)
{
  int c;
  if (GP_DATA->flags & (EMACS|TEXMACS)) return;
  pari_puts("---- (type RETURN to continue) ----");
  /* if called from a readline callback, may be in a funny TTY mode,  */
  do c = fgetc(stdin); while (c >= 0 && c != '\n' && c != '\r');
  pari_putc('\n');
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

  if (!F->t) F->t = (char*)pari_malloc(strlen(s)+1);
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
  Buffer *b = (Buffer*) pari_malloc(sizeof(Buffer));
  b->len = 1024;
  b->buf = (char*)pari_malloc(b->len);
  return b;
}
/* delete */
void
delete_buffer(Buffer *b)
{
  if (!b) return;
  pari_free((void*)b->buf); pari_free((void*)b);
}
/* resize */
void
fix_buffer(Buffer *b, long newlbuf)
{
  b->len = newlbuf;
  b->buf = (char*)pari_realloc((void*)b->buf, b->len);
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
    if (IM->free) pari_free(to_read);
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

static int last_was_newline = 1;

static void
set_last_newline(char c) { last_was_newline = (c == '\n'); }

void
pari_putc(char c) { set_last_newline(c); pariOut->putch(c); }

void
pari_puts(const char *s) {
  if (*s) {  set_last_newline(s[strlen(s)-1]); pariOut->puts(s); }
}

int
pari_last_was_newline(void) { return last_was_newline; }
void
pari_set_last_newline(int last) { last_was_newline = last; }

void
pari_flush(void) { pariOut->flush(); }

void
flusherr(void) { pariErr->flush(); }

/* e binary exponent, return exponent in base ten */
static long
ex10(long e) { return (long) ((e >= 0)? e*LOG10_2: -(-e*LOG10_2)-1); }

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

/* let ndig <= 9, x < 10^ndig, write in p[-ndig..-1] the decimal digits of x */
static void
utodec(char *p, ulong x, long ndig)
{
  switch(ndig)
  {
    case  9: *--p = x % 10 + '0'; x = x/10;
    case  8: *--p = x % 10 + '0'; x = x/10;
    case  7: *--p = x % 10 + '0'; x = x/10;
    case  6: *--p = x % 10 + '0'; x = x/10;
    case  5: *--p = x % 10 + '0'; x = x/10;
    case  4: *--p = x % 10 + '0'; x = x/10;
    case  3: *--p = x % 10 + '0'; x = x/10;
    case  2: *--p = x % 10 + '0'; x = x/10;
    case  1: *--p = x % 10 + '0'; x = x/10;
  }
}

/* convert abs(x) != 0 to str. Prepend '-' if (sx < 0) */
static char *
itostr_sign(GEN x, int sx, long *len)
{
  long l, d;
  ulong *res = convi(x, &l);
  /* l 9-digits words (< 10^9) + (optional) sign + \0 */
  char *s = (char*)new_chunk(nchar2nlong(l*9 + 1 + 1)), *t = s;

  if (sx < 0) *t++ = '-';
  d = numdig(*--res); t += d; utodec(t, *res, d);
  while (--l > 0) { t += 9; utodec(t, *--res, 9); }
  *t = 0; *len = t - s; return s;
}

/********************************************************************/
/**                                                                **/
/**                        WRITE A REAL NUMBER                     **/
/**                                                                **/
/********************************************************************/
/* 19 digits (if 64 bits, at most 2^60-1) + 1 sign */
static const long MAX_EXPO_LEN = 20;

/* write z to buf, inserting '.' at 'point', 0 < point < strlen(z) */
static void
wr_dec(char *buf, char *z, long point)
{
  char *s = buf + point;
  strncpy(buf, z, point); /* integer part */
  *s++ = '.'; z += point;
  while ( (*s++ = *z++) ) /* empty */;
}

static char *
zerotostr()
{
  char *s = (char*)new_chunk(1);
  s[0] = '0';
  s[1] = 0; return s;
}

/* write a real 0 of exponent ex in format f */
static char *
real0tostr_width_frac(long width_frac)
{
  char *buf, *s;
  if (width_frac == 0) return zerotostr();
  buf = s = stackmalloc(width_frac + 3);
  *s++ = '0';
  *s++ = '.';
  (void)zeros(s, width_frac);
  return buf;
}

/* write a real 0 of exponent ex */
static char *
real0tostr(long ex, char format, char exp_char, long wanted_dec)
{
  char *buf, *buf0;

  if (format == 'f') {
    long width_frac = wanted_dec;
    if (width_frac < 0) width_frac = (ex >= 0)? 0: (long)(-ex * LOG10_2);
    return real0tostr_width_frac(width_frac);
  } else {
    buf0 = buf = stackmalloc(3 + MAX_EXPO_LEN + 1);
    *buf++ = '0';
    *buf++ = '.';
    *buf++ = exp_char;
    sprintf(buf, "%ld", ex10(ex) + 1);
  }
  return buf0;
}

/* format f, width_frac >= 0: number of digits in fractional part, */
static char *
absrtostr_width_frac(GEN x, int width_frac)
{
  long beta, ls, point, lx, sx = signe(x);
  char *s, *buf, *buf0;
  GEN z;

  if (!sx) return real0tostr_width_frac(width_frac);

  /* x != 0 */
  lx = lg(x);
  beta = width_frac;
  if (beta) /* >= 0 */
  { /* z = |x| 10^beta, 10^b = 5^b * 2^b, 2^b goes into exponent */
    if (beta > 4e9) lx++;
    z = mulrr(x, rpowuu(5UL, (ulong)beta, lx+1));
    z[1] = evalsigne(1) | evalexpo(expo(z) + beta);
  }
  else
    z = mpabs(x);
  z = roundr_safe(z);
  if (!signe(z)) return real0tostr_width_frac(width_frac);

  s = itostr_sign(z, 1, &ls); /* ls > 0, number of digits in s */
  /* '.', trailing \0 */
  buf0 = buf = stackmalloc( ls + 1+1 );
  point = ls - beta; /* position of . in s; <= ls, may be < 0 */
  if (point > 0) /* write integer_part.fractional_part */
  {
    if (ls == point)
      strcpy(buf, s); /* no '.' */
    else
      wr_dec(buf, s, point);
  } else { /* point <= 0, fractional part must be written */
    *buf++ = '0';
    *buf++ = '.';
    buf = zeros(buf, -point);
    strcpy(buf, s);
  }
  return buf0;
}

/* Return t_REAL |x| in floating point format.
 * Allocate freely, the caller must clean the stack.
 *   FORMAT: E/e (exponential), F/f (floating point), G/g
 *   wanted_dec: number of significant digits to print (all if < 0).
 */
static char *
absrtostr(GEN x, int sp, char FORMAT, long wanted_dec)
{
  const char format = tolower(FORMAT), exp_char = (format == FORMAT)? 'e': 'E';
  long beta, ls, point, lx, sx = signe(x), ex = expo(x);
  char *s, *buf, *buf0;
  GEN z;

  if (!sx) return real0tostr(ex, format, exp_char, wanted_dec);

  /* x != 0 */
  lx = lg(x);
  if (wanted_dec >= 0)
  { /* reduce precision if possible */
    long w = ndec2prec(wanted_dec); /* digits -> pari precision in words */
    if (lx > w) lx = w; /* truncature with guard, no rounding */
  }
  beta = ex10(bit_accuracy(lx) - ex);
  if (beta)
  { /* z = |x| 10^beta, 10^b = 5^b * 2^b, 2^b goes into exponent */
    if (beta > 0)
    {
      if (beta > 4e9) lx++;
      z = mulrr(x, rpowuu(5UL, (ulong)beta, lx+1));
    }
    else
    {
      if (beta < -4e9) lx++;
      z = divrr(x, rpowuu(5UL, (ulong)-beta, lx+1));
    }
    z[1] = evalsigne(1) | evalexpo(expo(z) + beta);
  }
  else
    z = x;
  z = roundr_safe(z);
  if (!signe(z)) return real0tostr(ex, format, exp_char, wanted_dec);

  s = itostr_sign(z, 1, &ls); /* ls > 0, number of digits in s */
  if (wanted_dec < 0)
    wanted_dec = ls;
  else if (ls > wanted_dec)
  {
    beta -= ls - wanted_dec;
    ls = wanted_dec;
    if (s[ls] >= '5') /* round up */
    {
      long i;
      for (i = ls-1; i >= 0; s[i--] = '0')
        if (++s[i] <= '9') break;
      if (i < 0) { s[0] = '1'; beta--; }
    }
    s[ls] = 0;
  }

  /* '.', " E", exponent, trailing \0 */
  buf0 = buf = stackmalloc( ls + 1+2+MAX_EXPO_LEN+1 );
  point = ls - beta; /* position of . in s; < 0 or > 0 */
  if (beta <= 0 || format == 'e' || (format == 'g' && point-1 < -4))
  { /* e format */
    wr_dec(buf, s, 1); buf += ls + 1;
    if (sp) *buf++ = ' ';
    *buf++ = exp_char;
    sprintf(buf, "%ld", point-1);
  } else { /* f format */
    if (point > 0) /* write integer_part.fractional_part */
      wr_dec(buf, s, point); /* point < ls since beta > 0 */
    else { /* point <= 0, write fractional part */
      *buf++ = '0';
      *buf++ = '.';
      buf = zeros(buf, -point);
      strcpy(buf, s);
    }
  }
  return buf0;
}

/* vsnprintf implementation rewritten from snprintf.c to be found at
 *
 * http://www.nersc.gov/~scottc/misc/docs/snort-2.1.1-RC1/snprintf_8c-source.html
 * The original code was
 *   Copyright (C) 1998-2002 Martin Roesch <roesch@sourcefire.com>
 * available under the terms of the GNU GPL version 2 or later. It
 * was itself adapted from an original version by Patrick Powell. */

/* Modifications for format %Ps: R.Butel IMB/CNRS 2007/12/03 */

static void
str_putc(outString *S, char c) {
  *S->cur++ = c;
  if (S->cur == S->end)
  {
    size_t l = S->size << 1;
    S->string = (char*)pari_realloc((void*)S->string, l);
    S->cur = S->string + S->size;
    S->end = S->string + l;
    S->size = l;
  }
}
static void
str_init(outString *S)
{
  S->size = 1024;
  S->string = S->cur = (char*)pari_malloc(S->size);
  S->end = S->string + S->size;
}
static void
str_puts(outString *S, const char *s) { while (*s) str_putc(S, *s++); }

static void
str_putscut(outString *S, const char *str, int cut)
{
  if (cut < 0) str_puts(S, str);
  else {
    while (*str && cut-- > 0) str_putc(S, *str++);
  }
}

/* lbuf = strlen(buf), len < 0: unset */
static void
outpad(outString *S, const char *buf, long lbuf, int sign, long ljust, long len, long zpad)
{
  long padlen = len - lbuf;
  if (padlen < 0) padlen = 0;
  if (ljust) padlen = -padlen;
  if (padlen > 0)
  {
    if (zpad) {
      if (sign) { str_putc(S, sign); --padlen; }
      while (padlen > 0) { str_putc(S, '0'); --padlen; }
    }
    else
    {
      if (sign) --padlen;
      while (padlen > 0) { str_putc(S, ' '); --padlen; }
      if (sign) str_putc(S, sign);
    }
  } else
    if (sign) str_putc(S, sign);
  str_puts(S, buf);
  while (padlen < 0) { str_putc(S, ' '); ++padlen; }
}

/* len < 0 or maxwidth < 0: unset */
static void
fmtstr(outString *S, const char *buf, int ljust, int len, int maxwidth)
{
  int padlen, lbuf = strlen(buf);

  if (maxwidth >= 0 && lbuf > maxwidth) lbuf = maxwidth;

  padlen = len - lbuf;
  if (padlen < 0) padlen = 0;
  if (ljust) padlen = -padlen;
  while (padlen > 0) { str_putc(S, ' '); --padlen; }
  str_putscut(S, buf, maxwidth);
  while (padlen < 0) { str_putc(S, ' '); ++padlen; }
}

/* abs(base) is 8, 10, 16. If base < 0, some "alternate" form
 * -- print hex in uppercase
 * -- prefix octal with 0
 * signvalue = -1: unsigned, otherwise ' ' or '+' */
static void
fmtnum(outString *S, long lvalue, GEN gvalue, int base, int signvalue,
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
          str_putc(S, '[');
          for (i = 1; i < l; i++)
          {
            fmtnum(S, 0, gel(gvalue,i), base, signvalue, ljust,len,zpad);
            if (i < l-1) str_putc(S, ',');
          }
          str_putc(S, ']');
          return;
        case t_COL:
          str_putc(S, '[');
          for (i = 1; i < l; i++)
          {
            fmtnum(S, 0, gel(gvalue,i), base, signvalue, ljust,len,zpad);
            if (i < l-1) str_putc(S, ',');
          }
          str_putc(S, ']');
          str_putc(S, '~');
          return;
        case t_MAT:
          if (l == 1)
            str_puts(S, "[;]");
          else
          {
            h = lg(gvalue[1]);
            for (i=1; i<l; i++)
            {
              str_putc(S, '[');
              for (j=1; j<h; j++)
              {
                fmtnum(S, 0, gcoeff(gvalue,i,j), base, signvalue, ljust,len,zpad);
                if (j<h-1) str_putc(S, ' ');
              }
              str_putc(S, ']');
              str_putc(S, '\n');
              if (i<l-1) str_putc(S, '\n');
            }
          }
          return;
      }
      gvalue = gfloor( simplify_i(gvalue) );
      if (typ(gvalue) != t_INT)
        pari_err(talker,"not a t_INT in integer format conversion: %Ps", gvalue);
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
  outpad(S, buf, lbuf, signvalue, ljust, len, zpad);
  avma = av;
}

static GEN
v_get_arg(GEN arg_vector, int *index, const char *save_fmt)
{
  if (*index >= lg(arg_vector))
    pari_err(talker, "missing arg %d for printf format '%s'", *index, save_fmt);
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

static long
get_sigd(GEN gvalue, char ch, int maxwidth)
{
  long sigd;
  if (maxwidth < 0) return prec2ndec(precreal);
  switch(ch)
  {
    case 'E':
    case 'e': sigd = maxwidth+1; break;
    case 'F':
    case 'f': sigd = ex10(gexpo(gvalue)) + 1 + maxwidth; break;
    /* 'g', 'G' */
    default : sigd = maxwidth? maxwidth: 1; break;
  }
  return sigd;
}

static void
fmtreal(outString *S, GEN gvalue, int space, int signvalue, int FORMAT,
        int maxwidth, int ljust, int len, int zpad)
{
  pari_sp av = avma;
  long sigd;
  char *buf;

  if (typ(gvalue) == t_REAL)
    sigd = get_sigd(gvalue, FORMAT, maxwidth);
  else
  {
    long i, j, h, l = lg(gvalue);
    switch(typ(gvalue))
    {
      case t_VEC:
        str_putc(S, '[');
        for (i = 1; i < l; i++)
        {
          fmtreal(S, gel(gvalue,i), space, signvalue, FORMAT, maxwidth,
                  ljust,len,zpad);
          if (i < l-1) str_putc(S, ',');
        }
        str_putc(S, ']');
        return;
      case t_COL:
        str_putc(S, '[');
        for (i = 1; i < l; i++)
        {
          fmtreal(S, gel(gvalue,i), space, signvalue, FORMAT, maxwidth,
                  ljust,len,zpad);
          if (i < l-1) str_putc(S, ',');
        }
        str_putc(S, ']');
        str_putc(S, '~');
        return;
      case t_MAT:
        if (l == 1)
          str_puts(S, "[;]");
        else
        {
          h = lg(gvalue[1]);
          for (i=1; i<l; i++)
          {
            str_putc(S, '[');
            for (j=1; j<h; j++)
            {
              fmtreal(S, gcoeff(gvalue,i,j), space, signvalue, FORMAT, maxwidth,
                      ljust,len,zpad);
              if (j<h-1) str_putc(S, ' ');
            }
            str_putc(S, ']');
            str_putc(S, '\n');
            if (i<l-1) str_putc(S, '\n');
          }
        }
        return;
    }
    sigd = get_sigd(gvalue, FORMAT, maxwidth);
    gvalue = gtofp(gvalue, ndec2prec(sigd));
    if (typ(gvalue) != t_REAL)
      pari_err(talker,"impossible conversion to t_REAL: %Ps",gvalue);
  }
  if ((FORMAT == 'f' || FORMAT == 'F') && maxwidth >= 0)
    buf = absrtostr_width_frac(gvalue, maxwidth);
  else
    buf = absrtostr(gvalue, space, FORMAT, sigd);
  if (signe(gvalue) < 0) signvalue = '-';
  outpad(S, buf, strlen(buf), signvalue, ljust, len, zpad);
  avma = av;
}
/* format handling "inspired" by the standard draft at
-- http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1124.pdf pages 274ff
 * fmt is a standard printf format, except 'Z' is a "length modifier"
 * allowing GEN arguments. Use either the arg_vector or (if NULL) the va_list */
static char *
sm_dopr(const char *fmt, GEN arg_vector, va_list args)
{
  int GENflag = 0, longflag = 0, pointflag = 0;
  int print_plus, print_blank, with_sharp, ch, ljust, len, maxwidth, zpad;
  long lvalue;
  int index = 1;
  GEN gvalue;
  const char *recall = NULL, *save_fmt = fmt;
  outString __S, *S = &__S;

  str_init(S);

  while ((ch = *fmt++) != '\0') {
    switch(ch) {
      case '%':
        ljust = zpad = 0;
        len = maxwidth = -1;
        GENflag = longflag = pointflag = 0;
        recall = fmt - 1; /* '%' was skipped */
        print_plus = print_blank = with_sharp = 0;
nextch:
        ch = *fmt++;
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
            print_plus = 1;
            goto nextch;
          case '#':
            with_sharp = 1;
            goto nextch;
          case ' ':
            print_blank = 1;
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
            if (arg_vector)
              *t = (int)gtolong( v_get_arg(arg_vector, &index, save_fmt) );
            else
              *t = va_arg(args, int);
            goto nextch;
          }
          case '.':
            if (pointflag)
              pari_err(talker, "two '.' in conversion specification");
            pointflag = 1;
            goto nextch;
/*------------------------------------------------------------------------
                       -- length modifiers
------------------------------------------------------------------------*/
          case 'l':
            if (GENflag)
              pari_err(talker, "P/l length modifiers in the same conversion");
            if (longflag)
              pari_err(impl, "ll length modifier in printf");
            longflag = 1;
            goto nextch;
          case 'P':
            if (longflag)
              pari_err(talker, "P/l length modifiers in the same conversion");
            if (GENflag)
              pari_err(talker, "'P' length modifier appears twice");
            GENflag = 1;
            goto nextch;
          case 'h': /* dummy: va_arg promotes short into int */
            goto nextch;
/*------------------------------------------------------------------------
                       -- conversions
------------------------------------------------------------------------*/
          case 'u': /* not a signed conversion: print_(blank|plus) ignored */
#define get_num_arg() \
  if (arg_vector) { \
    lvalue = 0; \
    gvalue = v_get_arg(arg_vector, &index, save_fmt); \
  } else { \
    if (GENflag) { \
      lvalue = 0; \
      gvalue = va_arg(args, GEN); \
    } else { \
      lvalue = longflag? va_arg(args, long): va_arg(args, int); \
      gvalue = NULL; \
    } \
  }
            get_num_arg();
            fmtnum(S, lvalue, gvalue, 10, -1, ljust, len, zpad);
            break;
          case 'o': /* not a signed conversion: print_(blank|plus) ignored */
            get_num_arg();
            fmtnum(S, lvalue, gvalue, with_sharp? -8: 8, -1, ljust, len, zpad);
            break;
          case 'd':
          case 'i':
            get_num_arg();
            fmtnum(S, lvalue, gvalue, 10,
                   dosign(print_blank, print_plus), ljust, len, zpad);
            break;
          case 'p':
            str_putc(S, '0'); str_putc(S, 'x');
            if (arg_vector)
              lvalue = (long)v_get_arg(arg_vector, &index, save_fmt);
            else
              lvalue = (long)va_arg(args, void*);
            fmtnum(S, lvalue, NULL, 16, -1, ljust, len, zpad);
            break;
          case 'x': /* not a signed conversion: print_(blank|plus) ignored */
            if (with_sharp) { str_putc(S, '0'); str_putc(S, 'x'); }
            get_num_arg();
            fmtnum(S, lvalue, gvalue, 16, -1, ljust, len, zpad);
            break;
          case 'X': /* not a signed conversion: print_(blank|plus) ignored */
            if (with_sharp) { str_putc(S, '0'); str_putc(S, 'X'); }
            get_num_arg();
            fmtnum(S, lvalue, gvalue,-16, -1, ljust, len, zpad);
            break;
          case 's':
          {
            char *strvalue;
            int tofree = 0;

            if (arg_vector) {
              gvalue = v_get_arg(arg_vector, &index, save_fmt);
              strvalue = NULL;
            } else {
              if (GENflag) {
                gvalue = va_arg(args, GEN);
                strvalue = NULL;
              } else {
                gvalue = NULL;
                strvalue = va_arg(args, char *);
              }
            }
            if (gvalue)
            {
              if (typ(gvalue) == t_STR)
                strvalue = GSTR(gvalue);
              else
              {
                strvalue = GENtostr_fun(gvalue, GP_DATA->fmt, bruti);
                tofree = 1;
              }
            }
            fmtstr(S, strvalue, ljust, len, maxwidth);
            if (tofree) pari_free(strvalue);
            break;
          }
          case 'c':
            if (arg_vector) {
              gvalue = v_get_arg(arg_vector, &index, save_fmt);
              ch = (int)gtolong(gvalue);
            } else {
              if (GENflag)
                ch = (int)gtolong( va_arg(args,GEN) );
              else
                ch = va_arg(args, int);
            }
            str_putc(S, ch);
            break;

          case '%':
            str_putc(S, ch);
            continue;
          case 'g':
          case 'G':
          case 'e':
          case 'E':
          case 'f':
          case 'F':
          {
            pari_sp av = avma;
            if (arg_vector)
              gvalue = simplify_i( v_get_arg(arg_vector, &index, save_fmt) );
            else {
              if (GENflag)
                gvalue = simplify_i( va_arg(args, GEN) );
              else
                gvalue = dbltor( va_arg(args, double) );
            }
            fmtreal(S, gvalue, GP_DATA->fmt->sp, dosign(print_blank,print_plus),
                    ch, maxwidth, ljust, len, zpad);
            avma = av; break;
          }
          default:
            pari_err(talker, "invalid conversion or specification %c in format `%s'", ch, save_fmt);
        } /* second switch on ch */
        break;
      default:
        str_putc(S, ch);
        break;
    } /* first switch on ch */
  } /* while loop on ch */
  *S->cur = 0;
  return S->string;
}

/* start printing in "color" c */
/* terminal has to support ANSI color escape sequences */
void
term_color(long c)
{
  FILE *o_logfile = pari_logfile;

  if (logstyle != logstyle_color) pari_logfile = 0; /* Ugly hack */
  /* _not_ pari_puts, because of last_was_newline */
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

static int col_index;

/* output string wrapped after MAX_WIDTH characters (for gp -test) */
static void
putc80(char c)
{
  const int MAX_WIDTH = 76;
  if (c == '\n') col_index = 0;
  else if (col_index == MAX_WIDTH) { normalOutC('\n'); col_index = 1; }
  else col_index++;
  normalOutC(c);
}
static void
puts80(const char *s) { while (*s) putc80(*s++); }

PariOUT pariOut80= {putc80, puts80, normalOutF, NULL};

void
init80col() { col_index = 0; pariOut = &pariOut80; }

/* output stopped after max_line have been printed, for default(lines,).
 * n = length of prefix already printed (print up to max_lin lines) */
void
lim_lines_output(char *s, long n, long max_lin)
{
  long lin, col, width;
  char c;
  if (!*s) return;
  width = term_width();
  lin = 1;
  col = n;

  if (lin > max_lin) return;
  while ( (c = *s++) )
  {
    if (lin >= max_lin)
      if (c == '\n' || col >= width-5)
      {
        normalOutS(term_get_color(c_ERR));
        normalOutS("[+++]"); return;
      }
    if (c == '\n')         { col = -1; lin++; }
    else if (col == width) { col =  0; lin++; }
    set_last_newline(c);
    col++; normalOutC(c);
  }
}

static void
new_line(const char *prefix)
{
  pari_putc('\n'); if (prefix) pari_puts(prefix);
}

static long
strlen_real(const char *s)
{
  const char *t = s;
  long len = 0;
  while (*t)
  {
    if (t[0] == ESC && t[1] == '[')
    { /* skip ANSI escape sequence */
      t += 2;
      while (*t && *t++ != 'm') /* empty */;
      continue;
    }
    t++; len++;
  }
  return len;
}

#define is_blank(c) ((c) == ' ' || (c) == '\n' || (c) == '\t')
/* output: <prefix>< s wrapped at EOL >
 *         <prefix>< ... > <str>
 *                         ^---  (no \n at the end)
 * If str is NULL, omit the arrow, end the text with '\n'.
 * If prefix is NULL, use "" */
void
print_prefixed_text(const char *s, const char *prefix, const char *str)
{
  const long prelen = prefix? strlen_real(prefix): 0;
  const long W = term_width(), ls = strlen(s);
  long linelen = prelen;
  char *word = stackmalloc(ls + 3);

  if (prefix) pari_puts(prefix);
  for(;;)
  {
    long len;
    int blank = 0;
    char *u = word;
    while (*s && !is_blank(*s)) *u++ = *s++;
    *u = 0; /* finish "word" */
    len = strlen_real(word);
    linelen += len;
    if (linelen >= W) { new_line(prefix); linelen = prelen + len; }
    pari_puts(word);
    while (is_blank(*s)) {
      switch (*s) {
        case ' ': break;
        case '\t':
          linelen = (linelen & ~7UL) + 8; pari_putc('\t');
          blank = 1; break;
        case '\n':
          linelen = W;
          blank = 1; break;
      }
      if (linelen >= W) { new_line(prefix); linelen = prelen; }
      s++;
    }
    if (!*s) break; 
    if (!blank) { pari_putc(' '); linelen++; }
  }
  if (!str)
    pari_putc('\n');
  else
  {
    long i,len = strlen_real(str);
    int space = (*str == ' ' && str[1]);
    if (linelen + len >= W)
    {
      new_line(prefix); linelen = prelen;
      if (space) { str++; len--; space = 0; }
    }
    term_color(c_OUTPUT);
    pari_puts(str); if (!len || str[len-1] != '\n') pari_putc('\n');
    if (space) { linelen++; len--; }
    term_color(c_ERR);
    for (i=0; i<linelen; i++) pari_putc(' ');
    pari_putc('^');
    for (i=0; i<len; i++) pari_putc('-');
  }
}

/********************************************************************/
/**                                                                **/
/**                    GEN <---> CHARACTER STRINGS                 **/
/**                                                                **/
/********************************************************************/
static OUT_FUN
get_fun(long flag)
{
  switch(flag) {
    case f_RAW : return bruti;
    case f_TEX : return texi;
    default: return matbruti;
  }
}

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
  char *t = (char*)pari_malloc(n);
  memcpy(t,s,n); return t;
}

char *
pari_strndup(const char *s, long n)
{
  char *t = (char*)pari_malloc(n+1);
  memcpy(t,s,n); t[n] = 0; return t;
}

/* returns a malloc-ed string, which should be freed after usage */
/* Returns pari_malloc()ed string */
static char *
GENtostr_fun(GEN x, pariout_t *T, OUT_FUN out) {
  pari_sp av = avma;
  outString S;
  str_init(&S); out(x, T, &S); *S.cur = 0;
  avma = av; return S.string;
}
char *
GENtostr(GEN x) {
  pariout_t *T = GP_DATA->fmt;
  return GENtostr_fun(x, T, get_fun(T->prettyp));
}
char *
GENtoTeXstr(GEN x) { return GENtostr_fun(x, GP_DATA->fmt, &texi); }

static char *
GENtostr1(GEN x, OUT_FUN out)
{
  return (typ(x) == t_STR)? pari_strdup(GSTR(x))
                          : GENtostr_fun(x, GP_DATA->fmt, out);
}

/* see print0(). Returns pari_malloc()ed string */
static char *
RgV_to_str_fun(GEN g, OUT_FUN out) {
  pari_sp av = avma;
  char *t, *t2;
  long i, tlen = 0, l = lg(g);
  GEN Ls, Ll;

  /* frequent special case */
  if (l == 2) return GENtostr1(gel(g,1), out);

  Ls = cgetg(l, t_VEC);
  Ll = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++)
  {
    char *s = GENtostr1(gel(g,i), out);
    gel(Ls,i) = (GEN)s;
    Ll[i] = strlen(s);
    tlen += Ll[i];
  }
  t2 = t = (char*)pari_malloc(tlen + 1);
  *t = 0;
  for (i = 1; i < l; i++)
  {
    strcpy(t2, (char*)Ls[i]);
    t2 += Ll[i];
    pari_free((void*)Ls[i]);
  }
  avma = av; return t;
}

char *
RgV_to_str(GEN g, long flag) { return RgV_to_str_fun(g, get_fun(flag)); }

static GEN
Str_fun(GEN g, OUT_FUN out) {
  char *t = RgV_to_str_fun(g, out);
  GEN z = strtoGENstr(t);
  pari_free(t); return z;
}
GEN Str(GEN g)    { return Str_fun(g, &bruti); }
GEN Strtex(GEN g) { return Str_fun(g, &texi); }
GEN
Strexpand(GEN g) {
  char *s = RgV_to_str_fun(g, &bruti), *t = path_expand(s);
  GEN z = strtoGENstr(t);
  pari_free(t); pari_free(s); return z;
}

GEN
GENtoGENstr(GEN x)
{
  char *s = GENtostr_fun(x, GP_DATA->fmt, &bruti);
  GEN z = strtoGENstr(s); pari_free(s); return z;
}

GEN
GENtoGENstr_nospace(GEN x)
{
  pariout_t T = *(GP_DATA->fmt);
  char *s;
  GEN z;
  T.sp = 0;
  s = GENtostr_fun(x, &T, &bruti);
  z = strtoGENstr(s); pari_free(s); return z;
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
    return chartoGENstr(itoc(g));
  *s = 0; return x;
}

/********************************************************************/
/**                                                                **/
/**                         WRITE AN INTEGER                       **/
/**                                                                **/
/********************************************************************/
char *
itostr(GEN x) {
  long sx = signe(x), l;
  return sx? itostr_sign(x, sx, &l): zerotostr();
}

/* x != 0 t_INT, write abs(x) to S */
static void
str_absint(outString *S, GEN x)
{
  pari_sp av = avma;
  long l;
  str_puts(S, itostr_sign(x, 1, &l)); avma = av;
}

#define putsigne_nosp(S, x) str_putc(S, (x>0)? '+' : '-')
#define putsigne(S, x) str_puts(S, (x>0)? " + " : " - ")
#define sp_sign_sp(T,S, x) ((T)->sp? putsigne(S,x): putsigne_nosp(S,x))
#define comma_sp(T,S)     ((T)->sp? str_puts(S, ", "): str_putc(S, ','))

/* print e to S (more efficient than sprintf) */
static void
str_ulong(outString *S, ulong e)
{
  if (e == 0) str_putc(S, '0');
  else
  {
    const int MAX = 21;
    char buf[MAX], *p = buf + MAX;
    *--p = 0;
    if (e > 9) {
      do
        *--p = "0123456789"[e % 10];
      while ((e /= 10) > 9);
    }
    *--p = "0123456789"[e];
    str_puts(S, p);
  }
}
static void
str_long(outString *S, long e)
{
  if (e >= 0) str_ulong(S, (ulong)e);
  else { str_putc(S, '-'); str_ulong(S, (ulong)(-e)); }
}

static void
wr_vecsmall(pariout_t *T, outString *S, GEN g)
{
  long i, l;
  str_puts(S, "Vecsmall(["); l = lg(g);
  for (i=1; i<l; i++)
  {
    str_long(S, g[i]);
    if (i<l-1) comma_sp(T,S);
  }
  str_puts(S, "])");
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

static void
blancs(long nb) { while (nb-- > 0) pari_putc(' '); }

/* write an "address" */
static void
str_addr(outString *S, ulong x)
{ char s[128]; sprintf(s,"%0*lx", BITS_IN_LONG/4, x); str_puts(S, s); }
static void
dbg_addr(ulong x) { pari_printf("[&=%0*lx] ", BITS_IN_LONG/4, x); }
/* write a "word" */
static void
dbg_word(ulong x) { pari_printf("%0*lx ", BITS_IN_LONG/4, x); }

/* bl: indent level */
static void
dbg(GEN x, long nb, long bl)
{
  long tx,i,j,e,dx,lx;

  if (!x) { pari_puts("NULL\n"); return; }
  tx = typ(x);
  if (tx == t_INT && x == gen_0) { pari_puts("gen_0\n"); return; }
  dbg_addr((ulong)x);

  lx = lg(x);
  pari_printf("%s(lg=%ld%s):",type_name(tx)+2,lx,isclone(x)? ",CLONE" : "");
  dbg_word(x[0]);
  if (! is_recursive_t(tx)) /* t_INT, t_REAL, t_STR, t_VECSMALL */
  {
    if (tx == t_STR)
      pari_puts("chars:");
    else if (tx == t_INT)
    {
      lx = lgefint(x);
      pari_printf("(%c,lgefint=%ld):", vsigne(x), lx);
    }
    else if (tx == t_REAL)
      pari_printf("(%c,expo=%ld):", vsigne(x), expo(x));
    if (nb < 0) nb = lx;
    for (i=1; i < nb; i++) dbg_word(x[i]);
    pari_putc('\n'); return;
  }

  if (tx == t_PADIC)
    pari_printf("(precp=%ld,valp=%ld):", precp(x), valp(x));
  else if (tx == t_POL)
    pari_printf("(%c,varn=%ld):", vsigne(x), varn(x));
  else if (tx == t_SER)
    pari_printf("(%c,varn=%ld,prec=%ld,valp=%ld):",
	       vsigne(x), varn(x), lgpol(x), valp(x));
  else if (tx == t_LIST)
  {
    pari_printf("(lmax=%ld):", list_nmax(x));
    x = list_data(x); lx = x? lg(x): 1;
  } else if (tx == t_CLOSURE)
    pari_printf("(arity=%ld):", x[1]);
  for (i=1; i<lx; i++) dbg_word(x[i]);
  bl+=2; pari_putc('\n');
  switch(tx)
  {
    case t_INTMOD: case t_POLMOD:
    {
      const char *s = (tx==t_INTMOD)? "int = ": "pol = ";
      blancs(bl); pari_puts("mod = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts(s);        dbg(gel(x,2),nb,bl);
      break;
    }
    case t_FRAC: case t_RFRAC:
      blancs(bl); pari_puts("num = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts("den = "); dbg(gel(x,2),nb,bl);
      break;

    case t_FFELT:
      blancs(bl); pari_puts("pol = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("mod = "); dbg(gel(x,3),nb,bl);
      blancs(bl); pari_puts("p   = "); dbg(gel(x,4),nb,bl);
      break;

    case t_COMPLEX:
      blancs(bl); pari_puts("real = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts("imag = "); dbg(gel(x,2),nb,bl);
      break;

    case t_PADIC:
      blancs(bl); pari_puts("  p : "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("p^l : "); dbg(gel(x,3),nb,bl);
      blancs(bl); pari_puts("  I : "); dbg(gel(x,4),nb,bl);
      break;

    case t_QUAD:
      blancs(bl); pari_puts("pol = ");  dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts("real = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("imag = "); dbg(gel(x,3),nb,bl);
      break;

    case t_POL: case t_SER:
      e = (tx==t_SER)? valp(x): 0;
      for (i=2; i<lx; i++)
      {
	blancs(bl); pari_printf("coef of degree %ld = ",e);
	e++; dbg(gel(x,i),nb,bl);
      }
      break;

    case t_LIST:
      x = list_data(x); lx = x ? lg(x): 1;
    case t_QFR: case t_QFI: case t_VEC: case t_COL:
      for (i=1; i<lx; i++)
      {
	blancs(bl); pari_printf("%ld%s component = ",i,eng_ord(i));
	dbg(gel(x,i),nb,bl);
      }
      break;

    case t_CLOSURE:
      blancs(bl); pari_puts("code = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("operand = "); dbg(gel(x,3),nb,bl);
      blancs(bl); pari_puts("data = "); dbg(gel(x,4),nb,bl);
      if (lg(x)>=6)
      {
        blancs(bl); pari_puts("text = "); dbg(gel(x,5),nb,bl);
        if (lg(x)>=7)
        {
          blancs(bl); pari_puts("frame = "); dbg(gel(x,6),nb,bl);
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
	  blancs(bl); pari_printf("%ld%s column = ",i,eng_ord(i));
	  dbg(gel(x,i),nb,bl);
	}
      }
      else
      {
	dx = lg(c);
	for (i=1; i<dx; i++)
	  for (j=1; j<lx; j++)
	  {
	    blancs(bl); pari_printf("mat(%ld,%ld) = ",i,j);
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
  pari_printf(" %s ",ep->name); dbg_addr((ulong)ep);
  pari_printf(":\n   hash = %3ld, menu = %2ld, code = %-10s",
	    hash, ep->menu, ep->code? ep->code: "NULL");
  if (ep->next)
  {
    pari_printf("next = %s ",(ep->next)->name);
    dbg_addr((ulong)ep->next);
  }
  pari_puts("\n");
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
      if (*s !='$') m = minss(atol(s),m);
      if (m<n) pari_err(talker,"invalid range in print_functions_hash");
    }

    for(; n<=m; n++)
    {
      pari_printf("*** hashcode = %lu\n",n);
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
      pari_printf("%3ld:%3ld ",n,m);
      if (n%9 == 8) pari_putc('\n');
    }
    pari_putc('\n'); return;
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
  pari_printf("Total: %ld, Max: %ld\n", Total, Max);
}

/********************************************************************/
/**                                                                **/
/**                        FORMATTED OUTPUT                        **/
/**                                                                **/
/********************************************************************/
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
dbg_pari_heap(void)
{
  long nu, l, u, s;
  pari_sp av = avma;
  GEN adr = getheap();

  nu = (top-avma)/sizeof(long);
  l = (top-bot)/sizeof(long);
  pari_printf("\n Top : %lx   Bottom : %lx   Current stack : %lx\n",
	      top, bot, avma);
  pari_printf(" Used :                         %ld  long words  (%ld K)\n",
	      nu, nu/1024*sizeof(long));
  pari_printf(" Available :                    %ld  long words  (%ld K)\n",
	      (l-nu), (l-nu)/1024*sizeof(long));
  pari_printf(" Occupation of the PARI stack : %6.2f percent\n", 100.0*nu/l);
  pari_printf(" %ld objects on heap occupy %ld long words\n\n",
	      itos(gel(adr,1)), itos(gel(adr,2)));
  u = pari_var_next();
  s = MAXVARN - pari_var_next_temp();
  pari_printf(" %ld variable names used (%ld user + %ld private) out of %d\n\n",
	      u+s, u, s, MAXVARN);
  avma = av;
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
texexpo(outString *S, long e)
{
  if (e != 1) {
    str_putc(S, '^');
    if (e >= 0 && e < 10)
    { str_putc(S, '0' + e); }
    else
    {
      str_putc(S, '{'); str_long(S, e); str_putc(S, '}');
    }
  }
}
static void
wrexpo(outString *S, long e)
{
  if (e != 1) { str_putc(S, '^'); str_long(S, e); }
}

/* v^e */
static void
VpowE(outString *S, const char *v, long e) { str_puts(S, v); wrexpo(S,e); }
static void
texVpowE(outString *S, const char *v, long e) {
  str_puts(S, v); texexpo(S,e);
}
static void
monome(outString *S, const char *v, long e)
{
  if (e) VpowE(S, v, e); else str_putc(S, '1');
}
static void
texnome(outString *S, const char *v, long e)
{
  if (e) texVpowE(S, v, e); else str_putc(S, '1');
}

/* ( a ) */
static void
paren(pariout_t *T, outString *S, GEN a)
{
  str_putc(S, '('); bruti(a,T,S); str_putc(S, ')');
}
static void
texparen(pariout_t *T, outString *S, GEN a)
{
  if (T->TeXstyle & TEXSTYLE_PAREN)
    str_puts(S, " (");
  else
    str_puts(S, " \\left(");
  texi(a,T,S);
  if (T->TeXstyle & TEXSTYLE_PAREN)
    str_puts(S, ") ");
  else
    str_puts(S, "\\right) ");
}

/* * v^d */
static void
times_texnome(outString *S, const char *v, long d)
{
  if (d)
  {
    if (GP_DATA->flags & TEXMACS) str_puts(S, "\\*"); else str_putc(S, ' ');
    texnome(S,v,d);
  }
}
static void
times_monome(outString *S, const char *v, long d)
{
  if (d) { str_putc(S, '*'); monome(S,v,d); }
}

/* write a * v^d */
static void
wr_monome(pariout_t *T, outString *S, GEN a, const char *v, long d)
{
  long sig = isone(a);

  if (sig) {
    sp_sign_sp(T,S,sig); monome(S,v,d);
  } else {
    sig = isfactor(a);
    if (sig) { sp_sign_sp(T,S,sig); bruti_sign(a,T,S,0); }
    else { sp_sign_sp(T,S,1); paren(T,S, a); }
    times_monome(S, v, d);
  }
}
static void
wr_texnome(pariout_t *T, outString *S, GEN a, const char *v, long d)
{
  long sig = isone(a);

  str_putc(S, '\n'); /* Avoid TeX buffer overflow */
  if (T->TeXstyle & TEXSTYLE_BREAK) str_puts(S, "\\PARIbreak ");

  if (sig) {
    putsigne(S,sig); texnome(S,v,d);
  } else {
    sig = isfactor(a);
    if (sig) { putsigne(S,sig); texi_sign(a,T,S,0); }
    else { str_puts(S, " +"); texparen(T,S, a); }
    times_texnome(S, v, d);
  }
}

static void
wr_lead_monome(pariout_t *T, outString *S, GEN a,const char *v, long d, int addsign)
{
  long sig = isone(a);
  if (sig) {
    if (addsign && sig<0) str_putc(S, '-');
    monome(S,v,d);
  } else {
    if (isfactor(a)) bruti_sign(a,T,S,addsign);
    else paren(T,S, a);
    times_monome(S, v, d);
  }
}
static void
wr_lead_texnome(pariout_t *T, outString *S, GEN a,const char *v, long d, int addsign)
{
  long sig = isone(a);
  if (sig) {
    if (addsign && sig<0) str_putc(S, '-');
    texnome(S,v,d);
  } else {
    if (isfactor(a)) texi_sign(a,T,S,addsign);
    else texparen(T,S, a);
    times_texnome(S, v, d);
  }
}

static void
prints(GEN g, pariout_t *T, outString *S)
{ (void)T; str_long(S, (long)g); }

static void
quote_string(outString *S, char *s)
{
  str_putc(S, '"');
  while (*s)
  {
    char c=*s++;
    if (c=='\\' || c=='"' || c=='\033' || c=='\n' || c=='\t')
    {
      str_putc(S, '\\');
      switch(c)
      {
      case '\\': case '"': break;
      case '\n':   c='n'; break;
      case '\033': c='e'; break;
      case '\t':   c='t'; break;
      }
    }
    str_putc(S, c);
  }
  str_putc(S, '"');
}

static int
print_0_or_pm1(GEN g, outString *S, int addsign)
{
  long r;
  if (!g) { str_puts(S, "NULL"); return 1; }
  if (isnull(g)) { str_putc(S, '0'); return 1; }
  r = isone(g);
  if (r)
  {
    if (addsign && r<0) str_putc(S, '-');
    str_putc(S, '1'); return 1;
  }
  return 0;
}

static void
bruti_intern(GEN g, pariout_t *T, outString *S, int addsign)
{
  long l,i,j,r, tg = typ(g);
  GEN a,b;
  const char *v;
  char buf[32];

  switch(tg)
  {
    case t_INT:
      if (addsign && signe(g) < 0) str_putc(S, '-');
      str_absint(S, g); break;
    case t_REAL:
    {
      pari_sp av = avma;
      if (addsign && signe(g) < 0) str_putc(S, '-');
      str_puts(S, absrtostr(g, T->sp, toupper(T->format), T->sigd) );
      avma = av; break;
    }

    case t_INTMOD: case t_POLMOD:
      str_puts(S, new_fun_set? "Mod(": "mod(");
      bruti(gel(g,2),T,S); comma_sp(T,S);
      bruti(gel(g,1),T,S); str_putc(S, ')'); break;

    case t_FFELT:
      bruti_sign(FF_to_FpXQ_i(g),T,S,addsign);
      break;

    case t_FRAC: case t_RFRAC:
      r = isfactor(gel(g,1)); if (!r) str_putc(S, '(');
      bruti_sign(gel(g,1),T,S,addsign);
      if (!r) str_putc(S, ')');
      str_putc(S, '/');
      r = isdenom(gel(g,2)); if (!r) str_putc(S, '(');
      bruti(gel(g,2),T,S);
      if (!r) str_putc(S, ')');
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = gel(g,r+1); b = gel(g,r+2); v = r? "w": "I";
      if (isnull(a))
      {
	wr_lead_monome(T,S,b,v,1,addsign);
	return;
      }
      bruti_sign(a,T,S,addsign);
      if (!isnull(b)) wr_monome(T,S,b,v,1);
      break;

    case t_POL: v = get_var(varn(g), buf);
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      wr_lead_monome(T,S,gel(g,i),v,i,addsign);
      while (i--)
      {
	a = gel(g,i);
	if (!isnull_for_pol(a)) wr_monome(T,S,a,v,i);
      }
      break;

    case t_SER: v = get_var(varn(g), buf);
      i = valp(g);
      if (lgpol(g))
      { /* hack: we want g[i] = coeff of degree i. */
	l = i + lgpol(g); g -= i-2;
	wr_lead_monome(T,S,gel(g,i),v,i,addsign);
	while (++i < l)
	{
	  a = gel(g,i);
	  if (!isnull_for_pol(a)) wr_monome(T,S,a,v,i);
	}
	sp_sign_sp(T,S,1);
      }
      str_puts(S, "O("); monome(S,v,i); str_putc(S, ')'); break;

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
	    str_absint(S, a); if (i) str_putc(S, '*');
	  }
	  if (i) VpowE(S, ev,i);
	  sp_sign_sp(T,S,1);
	}
	if ((i & 0xff) == 0) g = gerepileuptoint(av,g);
      }
      str_puts(S, "O("); VpowE(S, ev,i); str_putc(S, ')');
      pari_free(ev); break;
    }

    case t_QFR: case t_QFI: r = (tg == t_QFR);
      if (new_fun_set) str_puts(S, "Qfb("); else str_puts(S, r? "qfr(": "qfi(");
      bruti(gel(g,1),T,S); comma_sp(T,S);
      bruti(gel(g,2),T,S); comma_sp(T,S);
      bruti(gel(g,3),T,S);
      if (r) { comma_sp(T,S); bruti(gel(g,4),T,S); }
      str_putc(S, ')'); break;

    case t_VEC: case t_COL:
      str_putc(S, '['); l = lg(g);
      for (i=1; i<l; i++)
      {
	bruti(gel(g,i),T,S);
	if (i<l-1) comma_sp(T,S);
      }
      str_putc(S, ']'); if (tg==t_COL) str_putc(S, '~');
      break;
    case t_VECSMALL: wr_vecsmall(T,S,g); break;

    case t_LIST:
      str_puts(S, "List([");
      g = list_data(g);
      l = g? lg(g): 1;
      for (i=1; i<l; i++)
      {
	bruti(gel(g,i),T,S);
	if (i<l-1) comma_sp(T,S);
      }
      str_puts(S, "])"); break;

    case t_STR:
      quote_string(S, GSTR(g)); break;

    case t_CLOSURE:
      if (lg(g)>=6)
      {
        if (typ(g[5])==t_STR)
          str_puts(S, GSTR(gel(g,5)));
        else
        {
          str_putc(S,'(');   str_puts(S,GSTR(gmael(g,5,1)));
          str_puts(S,")->"); str_puts(S,GSTR(gmael(g,5,2)));
        }
      }
      else
      {
        str_puts(S,"{\""); str_puts(S,GSTR(gel(g,2)));
        str_puts(S,"\","); wr_vecsmall(T,S,gel(g,3));
        str_putc(S,',');   bruti(gel(g,4),T,S); str_putc(S,'}');
      }
      break;

    case t_MAT:
    {
      OUT_FUN print;

      r = lg(g); if (r==1) { str_puts(S, "[;]"); return; }
      l = lg(g[1]);
      if (l==1)
      {
	str_puts(S, "matrix(0,");
        str_long(S, r-1);
        if (new_fun_set)
          str_putc(S, ')');
        else
	  str_puts(S, ",j,k,0)");
	return;
      }
      print = (typ(g[1]) == t_VECSMALL)? prints: bruti;
      if (l==2)
      {
	str_puts(S, new_fun_set? "Mat(": "mat(");
	if (r == 2) { print(gcoeff(g,1,1),T,S); str_putc(S, ')'); return; }
      }
      str_putc(S, '[');
      for (i=1; i<l; i++)
      {
	for (j=1; j<r; j++)
	{
	  print(gcoeff(g,i,j),T,S);
	  if (j<r-1) comma_sp(T,S);
	}
	if (i<l-1) { str_putc(S, ';'); if (T->sp) str_putc(S, ' '); }
      }
      str_putc(S, ']'); if (l==2) str_putc(S, ')');
      break;
    }

    default: str_addr(S, *g);
  }
}

static void
bruti_sign(GEN g, pariout_t *T, outString *S, int addsign)
{
  if (!print_0_or_pm1(g, S, addsign))
    bruti_intern(g, T, S, addsign);
}

static void
matbruti(GEN g, pariout_t *T, outString *S)
{
  long i, j, r, l;
  OUT_FUN print;

  if (typ(g) != t_MAT) { bruti(g,T,S); return; }

  r=lg(g); if (r==1 || lg(g[1])==1) { str_puts(S, "[;]"); return; }
  l = lg(g[1]); str_putc(S, '\n');
  print = (typ(g[1]) == t_VECSMALL)? prints: bruti;
  for (i=1; i<l; i++)
  {
    str_putc(S, '[');
    for (j=1; j<r; j++)
    {
      print(gcoeff(g,i,j),T,S); if (j<r-1) str_putc(S, ' ');
    }
    if (i<l-1) str_puts(S, "]\n\n"); else str_puts(S, "]\n");
  }
}

/********************************************************************/
/**                                                                **/
/**                           TeX OUTPUT                           **/
/**                                                                **/
/********************************************************************/
/* this follows bruti_sign */
static void
texi_sign(GEN g, pariout_t *T, outString *S, int addsign)
{
  long tg,i,j,l,r;
  GEN a,b;
  const char *v;
  char buf[67];

  if (print_0_or_pm1(g, S, addsign)) return;

  tg = typ(g);
  switch(tg)
  {
    case t_INT: case t_REAL: case t_QFR: case t_QFI:
      bruti_intern(g, T, S, addsign); break;

    case t_INTMOD: case t_POLMOD:
      texi(gel(g,2),T,S); str_puts(S, " mod ");
      texi(gel(g,1),T,S); break;

    case t_FRAC:
      if (addsign && isfactor(gel(g,1)) < 0) str_putc(S, '-');
      str_puts(S, "\\frac{");
      texi_sign(gel(g,1),T,S,0);
      str_puts(S, "}{");
      texi_sign(gel(g,2),T,S,0);
      str_puts(S, "}"); break;

    case t_RFRAC:
      str_puts(S, "\\frac{");
      texi(gel(g,1),T,S); /* too complicated otherwise */
      str_puts(S, "}{");
      texi(gel(g,2),T,S);
      str_puts(S, "}"); break;

    case t_FFELT:
      bruti_sign(FF_to_FpXQ_i(g),T,S,addsign);
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      a = gel(g,r+1); b = gel(g,r+2); v = r? "w": "I";
      if (isnull(a))
      {
	wr_lead_texnome(T,S,b,v,1,addsign);
	break;
      }
      texi_sign(a,T,S,addsign);
      if (!isnull(b)) wr_texnome(T,S,b,v,1);
      break;

    case t_POL: v = get_texvar(varn(g), buf, sizeof(buf));
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      wr_lead_texnome(T,S,gel(g,i),v,i,addsign);
      while (i--)
      {
	a = gel(g,i);
	if (!isnull_for_pol(a)) wr_texnome(T,S,a,v,i);
      }
      break;

    case t_SER: v = get_texvar(varn(g), buf, sizeof(buf));
      i = valp(g);
      if (lgpol(g))
      { /* hack: we want g[i] = coeff of degree i. */
	l = i + lgpol(g); g -= i-2;
	wr_lead_texnome(T,S,gel(g,i),v,i,addsign);
	while (++i < l)
	{
	  a = gel(g,i);
	  if (!isnull_for_pol(a)) wr_texnome(T,S,a,v,i);
	}
	str_puts(S, "+ ");
      }
      str_puts(S, "O("); texnome(S,v,i); str_putc(S, ')'); break;

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
	    str_absint(S, a); if (i) str_puts(S, "\\cdot");
	  }
	  if (i) texVpowE(S, ev,i);
	  str_putc(S, '+');
	}
      }
      str_puts(S, "O("); texVpowE(S, ev,i); str_putc(S, ')');
      pari_free(ev); break;
    }

    case t_VEC:
      str_puts(S, "\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi(gel(g,i),T,S); if (i < l-1) str_putc(S, '&');
      }
      str_puts(S, "\\cr}\n"); break;

    case t_LIST:
      str_puts(S, "\\pmatrix{ ");
      g = list_data(g);
      l = g? lg(g): 1;
      for (i=1; i<l; i++)
      {
	texi(gel(g,i),T,S); if (i < l-1) str_putc(S, '&');
      }
      str_puts(S, "\\cr}\n"); break;

    case t_COL:
      str_puts(S, "\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	texi(gel(g,i),T,S); str_puts(S, "\\cr\n");
      }
      str_putc(S, '}'); break;

    case t_VECSMALL:
      str_puts(S, "\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
	str_long(S, g[i]);
	if (i < l-1) str_putc(S, '&');
      }
      str_puts(S, "\\cr}\n"); break;

    case t_STR:
      str_puts(S, GSTR(g)); break;

    case t_CLOSURE:
      if (lg(g)>=6)
      {
        if (typ(g[5])==t_STR)
          str_puts(S, GSTR(gel(g,5)));
        else
        {
          str_putc(S,'(');          str_puts(S,GSTR(gmael(g,5,1)));
          str_puts(S,")\\mapsto "); str_puts(S,GSTR(gmael(g,5,2)));
        }
      }
      else
      {
        str_puts(S,"\\{\""); str_puts(S,GSTR(gel(g,2)));
        str_puts(S,"\","); texi(gel(g,3),T,S);
        str_putc(S,',');   texi(gel(g,4),T,S); str_puts(S,"\\}");
      }
      break;

    case t_MAT:
    {
      str_puts(S, "\\pmatrix{\n "); r = lg(g);
      if (r>1)
      {
        OUT_FUN print = (typ(g[1]) == t_VECSMALL)? prints: texi;

	l = lg(g[1]);
	for (i=1; i<l; i++)
	{
	  for (j=1; j<r; j++)
	  {
	    print(gcoeff(g,i,j),T,S); if (j<r-1) str_putc(S, '&');
	  }
	  str_puts(S, "\\cr\n ");
	}
      }
      str_putc(S, '}'); break;
    }
  }
}

/*******************************************************************/
/**                                                               **/
/**                        USER OUTPUT FUNCTIONS                  **/
/**                                                               **/
/*******************************************************************/
static void
_initout(pariout_t *T, char f, long sigd, long sp)
{
  T->format = f;
  T->sigd = sigd;
  T->sp = sp;
}

static void
gen_output_fun(GEN x, pariout_t *T, OUT_FUN out)
{
  char *s = GENtostr_fun(x, T, out);
  pari_puts(s); free(s);
}

void
gen_output(GEN x, pariout_t *T)
{
  if (!T) T = GP_DATA->fmt;
  gen_output_fun(x, T, get_fun(T->prettyp));
}

void
brute(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,0);
  gen_output_fun(g, &T, &bruti);
}

void
matbrute(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,1);
  gen_output_fun(g, &T, &matbruti);
}

void
texe(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,0);
  gen_output_fun(g, &T, &texi);
}

void
output(GEN x)
{ brute(x,'g',-1); pari_putc('\n'); pari_flush(); }
void
outmat(GEN x)
{ matbrute(x,'g',-1); pari_putc('\n'); pari_flush(); }

void
fprintferr(const char* fmt, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  va_start(args, fmt); pari_vprintf(fmt,args);
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
  pariFILE *file = (pariFILE*) pari_malloc(strlen(name) + 1 + sizeof(pariFILE));
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
  pari_free(f);
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
pari_fopen_or_fail(const char *s, const char *mode)
{
  return pari_open_file(fopen(s, mode), s, mode);
}
pariFILE *
pari_fopen(const char *s, const char *mode)
{
  FILE *f = fopen(s, mode);
  return f? pari_open_file(f, s, mode): NULL;
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
  return pari_fopen_or_fail(s, mode);
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

/* Remove one INFILE from the stack. Reset pari_infile (to the most recent
 * infile)
 * Return -1, if we're trying to pop out stdin itself; 0 otherwise
 * Check for leaked file handlers (temporary files) */
int
popinfile(void)
{
  pariFILE *f;
  for (f = last_tmp_file; f; f = f->prev)
  {
    if (f->type & mf_IN) break;
    pari_warn(warner, "I/O: leaked file descriptor (%d): %s", f->type, f->name);
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
    if (last_filename) pari_free(last_filename);
    if (homedir) pari_free(homedir);
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
    flag |= mf_FALSE; pari_free(f); avma = av;
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

#if 0
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
#endif

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
_path_expand(const char *s)
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
    len = u-s; user = (char*)pari_malloc(len+1);
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
    ret = (char*)pari_malloc(strlen(dir) + strlen(u) + 1);
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
  char **x = (char **)pari_malloc(xlen * sizeof(char*));

  while (*s)
  {
    if (*s != '$') { s++; continue; }
    l = s - s0;
    if (l)
    {
      s0 = strncpy((char*)pari_malloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    if (xnum > xlen - 3) /* need room for possibly two more elts */
    {
      xlen <<= 1;
      x = (char **)pari_realloc((void*)x, xlen * sizeof(char*));
    }

    s0 = ++s; /* skip $ */
    while (is_keyword_char(*s)) s++;
    l = s - s0;
    env = strncpy((char*)pari_malloc(l+1), s0, l); env[l] = 0;
    s0 = os_getenv(env);
    if (!s0)
    {
      pari_warn(warner,"undefined environment variable: %s",env);
      s0 = (char*)"";
    }
    l = strlen(s0);
    if (l)
    {
      s0 = strncpy((char*)pari_malloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    pari_free(env); s0 = s;
  }
  l = s - s0;
  if (l)
  {
    s0 = strncpy((char*)pari_malloc(l+1), s0, l); s0[l] = 0;
    x[xnum++] = s0; len += l;
  }

  s = (char*)pari_malloc(len+1); *s = 0;
  for (i = 0; i < xnum; i++) { (void)strcat(s, x[i]); pari_free(x[i]); }
  pari_free(str); pari_free(x); return s;
}

char *
path_expand(const char *s)
{
  return _expand_env(_path_expand(s));
}

void
delete_dirs(gp_path *p)
{
  char **v = p->dirs, **dirs;
  if (v)
  {
    p->dirs = NULL; /* in case of error */
    for (dirs = v; *dirs; dirs++) pari_free(*dirs);
    pari_free(v);
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
  dirs = (char**) pari_malloc((n + 2)*sizeof(char *));

  for (s=v, i=0; i<=n; i++)
  {
    char *end = s + strlen(s), *f = end;
    while (f > s && *--f == '/') *f = 0;
    dirs[i] = path_expand(s);
    s = end + 1; /* next path component */
  }
  pari_free((void*)v);
  dirs[i] = NULL; p->dirs = dirs;
}

/* name is a malloc'ed (existing) filename. Accept it as new pari_infile
 * (unzip if needed). */
static pariFILE *
pari_get_infile(const char *name, FILE *file)
{
#ifdef ZCAT
  long l = strlen(name);
  const char *end = name + l-1;

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

pariFILE *
pari_fopengz(const char *s)
{
  pari_sp av = avma;
  char *name;
  long l;
  FILE *f = fopen(s, "r");
  pariFILE *pf;

  if (f) return pari_get_infile(s, f);

  l = strlen(s);
  name = stackmalloc(l + 3 + 1);
  strcpy(name, s); (void)sprintf(name + l, ".gz");
  f = fopen(name, "r");
  pf = f ? pari_get_infile(name, f): NULL;
  avma = av; return pf;
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
      if (last_filename) pari_free(last_filename);
      last_filename = pari_strdup(s);
    }
    file = pari_infile = pari_get_infile(s,file)->file;
  }
  pari_free(name); avma = av;
  return file;
}

/* If name = "", re-read last file */
void
switchin(const char *name0)
{
  char *s, *name;

  if (*name0)
    name = path_expand(name0);
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
      s = (char*)pari_malloc(2 + strlen(*tmp) + strlen(name));
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
  pari_free((void*)p);
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
  s = (char*)pari_malloc(L);
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
  p = (GENbin*)pari_malloc(sizeof(GENbin) + L*sizeof(long));
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

/* return 1 if valid binary file */
static int
check_magic(const char *name, FILE *f)
{
  if (!is_magic_ok(f))
    pari_warn(warner, "%s is not a GP binary file",name);
  else if (!is_sizeoflong_ok(f))
    pari_warn(warner, "%s not written for a %ld bit architecture",
	       name, sizeof(long)*8);
  else if (!is_long_ok(f, ENDIAN_CHECK))
    pari_warn(warner, "unexpected endianness in %s",name);
  else if (!is_long_ok(f, BINARY_VERSION))
    pari_warn(warner, "%s written by an incompatible version of GP",name);
  else return 1;
  return 0;
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

  if (f) {
    int ok = check_magic(name,f);
    fclose(f);
    if (!ok) pari_err(openfiler,"binary output",name);
  }
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
  if (!check_magic(name,f)) return NULL;
  x = y = z = NULL;
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
    if (vector) *vector = 1;
  }
  else
    if (vector) *vector = 0;
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
  OUT_FUN out = get_fun(flag);
  long i, l = lg(g);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(g,i);
    if (typ(x)==t_STR)
      pari_puts(GSTR(x)); /* text surrounded by "" otherwise */
    else
      gen_output_fun(x, GP_DATA->fmt, out);
  }
}

/* dummy needed to pass a (empty!) va_list to sm_dopr */
static char *
dopr_arg_vector(GEN arg_vector, const char* fmt, ...)
{
  va_list ap;
  char *s;
  va_start(ap, fmt);
  s = sm_dopr(fmt, arg_vector, ap);
  va_end(ap); return s;
}
/* GP only */
void
printf0(GEN gfmt, GEN args)
{ char *s = dopr_arg_vector(args, (const char*)gfmt);
  pari_puts(s); free(s); }
/* GP only */
GEN
Strprintf(GEN gfmt, GEN args)
{ char *s = dopr_arg_vector(args, (const char *)gfmt);
  GEN z = strtoGENstr(s); free(s); return z; }

void
pari_vprintf(const char *fmt, va_list ap)
{
  char *s = sm_dopr(fmt, NULL, ap);
  pari_puts(s); free(s);
}
void
pari_printf(const char *fmt, ...) /* variadic version of printf0 */
{
  va_list args; va_start(args,fmt);
  pari_vprintf(fmt,args); va_end(args);
}

char *
pari_vsprintf(const char *fmt, va_list ap)
{ return sm_dopr(fmt, NULL, ap); }
char *
pari_sprintf(const char *fmt, ...) /* variadic version of Strprintf */
{
  char *s;
  va_list ap; va_start(ap, fmt);
  s = pari_vsprintf(fmt, ap); va_end(ap); return s;
}

/* variadic version of fprintf0. FIXME: fprintf0 not yet available */
void
pari_vfprintf(FILE *file, const char *fmt, va_list ap)
{
  char *s = sm_dopr(fmt, NULL, ap);
  fputs(s, file); free(s);
}
void
pari_fprintf(FILE *file, const char *fmt, ...)
{
  va_list ap; va_start(ap, fmt);
  pari_vfprintf(file, fmt, ap); va_end(ap);
}

void print   (GEN g) { print0(g, f_RAW);       pari_putc('\n'); pari_flush(); }
void printtex(GEN g) { print0(g, f_TEX);       pari_putc('\n'); pari_flush(); }
void print1  (GEN g) { print0(g, f_RAW);       pari_flush(); }

void error0(GEN g) { pari_err(user, g); }
void warning0(GEN g) { pari_warn(user, g); }

static char *
wr_check(const char *s) {
  char *t = path_expand(s);
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
static void
wr_init(const char *s)
{
  char *t = wr_check(s);
  switchout(t); pari_free(t);
  wr_last_was_newline = pari_last_was_newline();
}

/* End writing to file s, go back to stdout */
static void
wr_finish()
{
  pari_flush(); switchout(NULL);
  pari_set_last_newline(wr_last_was_newline);
}

#define WR_NL() pari_putc('\n'); wr_finish()
#define WR_NO() wr_finish()

void write0  (const char *s, GEN g) { wr_init(s); print0(g, f_RAW); WR_NL(); }
void writetex(const char *s, GEN g) { wr_init(s); print0(g, f_TEX); WR_NL(); }
void write1  (const char *s, GEN g) { wr_init(s); print0(g, f_RAW); WR_NO(); }

void gpwritebin(const char *s, GEN x) { char *t=wr_check(s); writebin(t, x); pari_free(t);}

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
    sprintf(str, "History result %%%ld not available [%%%ld-%%%lu]", p,pmin,t);
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
  buf = (char*) pari_malloc(lpre + 1 + 8 + lsuf + 1);
  strcpy(buf, pre);
  if (buf[lpre-1] != '/') { (void)strcat(buf, "/"); lpre++; }
  swap_slash(buf);

  sprintf(buf + lpre, "%.8s%s", s, suf);
  return buf;
}

/* Return a "unique filename" built from the string s, possibly the user id
 * and the process pid (on Unix systems). A "temporary" directory name is
 * prepended. The name returned is pari_malloc'ed. It is DOS-safe
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
 * directory name is prepended. The name returned is pari_malloc'ed.
 * It is DOS-safe (truncated to 8 chars) */
char*
pari_unique_dir(const char *s)
{
  char *buf = init_unique(s);
  if (pari_dir_exists(buf) && !get_file(buf, pari_dir_exists))
    pari_err(talker,"couldn't find a suitable name for a tempdir (%s)",s);
  return buf;
}
