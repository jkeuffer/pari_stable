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
#include "pari.h"
#include "paripriv.h"
#include "anal.h"

#ifdef HAS_STRFTIME
#  include <time.h>
#endif

/* Simple-minded parsing utilities. These are forbidden to use the GP stack
 * which may not exist at this point [e.g upon GP initialization]  */

#ifdef MAXPATHLEN
#  define GET_SEP_SIZE MAXPATHLEN
#else
#  define GET_SEP_SIZE 128
#endif

/* Return all chars, up to next separator
 * [as strtok but must handle verbatim character string] */
char*
get_sep(const char *t)
{
  static char buf[GET_SEP_SIZE], *lim = buf + GET_SEP_SIZE;
  char *s = buf;
  int outer = 1;

  for(;;)
  {
    switch(*s++ = *t++)
    {
      case '"':
        outer = !outer; break;
      case '\0':
        return buf;
      case ';':
        if (outer) { s[-1] = 0; return buf; }
        break;
      case '\\': /* gobble next char */
        if (s == lim) break;
        if (! (*s++ = *t++) ) return buf;
    }
    if (s == lim)
      pari_err(talker,"get_sep: argument too long (< %ld chars)", GET_SEP_SIZE);
  }
}

static ulong
safe_mul(ulong x, ulong y)
{
  ulong z;
  LOCAL_HIREMAINDER;
  z = mulll(x, y);
  return hiremainder? 0: z;
}

/* "atoul" + optional [kmg] suffix */
static ulong
my_int(char *s)
{
  ulong n = 0;
  char *p = s;

  while (isdigit((int)*p)) {
    ulong m;
    if (n > (~0UL / 10)) pari_err(talker2,"integer too large",s,s);
    n *= 10; m = n;
    n += *p++ - '0';
    if (n < m) pari_err(talker2,"integer too large",s,s);
  }
  if (n)
  {
    switch(*p)
    {
      case 'k': case 'K': n = safe_mul(n,1000UL);       p++; break;
      case 'm': case 'M': n = safe_mul(n,1000000UL);    p++; break;
      case 'g': case 'G': n = safe_mul(n,1000000000UL); p++; break;
    }
    if (!n) pari_err(talker2,"integer too large",s,s);
  }
  if (*p) pari_err(talker2,"I was expecting an integer here", s, s);
  return n;
}

long
get_int(const char *s, long dflt)
{
  char *p = get_sep(s);
  long n;
  int minus = 0;

  if (*p == '-') { minus = 1; p++; }
  if (!isdigit((int)*p)) return dflt;

  n = (long)my_int(p);
  if (n < 0) pari_err(talker2,"integer too large",s,s);
  return minus? -n: n;
}

ulong
get_uint(const char *s)
{
  char *p = get_sep(s);
  if (*p == '-') pari_err(talker2,"arguments must be positive integers",s,s);
  return my_int(p);
}

/********************************************************************/
/*                                                                  */
/*                            DEFAULTS                              */
/*                                                                  */
/********************************************************************/
static void
init_hist(gp_data *D, size_t l, ulong total)
{
  gp_hist *H = D->hist;
  H->total = total;
  H->size = l;
  H->res = (GEN *) pari_calloc(l * sizeof(GEN));
}

static void
init_path(gp_data *D)
{
  gp_path *path = D->path;
  path->PATH = pari_strdup(pari_default_path());
  path->dirs = NULL;
}

static void
init_help(gp_data *D)
{
  char *h = os_getenv("GPHELP");
# ifdef GPHELP
  if (!h) h = (char*)GPHELP;
# endif
  if (h) h = pari_strdup(h);
  D->help = h;
}

static void
init_fmt(gp_data *D)
{
#ifdef LONG_IS_64BIT
  static pariout_t DFLT_OUTPUT = { 'g', 38, 1, f_PRETTYMAT, 0 };
#else
  static pariout_t DFLT_OUTPUT = { 'g', 28, 1, f_PRETTYMAT, 0 };
#endif
  D->fmt = &DFLT_OUTPUT;
}

static const char *DFT_PRETTYPRINTER = "tex2mail -TeX -noindent -ragged -by_par";
static void
init_pp(gp_data *D)
{
  gp_pp *p = D->pp;
  p->cmd = pari_strdup(DFT_PRETTYPRINTER);
  p->file = NULL;
}

static void
do_strftime(const char *s, char *buf, long max)
{
#ifdef HAS_STRFTIME
  time_t t = time(NULL);
  (void)strftime(buf,max,s,localtime(&t));
#else
  strcpy(buf,s);
#endif
}

/**************************************************************************/

long
getrealprecision(void)
{
  return GP_DATA->fmt->sigd;
}

long
setrealprecision(long n, long *prec)
{
  GP_DATA->fmt->sigd = n;
  *prec = precreal = ndec2prec(n);
  return n;
}

static GEN
sd_toggle(const char *v, long flag, const char *s, int *ptn)
{
  int state = *ptn;
  if (*v)
  {
    int n = (int)get_int(v,0);
    if (n == state) return gnil;
    if (n != !state)
    {
      char *t = stackmalloc(64 + strlen(s));
      (void)sprintf(t, "default: incorrect value for %s [0:off / 1:on]", s);
      pari_err(talker2, t, v,v);
    }
    state = *ptn = n;
  }
  switch(flag)
  {
    case d_RETURN: return utoi(state);
    case d_ACKNOWLEDGE:
      if (state) pari_printf("   %s = 1 (on)\n", s);
      else       pari_printf("   %s = 0 (off)\n", s);
      break;
  }
  return gnil;
}

static GEN
sd_gptoggle(const char *v, long flag, const char *s, ulong FLAG)
{
  int n = (GP_DATA->flags & FLAG)? 1: 0, old = n;
  GEN z = sd_toggle(v, flag, s, &n);
  if (n != old)
  {
    if (n) GP_DATA->flags |=  FLAG;
    else   GP_DATA->flags &= ~FLAG;
  }
  return z;
}

static void
sd_ulong_init(const char *v, const char *s, ulong *ptn, ulong Min, ulong Max)
{
  if (*v)
  {
    ulong n = get_uint(v);
    if (n > Max || n < Min)
    {
      char *buf = stackmalloc(strlen(s) + 2 * 20 + 40);
      (void)sprintf(buf, "default: incorrect value for %s [%lu-%lu]",
                    s, Min, Max);
      pari_err(talker2, buf, v,v);
    }
    *ptn = n;
  }
}

static GEN
sd_ulong(const char *v, long flag, const char *s, ulong *ptn, ulong Min, ulong Max,
         const char **msg)
{
  ulong n = *ptn;
  sd_ulong_init(v, s, ptn, Min, Max);
  switch(flag)
  {
    case d_RETURN:
      return utoi(*ptn);
    case d_ACKNOWLEDGE:
      if (!*v || *ptn != n) {
        if (msg)
        {
          if (!*msg) msg++; /* single msg, always printed */
          else       msg += *ptn; /* one per possible value */
          pari_printf("   %s = %lu %s\n", s, *ptn, *msg);
        }
        else
          pari_printf("   %s = %lu\n", s, *ptn);
      }
      break;
  }
  return gnil;
}

GEN
sd_realprecision(const char *v, long flag)
{
  pariout_t *fmt = GP_DATA->fmt;
  if (*v)
  {
    ulong newnb = fmt->sigd, prec;
    sd_ulong_init(v, "realprecision", &newnb, 1, prec2ndec(LGBITS));
    if (fmt->sigd == (long)newnb) return gnil;
    if (fmt->sigd >= 0) fmt->sigd = newnb;
    prec = (ulong)ndec2prec(newnb);
    if (prec == precreal) return gnil;
    precreal = prec;
  }
  if (flag == d_RETURN) return stoi(fmt->sigd);
  if (flag == d_ACKNOWLEDGE)
  {
    long n = prec2ndec(precreal);
    pari_printf("   realprecision = %ld significant digits", n);
    if (fmt->sigd < 0)
      pari_puts(" (all digits displayed)");
    else if (n != fmt->sigd)
      pari_printf(" (%ld digits displayed)", fmt->sigd);
    pari_putc('\n');
  }
  return gnil;
}

GEN
sd_seriesprecision(const char *v, long flag)
{
  const char *msg[] = {NULL, "significant terms"};
  return sd_ulong(v,flag,"seriesprecision",&precdl, 1,LGBITS,msg);
}

GEN
sd_format(const char *v, long flag)
{
  pariout_t *fmt = GP_DATA->fmt;
  if (*v)
  {
    char c = *v;
    if (c!='e' && c!='f' && c!='g')
      pari_err(talker2,"default: inexistent format",v,v);
    fmt->format = c; v++;

    if (isdigit((int)*v))
      { while (isdigit((int)*v)) v++; } /* FIXME: skip obsolete field width */
    if (*v++ == '.')
    {
      if (*v == '-') fmt->sigd = -1;
      else
        if (isdigit((int)*v)) fmt->sigd=atol(v);
    }
  }
  if (flag == d_RETURN)
  {
    char *s = stackmalloc(64);
    (void)sprintf(s, "%c.%ld", fmt->format, fmt->sigd);
    return strtoGENstr(s);
  }
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   format = %c.%ld\n", fmt->format, fmt->sigd);
  return gnil;
}

static long
gp_get_color(char **st)
{
  char *s, *v = *st;
  int trans;
  long c;
  if (isdigit((int)*v))
    { c = atol(v); trans = 1; } /* color on transparent background */
  else
  {
    if (*v == '[')
    {
      const char *a[3];
      long i = 0;
      for (a[0] = s = ++v; *s && *s != ']'; s++)
        if (*s == ',') { *s = 0; a[++i] = s+1; }
      if (*s != ']') pari_err(talker2,"expected character: ']'",s, *st);
      *s = 0; for (i++; i<3; i++) a[i] = "";
      /*    properties    |   color    | background */
      c = (atoi(a[2])<<8) | atoi(a[0]) | (atoi(a[1])<<4);
      trans = (*(a[1]) == 0);
      v = s + 1;
    }
    else { c = c_NONE; trans = 0; }
  }
  if (trans) c = c | (1L<<12);
  while (*v && *v++ != ',') /* empty */;
  if (c != c_NONE) disable_color = 0;
  *st = v; return c;
}

/* 1: error, 2: history, 3: prompt, 4: input, 5: output, 6: help, 7: timer */
GEN
sd_colors(const char *v, long flag)
{
  long c,l;
  if (*v && !(GP_DATA->flags & (EMACS|TEXMACS)))
  {
    char *v0, *s;
    disable_color=1;
    l = strlen(v);
    if (l <= 2 && strncmp(v, "no", l) == 0)
      v = "";
    if (l <= 6 && strncmp(v, "darkbg", l) == 0)
      v = "1, 5, 3, 7, 6, 2, 3"; /* Assume recent ReadLine. */
    if (l <= 7 && strncmp(v, "lightbg", l) == 0)
      v = "1, 6, 3, 4, 5, 2, 3"; /* Assume recent ReadLine. */
    if (l <= 6 && strncmp(v, "boldfg", l) == 0)        /* Good for darkbg consoles */
      v = "[1,,1], [5,,1], [3,,1], [7,,1], [6,,1], , [2,,1]";
    v0 = s = filtre(v, 0);
    for (c=c_ERR; c < c_LAST; c++)
      gp_colors[c] = gp_get_color(&s);
    pari_free(v0);
  }
  if (flag == d_ACKNOWLEDGE || flag == d_RETURN)
  {
    char s[128], *t = s;
    long col[3], n;
    for (*t=0,c=c_ERR; c < c_LAST; c++)
    {
      n = gp_colors[c];
      if (n == c_NONE)
        sprintf(t,"no");
      else
      {
        decode_color(n,col);
        if (n & (1L<<12))
        {
          if (col[0])
            sprintf(t,"[%ld,,%ld]",col[1],col[0]);
          else
            sprintf(t,"%ld",col[1]);
        }
        else
          sprintf(t,"[%ld,%ld,%ld]",col[1],col[2],col[0]);
      }
      t += strlen(t);
      if (c < c_LAST - 1) { *t++=','; *t++=' '; }
    }
    if (flag==d_RETURN) return strtoGENstr(s);
    pari_printf("   colors = \"%s\"\n",s);
  }
  return gnil;
}

static long
atocolor(const char *s)
{
  long l = atol(s);
  if (l <   0) l =   0;
  if (l > 255) l = 255;
  return l;
}

GEN
sd_graphcolormap(const char *v, long flag)
{
  char *p, *q;
  long i, j, l, a, s, *lp;

  if (*v)
  {
    char *t = filtre(v, 0);
    if (*t != '[' || t[strlen(t)-1] != ']')
      pari_err(talker2, "incorrect value for graphcolormap", t, t);
    for (s = 0, p = t+1, l = 2, a=0; *p; p++)
      if (*p == '[')
      {
        a++;
        while (*++p != ']')
          if (!*p || *p == '[')
            pari_err(talker2, "incorrect value for graphcolormap", p, t);
      }
      else if (*p == '"')
      {
        s += sizeof(long)+1;
        while (*p && *++p != '"') s++;
        if (!*p) pari_err(talker2, "incorrect value for graphcolormap", p, t);
        s = (s+sizeof(long)-1) & ~(sizeof(long)-1);
      }
      else if (*p == ',')
        l++;
    if (l < 4)
      pari_err(talker, "too few colors (< 4) in graphcolormap");
    if (pari_colormap) pari_free(pari_colormap);
    pari_colormap = (GEN)pari_malloc((l+4*a)*sizeof(long) + s);
    pari_colormap[0] = evaltyp(t_VEC)|evallg(l);
    for (p = t+1, i = 1, lp = pari_colormap+l; i < l; p++)
      switch(*p)
      {
      case '"':
        gel(pari_colormap, i) = lp;
        q = ++p; while (*q != '"') q++;
        *q = 0;
        j = 1 + nchar2nlong(q-p+1);
        lp[0] = evaltyp(t_STR)|evallg(j);
        strncpy(GSTR(lp), p, q-p+1);
        lp += j; p = q;
        break;
      case '[': {
        const char *ap[3];
        gel(pari_colormap, i) = lp;
        lp[0] = evaltyp(t_VECSMALL)|_evallg(4);
        for (ap[0] = ++p, j=0; *p && *p != ']'; p++)
          if (*p == ',' && j<2) { *p++ = 0; ap[++j] = p; }
        while (j<2) ap[++j] = "0";
        if (j>2 || *p != ']')
        {
          char buf[100];
          sprintf(buf, "incorrect value for graphcolormap[%ld]: ", i);
          pari_err(talker2, buf, p, t);
        }
        *p = '\0';
        lp[1] = atocolor(ap[0]);
        lp[2] = atocolor(ap[1]);
        lp[3] = atocolor(ap[2]);
        lp += 4;
        break;
      }
      case ',':
      case ']':
        i++;
        break;
      default:
        pari_err(talker2, "incorrect value for graphcolormap", p, t);
      }
    free(t);
  }
  if (flag == d_RETURN || flag == d_ACKNOWLEDGE)
  {
    GEN cols = cgetg(lg(pari_colormap), t_VEC);
    long i;

    for (i = 1; i < lg(cols); i++)
    {
      GEN c = gel(pari_colormap, i);
      if (typ(c) == t_STR)
        gel(cols, i) = gcopy(c);
      else
        gel(cols, i) = vecsmall_to_vec(c);
    }
    if (flag == d_RETURN) return cols;
    pari_printf("   graphcolormap = %Ps\n", cols);
  }
  return gnil;
}

GEN
sd_graphcolors(const char *v, long flag)
{
  long i, l;
  char *p;

  if (*v) {
    char *t = filtre(v, 0);
    for (p = t+1, l=2; *p != ']'; p++)
      if (*p == ',') l++;
      else if (*p < '0' || *p > '9')
        pari_err(talker2, "incorrect value for graphcolors", p, t);
    if (*++p) pari_err(talker2, "incorrect value for graphcolors", p, t);
    if (pari_graphcolors) pari_free(pari_graphcolors);
    pari_graphcolors = cgetalloc(t_VECSMALL, l);
    for (p = t+1, i=0; *p; p++)
    {
      long n = 0;
      while (*p >= '0' && *p <= '9')
      {
        n *= 10;
        n += *p-'0';
        p++;
      }
      pari_graphcolors[++i] = n;
    }
    free(t);
  }
  switch(flag)
  {
  case d_RETURN:
    return vecsmall_to_vec(pari_graphcolors);
  case d_ACKNOWLEDGE:
    pari_printf("   graphcolors = %Ps\n", vecsmall_to_vec(pari_graphcolors));
  }
  return gnil;
}

GEN
sd_compatible(const char *v, long flag)
{
  const char *msg[] = {
    "(no backward compatibility)",
    "(warn when using obsolete functions)",
    "(use old functions, don't ignore case)",
    "(use old functions, ignore case)", NULL
  };
  ulong old = compatible;
  GEN r = sd_ulong(v,flag,"compatible",&compatible, 0,3,msg);

  if (old != compatible && flag != d_INITRC && gp_init_functions())
    pari_warn(warner,"user functions re-initialized");
  return r;
}

GEN
sd_secure(const char *v, long flag)
{
  if (*v && (GP_DATA->flags & SECURE))
    pari_ask_confirm("[secure mode]: About to modify the 'secure' flag");
  return sd_gptoggle(v,flag,"secure", SECURE);
}

static THREAD long dbg = -1;
void
dbg_block() { if (DEBUGLEVEL) { dbg = DEBUGLEVEL; DEBUGLEVEL = 0; } }
void
dbg_release() { if (dbg >= 0) { DEBUGLEVEL = dbg; dbg = -1; } }

GEN
sd_debug(const char *v, long flag)
{ return sd_ulong(v,flag,"debug",&DEBUGLEVEL, 0,20,NULL); }

ulong readline_state = DO_ARGS_COMPLETE;

GEN
sd_rl(const char *v, long flag)
{
  const char *msg[] = {NULL,
        "(bits 0x2/0x4 control matched-insert/arg-complete)"};
  ulong o_readline_state = readline_state;
  GEN res = sd_ulong(v,flag,"readline", &readline_state, 0, 7, msg);

  if (o_readline_state != readline_state)
    (void)sd_gptoggle(readline_state? "1": "0", d_SILENT, "readline", USE_READLINE);
  return res;
}

GEN
sd_debugfiles(const char *v, long flag)
{ return sd_ulong(v,flag,"debugfiles",&DEBUGFILES, 0,20,NULL); }

GEN
sd_debugmem(const char *v, long flag)
{ return sd_ulong(v,flag,"debugmem",&DEBUGMEM, 0,20,NULL); }

GEN
sd_breakloop(const char *v, long flag)
{ return sd_gptoggle(v,flag,"breakloop", BREAKLOOP); }

GEN
sd_echo(const char *v, long flag)
{ return sd_gptoggle(v,flag,"echo", ECHO); }

GEN
sd_recover(const char *v, long flag)
{ return sd_gptoggle(v,flag,"recover", RECOVER); }

GEN
sd_lines(const char *v, long flag)
{ return sd_ulong(v,flag,"lines",&(GP_DATA->lim_lines), 0,LONG_MAX,NULL); }

GEN
sd_histsize(const char *v, long flag)
{
  gp_hist *H = GP_DATA->hist;
  ulong n = H->size;
  GEN r = sd_ulong(v,flag,"histsize",&n, 1,
                     (LONG_MAX / sizeof(long)) - 1,NULL);
  if (n != H->size)
  {
    const ulong total = H->total;
    long g, h, k, kmin;
    GEN *resG = H->res, *resH; /* G = old data, H = new one */
    size_t sG = H->size, sH;

    init_hist(GP_DATA, n, total);
    if (!total) return r;

    resH = H->res;
    sH   = H->size;
    /* copy relevant history entries */
    g     = (total-1) % sG;
    h = k = (total-1) % sH;
    kmin = k - minss(sH, sG);
    for ( ; k > kmin; k--, g--, h--)
    {
      resH[h] = resG[g];
      resG[g] = NULL;
      if (!g) g = sG;
      if (!h) h = sH;
    }
    /* clean up */
    for ( ; resG[g]; g--)
    {
      gunclone(resG[g]);
      if (!g) g = sG;
    }
    pari_free((void*)resG);
  }
  return r;
}

static void
TeX_define(const char *s, const char *def) {
  fprintf(pari_logfile, "\\ifx\\%s\\undefined\n  \\def\\%s{%s}\\fi\n", s,s,def);
}
static void
TeX_define2(const char *s, const char *def) {
  fprintf(pari_logfile, "\\ifx\\%s\\undefined\n  \\def\\%s#1#2{%s}\\fi\n", s,s,def);
}

static FILE *
open_logfile(const char *s) {
  FILE *log = fopen(s, "a");
  if (!log) pari_err(openfiler,"logfile",s);
#ifndef WINCE
  setbuf(log,(char *)NULL);
#endif
  return log;
}

GEN
sd_log(const char *v, long flag)
{
  const char *msg[] = {
      "(off)",
      "(on)",
      "(on with colors)",
      "(TeX output)", NULL
  };
  ulong oldstyle = logstyle;
  GEN res = sd_ulong(v,flag,"log", &logstyle, 0, 3, msg);

  if (!oldstyle != !logstyle)                /* Compare converts to boolean */
  { /* toggled LOG */
    if (oldstyle)
    { /* close log */
      if (flag == d_ACKNOWLEDGE)
        pari_printf("   [logfile was \"%s\"]\n", current_logfile);
      fclose(pari_logfile); pari_logfile = NULL;
    }
    else
      pari_logfile = open_logfile(current_logfile);
  }
  if (pari_logfile && oldstyle != logstyle && logstyle == logstyle_TeX)
  {
    TeX_define("PARIbreak",
               "\\hskip 0pt plus \\hsize\\relax\\discretionary{}{}{}");
    TeX_define("PARIpromptSTART", "\\vskip\\medskipamount\\bgroup\\bf");
    TeX_define("PARIpromptEND", "\\egroup\\bgroup\\tt");
    TeX_define("PARIinputEND", "\\egroup");
    TeX_define2("PARIout",
                "\\vskip\\smallskipamount$\\displaystyle{\\tt\\%#1} = #2$");
  }
  return res;
}

GEN
sd_TeXstyle(const char *v, long flag)
{
  const char *msg[] = { NULL,
        "(bits 0x2/0x4 control output of \\left/\\PARIbreak)"};
  ulong n = GP_DATA->fmt->TeXstyle;
  GEN z = sd_ulong(v,flag,"TeXstyle", &n, 0, 7, msg);
  GP_DATA->fmt->TeXstyle = n; return z;
}

GEN
sd_output(const char *v, long flag)
{
  const char *msg[] = {"(raw)", "(prettymatrix)", "(prettyprint)",
                 "(external prettyprint)", NULL};
  ulong n = GP_DATA->fmt->prettyp;
  GEN z = sd_ulong(v,flag,"output", &n, 0,3,msg);
  GP_DATA->fmt->prettyp = n;
  GP_DATA->fmt->sp = (n != f_RAW);
  return z;
}

GEN
sd_parisize(const char *v, long flag)
{
  ulong size = top - bot, n = size;
  GEN r = sd_ulong(v,flag,"parisize",&n, 10000,LONG_MAX,NULL);
  if (n != size) {
    if (flag == d_INITRC)
      pari_init_stack(n, size);
    else
      allocatemem0(r);
  }
  return r;
}

GEN
sd_primelimit(const char *v, long flag)
{
  ulong max = maxprime(), n = max;
  GEN r = sd_ulong(v,flag,"primelimit",&n, 0,2*(ulong)(LONG_MAX-1024) + 1,NULL);
  if (n != max)
  {
    byteptr ptr = initprimes(n);
    pari_free(diffptr); diffptr = ptr;
  }
  return r;
}

GEN
sd_simplify(const char *v, long flag)
{ return sd_gptoggle(v,flag,"simplify", SIMPLIFY); }

GEN
sd_strictmatch(const char *v, long flag)
{ return sd_gptoggle(v,flag,"strictmatch", STRICTMATCH); }

GEN
sd_timer(const char *v, long flag)
{ return sd_gptoggle(v,flag,"timer", CHRONO); }

static GEN
sd_filename(const char *v, long flag, const char *s, char **f)
{
  if (*v)
  {
    char *str, *old = *f;
    long l;
    char *ev = path_expand(v);
    l = strlen(ev) + 256;
    str = (char *) malloc(l);
    do_strftime(ev,str, l-1); pari_free(ev);
    if (GP_DATA->flags & SECURE)
    {
      char *msg=pari_sprintf("[secure mode]: About to change %s to '%s'",s,str);
      pari_ask_confirm(msg);
      pari_free(msg);
    }
    *f = pari_strdup(str); pari_free(str); pari_free(old);
  }
  if (flag == d_RETURN) return strtoGENstr(*f);
  if (flag == d_ACKNOWLEDGE) pari_printf("   %s = \"%s\"\n",s,*f);
  return gnil;
}

GEN
sd_logfile(const char *v, long flag)
{
  GEN r = sd_filename(v, flag, "logfile", &current_logfile);
  if (*v && pari_logfile)
  {
    FILE *log = open_logfile(current_logfile);
    fclose(pari_logfile); pari_logfile = log;
  }
  return r;
}

GEN
sd_factor_add_primes(const char *v, long flag)
{ return sd_toggle(v,flag,"factor_add_primes", &factor_add_primes); }

GEN
sd_factor_proven(const char *v, long flag)
{ return sd_toggle(v,flag,"factor_proven", &factor_proven); }

GEN
sd_new_galois_format(const char *v, long flag)
{ return sd_toggle(v,flag,"new_galois_format", &new_galois_format); }

GEN
sd_psfile(const char *v, long flag)
{ return sd_filename(v, flag, "psfile", &current_psfile); }

static void
err_secure(const char *d, const char *v)
{ pari_err(talker,"[secure mode]: can't modify '%s' default (to %s)",d,v); }

GEN
sd_help(const char *v, long flag)
{
  const char *str;
  if (*v)
  {
    if (GP_DATA->flags & SECURE) err_secure("help",v);
    if (GP_DATA->help) pari_free((void*)GP_DATA->help);
    GP_DATA->help = path_expand(v);
  }
  str = GP_DATA->help? GP_DATA->help: "none";
  if (flag == d_RETURN) return strtoGENstr(str);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   help = \"%s\"\n", str);
  return gnil;
}

GEN
sd_datadir(const char *v, long flag)
{
  const char *str;
  if (*v)
  {
    if (pari_datadir) pari_free(pari_datadir);
    pari_datadir = path_expand(v);
  }
  str = pari_datadir? pari_datadir: "none";
  if (flag == d_RETURN) return strtoGENstr(str);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   datadir = \"%s\"\n", str);
  return gnil;
}

GEN
sd_path(const char *v, long flag)
{
  gp_path *p = GP_DATA->path;
  if (*v)
  {
    pari_free((void*)p->PATH);
    p->PATH = pari_strdup(v);
    if (flag == d_INITRC) return gnil;
    gp_expand_path(p);
  }
  if (flag == d_RETURN) return strtoGENstr(p->PATH);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   path = \"%s\"\n",p->PATH);
  return gnil;
}

GEN
sd_prettyprinter(const char *v, long flag)
{
  gp_pp *pp = GP_DATA->pp;
  if (*v && !(GP_DATA->flags & TEXMACS))
  {
    char *old = pp->cmd;
    int cancel = (!strcmp(v,"no"));

    if (GP_DATA->flags & SECURE) err_secure("prettyprinter",v);
    if (!strcmp(v,"yes")) v = DFT_PRETTYPRINTER;
    if (old && strcmp(old,v) && pp->file)
    {
      pariFILE *f;
      if (cancel) f = NULL;
      else
      {
        f = try_pipe(v, mf_OUT);
        if (!f)
        {
          pari_warn(warner,"broken prettyprinter: '%s'",v);
          return gnil;
        }
      }
      pari_fclose(pp->file);
      pp->file = f;
    }
    pp->cmd = cancel? NULL: pari_strdup(v);
    if (old) pari_free(old);
    if (flag == d_INITRC) return gnil;
  }
  if (flag == d_RETURN)
    return strtoGENstr(pp->cmd? pp->cmd: "");
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   prettyprinter = \"%s\"\n",pp->cmd? pp->cmd: "");
  return gnil;
}

static GEN
sd_prompt_set(const char *v, long flag, const char *how, char *p)
{
  if (*v) strncpy(p,v,MAX_PROMPT_LEN);
  if (flag == d_RETURN) return strtoGENstr(p);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   prompt%s = \"%s\"\n", how, p);
  return gnil;
}

GEN
sd_prompt(const char *v, long flag)
{
  return sd_prompt_set(v, flag, "", GP_DATA->prompt);
}

GEN
sd_prompt_cont(const char *v, long flag)
{
  return sd_prompt_set(v, flag, "_cont", GP_DATA->prompt_cont);
}

const char *
expand_prompt(const char *prompt, filtre_t *F)
{
  static char buf[MAX_PROMPT_LEN];
  char *s = buf;
  if (F->in_comment) return COMMENTPROMPT;
  do_strftime(prompt, s, MAX_PROMPT_LEN-1);
  return s;
}

default_type gp_default_list[] =
{
  {"breakloop",(void*)sd_breakloop},
  {"colors",(void*)sd_colors},
  {"compatible",(void*)sd_compatible},
  {"datadir",(void*)sd_datadir},
  {"debug",(void*)sd_debug},
  {"debugfiles",(void*)sd_debugfiles},
  {"debugmem",(void*)sd_debugmem},
  {"echo",(void*)sd_echo},
  {"factor_add_primes",(void*)sd_factor_add_primes},
  {"factor_proven",(void*)sd_factor_proven},
  {"format",(void*)sd_format},
  {"graphcolormap",(void*)sd_graphcolormap},
  {"graphcolors",(void*)sd_graphcolors},
  {"help",(void*)sd_help},
  {"histsize",(void*)sd_histsize},
  {"lines",(void*)sd_lines},
  {"log",(void*)sd_log},
  {"logfile",(void*)sd_logfile},
  {"new_galois_format",(void*)sd_new_galois_format},
  {"output",(void*)sd_output},
  {"parisize",(void*)sd_parisize},
  {"path",(void*)sd_path},
  {"prettyprinter",(void*)sd_prettyprinter},
  {"primelimit",(void*)sd_primelimit},
  {"prompt",(void*)sd_prompt},
  {"prompt_cont",(void*)sd_prompt_cont},
  {"psfile",(void*)sd_psfile},
  {"realprecision",(void*)sd_realprecision},
  {"readline",(void*)sd_rl},
  {"recover",(void*)sd_recover},
  {"secure",(void*)sd_secure},
  {"seriesprecision",(void*)sd_seriesprecision},
  {"simplify",(void*)sd_simplify},
  {"strictmatch",(void*)sd_strictmatch},
  {"TeXstyle",(void *)sd_TeXstyle},
  {"timer",(void *)sd_timer},
  {NULL,NULL} /* sentinel */
};

GEN
setdefault(const char *s, const char *v, long flag)
{
  default_type *dft = gp_default_list;

  if (!*s) {
    for (dft = gp_default_list; dft->fun; dft++)
      ((void (*)(const char*,long)) dft->fun)("", d_ACKNOWLEDGE);
    return gnil;
  }
  for (; dft->fun; dft++)
    if (!strcmp(s,dft->name))
      return ((GEN (*)(const char*,long)) dft->fun)(v,flag);
  pari_err(talker,"unknown default: %s",s);
  return NULL; /* not reached */
}
int
pari_is_default(const char *s)
{
  default_type *dft = gp_default_list;

  for (; dft->fun; dft++)
    if (!strcmp(s,dft->name)) return 1;
  return 0;
}

GEN
default0(const char *a, const char *b) { return setdefault(a,b, d_RETURN); }

gp_data *
default_gp_data(void)
{
  static char Prompt[MAX_PROMPT_LEN], Prompt_cont[MAX_PROMPT_LEN];
  static gp_data __GPDATA, *D = &__GPDATA;
  static gp_hist __HIST;
  static gp_pp   __PP;
  static gp_path __PATH;
  static pari_timer __T;

  D->flags = (
    BREAKLOOP | STRICTMATCH | SIMPLIFY | RECOVER
#ifdef READLINE
    | USE_READLINE
#endif
  );
  D->lim_lines = 0;
  D->T    = &__T;
  D->hist = &__HIST;
  D->pp   = &__PP;
  D->path = &__PATH;
  init_help(D);
  init_fmt(D);
  init_hist(D, 5000, 0);
  init_path(D);
  init_pp(D);
  strcpy(Prompt,      DFT_PROMPT); D->prompt = Prompt;
  strcpy(Prompt_cont, CONTPROMPT); D->prompt_cont = Prompt_cont;
  return D;
}
