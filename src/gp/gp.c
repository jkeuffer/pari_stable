/*******************************************************************/
/**                                                               **/
/**                        PARI CALCULATOR                        **/
/**                                                               **/
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#ifdef _WIN32
#  include <windows.h>
#  ifndef WINCE
#    include <process.h>
#  endif
#endif
#ifdef HAS_STRFTIME
#  include <time.h>
#endif
#include "../language/anal.h"
#include "gp.h"

#ifdef READLINE
  void init_readline();
BEGINEXTERN
#  if defined(__cplusplus) && defined(__SUNPRO_CC)
  /* readline.h gives a bad definition of readline() */
  extern char*readline(char*);
#  else
#   ifdef READLINE_LIBRARY
#     include <readline.h>
#   else
#     include <readline/readline.h>
#   endif
#  endif
  extern int isatty(int);
  extern void add_history(char*);
ENDEXTERN
#endif

char*  _analyseur(void);
void   err_recover(long numerr);
void   free_graph(void);
void   gp_expand_path(char *v);
int    gp_init_entrees(module *modlist, entree **hash, int force);
long   gptimer(void);
void   init80(long n);
void   init_defaults(int force);
void   init_graph(void);
void   init_lim_lines(char *s, long max);
void   pari_sig_init(void (*f)(int));
int    whatnow(char *s, int flag);

#define MAX_PROMPT_LEN 128
#define DFT_PROMPT "? "
#define COMMENTPROMPT "comment> "
#define DFT_INPROMPT ""
static GEN *hist;
static jmp_buf local_environnement[MAX_BUFFER];
static char *help_prg,*path,*buflist[MAX_BUFFER];
static char prompt[MAX_PROMPT_LEN];
static char thestring[256];
static long prettyp, test_mode, quiet_mode, gpsilent, simplifyflag;
static long secure;
static long chrono, pariecho, primelimit, parisize, strictmatch;
static long bufindex, tglobal, histsize, paribufsize, lim_lines;
static gp_format fmt;

#define LBRACE '{'
#define RBRACE '}'
#define pariputs_opt(s) if (!quiet_mode) pariputs(s)

void
hit_return()
{
  char tmp[16];
  pariputs("---- (type return to continue) ----");
  do fgets(tmp,16,stdin); while (tmp[strlen(tmp)-1] != '\n');
  /* \n has to be echoed later if we are under emacs (E. Kowalski) */
  pariputc('\n');
}

static void
usage(char *s)
{
  printf("### Usage: %s [options]\n", s);
  printf("Options are:\n");
  printf("\t[-b buffersize]\tDeprecated\n");
  printf("\t[-emacs]\tRun as if in Emacs shell\n");
  printf("\t[-f]\t\tFaststart: do not read .gprc\n");
  printf("\t[--help]\tPrint this message\n");
  printf("\t[-q]\t\tQuiet mode: do not print banner and history numbers\n");
  printf("\t[-p primelimit]\tPrecalculate primes up to the limit\n");
  printf("\t[-s stacksize]\tStart with the PARI stack of given size (in bytes)\n");
  printf("\t[-test]\t\tTest mode.  As -q, plus wrap long lines\n");
  printf("\t[--version]\tOutput version info and exit\n\n");
  exit(0);
}

/* must be called BEFORE pari_init() */
static void
gp_preinit(int force)
{
  static char *dflt;
  char *help;
  long i;

  if (force)
  {
#if !defined(macintosh) || defined(__MWERKS__)
    primelimit = 500000; parisize = 1000000*sizeof(long);
    dflt = DFT_PROMPT;
#else
    primelimit = 200000; parisize = 1000000;
    dflt = "?\n";
#endif
  }
  strcpy(prompt, dflt);

#if defined(UNIX) || defined(__EMX__)
#  ifdef __EMX__
  path = pari_strdup(".;C:/;C:/gp");
#  else
  path = pari_strdup(".:~:~/gp");
#  endif
  help = getenv("GPHELP");
# ifdef GPHELP
    if (!help) help = GPHELP;
# endif
#else
  path = pari_strdup(".");
  help = NULL;
#endif
  help_prg = help? pari_strdup(help): NULL;
  prettyp = f_PRETTYMAT;
  strictmatch = simplifyflag = 1;
  tglobal = 0;
  bufindex = -1;
  secure = test_mode = under_emacs = chrono = pariecho = 0;
  fmt.format = 'g'; fmt.field = 0;
#ifdef LONG_IS_64BIT
  fmt.nb = 38;
#else
  fmt.nb = 28;
#endif
  lim_lines = 0;
  histsize = 5000; paribufsize = 1024;
  i = histsize*sizeof(GEN);
  hist = (GEN *) gpmalloc(i); memset(hist,0,i);
  for (i=0; i<c_LAST; i++) gp_colors[i] = c_NONE;
}

#define GET_SEP_SIZE 128
#define separe(c)  ((c)==';' || (c)==':')

/* Return all chars, up to next separator */
static char*
get_sep(char *t)
{
  static char buf[GET_SEP_SIZE], *lim = buf + GET_SEP_SIZE-1;
  char *s = buf;
  int outer=1;

  for(;;)
  {
    switch(*s++ = *t++)
    {
      case '"':
        if (outer || s[-2] != '\\') outer = !outer;
        break;
      case '\0':
        return buf;
      default:
        if (outer && separe(*t)) { *s=0; return buf; }
    }
    if (s == lim) err(talker,"buffer overflow in get_sep");
  }
}

/* as above, t must be writeable, return 1 if we modified t */
static int
get_sep2(char *t)
{
  int outer=1;
  char *s = t;

  for(;;)
  {
    switch (*s++)
    {
      case '"':
        if (outer || s[-2] != '\\') outer = !outer;
        break;
      case '\0':
        return 0;
      default:
        if (outer && separe(*s)) { *s=0; return 1; }
    }
  }
}

static long
get_int(char *s, long dflt)
{
  char *p=get_sep(s);
  long n=atol(p);

  if (*p == '-') p++;
  while(isdigit((int)*p)) { p++; dflt=n; }
  switch(*p)
  {
    case 'k': case 'K': dflt *= 1000;    p++; break;
    case 'm': case 'M': dflt *= 1000000; p++; break;
  }
  if (*p) err(talker2,"I was expecting an integer here", s, s);
  return dflt;
}

static void
gp_output(GEN x)
{
  long tx=typ(x);

  if (fmt.nb >= 0 && is_intreal_t(tx))
    ecrire(x, fmt.format, fmt.nb, fmt.field);
  else
    switch(prettyp)
    {
      case f_PRETTYMAT: matbrute(x, fmt.format, fmt.nb); break;
      case f_PRETTY   : sor(x, fmt.format, fmt.nb, fmt.field); break;
      case f_RAW      : brute(x, fmt.format, fmt.nb); break;
      case f_TEX      : texe(x, fmt.format, fmt.nb); break;
    }
}

/* print a sequence of (NULL terminated) GEN */
void
print0(GEN *g, long flag)
{
  int old=prettyp;

  if (flag < NBFORMATS) added_newline=1;
  else
    { flag -= NBFORMATS; added_newline=0; }
  prettyp=flag;

  for( ; *g; g++)
    if (typ(*g)==t_STR)
      pariputs(GSTR(*g)); /* otherwise it's surrounded by "" */
    else
      gp_output(*g);

  if (added_newline) pariputc('\n');
  prettyp=old; pariflush();
}

/* write a sequence of (NULL terminated) GEN, to file s */
void
write0(char *s, GEN *g, long flag)
{
  int i = added_newline;
  s = expand_tilde(s);
  if (secure)
  {
    fprintferr("[secure mode]: about to write to '%s'. OK ? (^C if not)\n",s);
    hit_return();
  }
  switchout(s); free(s);
  print0(g,flag); added_newline = i;
  switchout(NULL);
}

/********************************************************************/
/*                                                                  */
/*                            DEFAULTS                              */
/*                                                                  */
/********************************************************************/
static void
do_strftime(char *s, char *buf)
{
#ifdef HAS_STRFTIME
  time_t t = time(NULL);
  strftime(buf,MAX_PROMPT_LEN-1,s,localtime(&t));
#else
  strcpy(buf,s);
#endif
}

static GEN
sd_numeric(char *v, int flag, char *s, long *ptn, long Min, long Max,
           char **msg)
{
  long n;
  if (*v == 0) n = *ptn;
  else
  {
    n = get_int(v,0);
    if (*ptn == n) return gnil;
    if (n > Max || n < Min)
    {
      sprintf(thestring, "default: incorrect value for %s [%ld-%ld]",
	      s, Min, Max);
      err(talker2, thestring, v,v);
    }
    *ptn = n;
  }
  switch(flag)
  {
    case d_RETURN: return stoi(n);
    case d_ACKNOWLEDGE:
      if (msg)
      {
	if (!*msg)
	  msg++; /* single msg, always printed */
	else
	  msg += n; /* one per possible value */
	pariputsf("   %s = %ld %s\n", s, n, *msg);
      }
      else if (Max != 1 || Min != 0)
	pariputsf("   %s = %ld\n", s, n);
      else /* toggle */
      {
	if (n==1) pariputsf("   %s = 1 (on)\n", s);
	else      pariputsf("   %s = 0 (off)\n", s);
      } /* fall through */
    default: return gnil;
  }
}

#define PRECDIGIT (long)((prec-2.)*pariK)
static GEN
sd_realprecision(char *v, int flag)
{
  if (*v)
  {
    long newnb = get_int(v, fmt.nb);
    long newprec = (long) (newnb*pariK1 + 3);

    if (fmt.nb == newnb && prec == newprec) return gnil;
    if (newnb < 0) err(talker,"default: negative real precision");
    fmt.nb = newnb; prec = newprec;
  }
  if (flag == d_RETURN) return stoi(fmt.nb);
  if (flag == d_ACKNOWLEDGE)
  {
    long n = PRECDIGIT;
    pariputsf("   realprecision = %ld significant digits", n);
    if (n != fmt.nb) pariputsf(" (%ld digits displayed)", fmt.nb);
    pariputc('\n');
  }
  return gnil;
}
#undef PRECDIGIT

static GEN
sd_seriesprecision(char *v, int flag)
{
  char *msg[] = {NULL, "significant terms"};
  return sd_numeric(v,flag,"seriesprecision",&precdl, 0,LGBITS,msg);
}

static GEN
sd_format(char *v, int flag)
{
  if (*v)
  {
    char c = *v;
    if (c!='e' && c!='f' && c!='g')
      err(talker2,"default: inexistent format",v,v);
    fmt.format = c; v++;

    if (isdigit((int)*v))
      { fmt.field=atol(v); while (isdigit((int)*v)) v++; }
    if (*v++ == '.')
    {
      if (*v == '-') fmt.nb = -1;
      else
	if (isdigit((int)*v)) fmt.nb=atol(v);
    }
  }
  if (flag == d_RETURN)
  {
    sprintf(thestring, "%c%ld.%ld", fmt.format, fmt.field, fmt.nb);
    return strtoGENstr(thestring,0);
  }
  if (flag == d_ACKNOWLEDGE)
    pariputsf("   format = %c%ld.%ld\n", fmt.format, fmt.field, fmt.nb);
  return gnil;
}

static long
gp_get_color(char **st)
{
  char *s, *v = *st;
  int c, trans = 1;
  if (!isdigit((int)*v)) 
  {
    if (*v == '[')
    {
      char *a[3];
      int i = 0;
      for (a[0] = s = ++v; *s && *s != ']'; s++)
        if (*s == ',') { *s = 0; a[++i] = s+1; }
      if (*s != ']') err(talker2,"expected character: ']'",s, *st);
      *s = 0; for (i++; i<3; i++) a[i] = "";
      /*    properties    |   color    | background */
      c = (atoi(a[2])<<8) | atoi(a[0]) | (atoi(a[1])<<4);
      trans = (*(a[1]) == 0);
      v = s + 1;
    } 
    else { c = c_NONE; trans = 0; }
  }
  else c = atol(v); /* color on transparent background */
  if (trans) c = -c;
  while (*v && *v++ != ',') /* empty */;
  if (c != c_NONE) disable_color=0;
  *st = v; return c;
}

static GEN
sd_colors(char *v, int flag)
{
  long c,l;
  if (*v && !under_emacs)
  {
    char *tmp;
    disable_color=1;
    l = strlen(v);
    if (l <= 2 && strncmp(v, "no", l) == 0)
      v = "";
    if (l <= 3 && strncmp(v, "yes", l) == 0)
      v = "1, 5, 3, 7, 6, 2, 3";	/* Assume recent ReadLine. */
    tmp = v = pari_strdup(v); filtre(v, f_INIT|f_REG);
    for (c=c_ERR; c < c_LAST; c++)
      gp_colors[c] = gp_get_color(&v);
    free(tmp);
  }
  if (flag == d_ACKNOWLEDGE || flag == d_RETURN)
  {
    char *s = thestring;
    int col[3], n;
    for (*s=0,c=c_ERR; c < c_LAST; c++)
    {
      n = gp_colors[c];
      if (n == c_NONE) 
        sprintf(s,"no");
      else
      {
        decode_color(abs(n),col);
        if (n < 0)
        {
          if (col[0])
            sprintf(s,"[%d,,%d]",col[1],col[0]);
          else
            sprintf(s,"%d",col[1]);
        }
        else
          sprintf(s,"[%d,%d,%d]",col[1],col[2],col[0]);
      }
      s += strlen(s);
      if (c < c_LAST - 1) { *s++=','; *s++=' '; }
    }
    if (flag==d_RETURN) return strtoGENstr(thestring,0);
    pariputsf("   colors = \"%s\"\n",thestring);
  }
  return gnil;
}

static GEN
sd_compatible(char *v, int flag)
{
  char *msg[] = {
    "(no backward compatibility)",
    "(warn when using obsolete functions)",
    "(use old functions, don't ignore case)",
    "(use old functions, ignore case)", NULL
  };
  long old = compatible;
  GEN r = sd_numeric(v,flag,"compatible",&compatible, 0,3,msg);

  if (old != compatible && flag != d_INITRC)
  {
    int res = gp_init_entrees(new_fun_set? pari_modules: pari_oldmodules,
        	              functions_hash, 0);
    if (res) err(warner,"user functions re-initialized");
  }
  return r;
}

static GEN
sd_secure(char *v, int flag)
{
  if (secure)
  {
    fprintferr("[secure mode]: Do you want to modify the 'secure' flag? (^C if not)\n");
    hit_return();
  }
  return sd_numeric(v,flag,"secure",&secure, 0,1,NULL);
}

static GEN
sd_buffersize(char *v, int flag)
{ return sd_numeric(v,flag,"buffersize",&paribufsize, 0,
                    (VERYBIGINT / sizeof(long)) - 1,NULL); }
static GEN
sd_debug(char *v, int flag)
{ return sd_numeric(v,flag,"debug",&DEBUGLEVEL, 0,20,NULL); }

static GEN
sd_debugfiles(char *v, int flag)
{ return sd_numeric(v,flag,"debugfiles",&DEBUGFILES, 0,20,NULL); }

static GEN
sd_debugmem(char *v, int flag)
{ return sd_numeric(v,flag,"debugmem",&DEBUGMEM, 0,20,NULL); }

static GEN
sd_echo(char *v, int flag)
{ return sd_numeric(v,flag,"echo",&pariecho, 0,1,NULL); }

static GEN
sd_lines(char *v, int flag)
{ return sd_numeric(v,flag,"lines",&lim_lines, 0,VERYBIGINT,NULL); }

static GEN
sd_histsize(char *v, int flag)
{
  long n = histsize;
  GEN r = sd_numeric(v,flag,"histsize",&n, 1,
                     (VERYBIGINT / sizeof(long)) - 1,NULL);
  if (n != histsize)
  {
    long i = n*sizeof(GEN);
    GEN *gg = (GEN *) gpmalloc(i); memset(gg,0,i);

    if (tglobal)
    {
      long k = (tglobal-1) % n;
      long kmin = k - min(n,histsize), j = k;

      i = (tglobal-1) % histsize;
      while (k > kmin)
      {
	gg[j] = hist[i];
	hist[i] = NULL;
	if (!i) i = histsize;
	if (!j) j = n;
	i--; j--; k--;
      }
      while (hist[i])
      {
	gunclone(hist[i]);
	if (!i) i = histsize;
	i--;
      }
    }
    free((void*)hist); hist=gg; histsize=n;
  }
  return r;
}

static GEN
sd_log(char *v, int flag)
{
  long vlog = logfile? 1: 0, old = vlog;
  GEN r = sd_numeric(v,flag,"log",&vlog, 0,1,NULL);
  if (vlog != old)
  {
    if (vlog)
    {
      logfile = fopen(current_logfile, "a");
      if (!logfile) err(openfiler,"logfile",current_logfile);
#ifndef WINCE
      setbuf(logfile,(char *)NULL);
#endif
    }
    else
    {
      if (flag == d_ACKNOWLEDGE)
        pariputsf("   [logfile was \"%s\"]\n", current_logfile);
      fclose(logfile); logfile=NULL;
    }
  }
  return r;
}

static GEN
sd_output(char *v, int flag)
{
  char *msg[] = {"(raw)", "(prettymatrix)", "(prettyprint)", NULL};
  return sd_numeric(v,flag,"output",&prettyp, 0,2,msg);
}

static GEN
sd_parisize(char *v, int flag)
{
  long n = parisize;
  GEN r = sd_numeric(v,flag,"parisize",&n, 10000,VERYBIGINT,NULL);
  if (n != parisize)
  {
    if (flag != d_INITRC)
    {
      parisize = allocatemoremem(n);
      longjmp(local_environnement[bufindex], 0);
    }
    parisize = n;
  }
  return r;
}

static GEN
sd_primelimit(char *v, int flag)
{
  long n = primelimit;
  GEN r = sd_numeric(v,flag,"primelimit",&n, 0,VERYBIGINT,NULL);
  if (n != primelimit)
  {
    if (flag != d_INITRC)
    {
      byteptr ptr = initprimes(n);
      free(diffptr); diffptr = ptr;
    }
    primelimit = n;
  }
  return r;
}

static GEN
sd_simplify(char *v, int flag)
{ return sd_numeric(v,flag,"simplify",&simplifyflag, 0,1,NULL); }

static GEN
sd_strictmatch(char *v, int flag)
{ return sd_numeric(v,flag,"strictmatch",&strictmatch, 0,1,NULL); }

static GEN
sd_timer(char *v, int flag)
{ return sd_numeric(v,flag,"timer",&chrono, 0,1,NULL); }

static GEN
sd_filename(char *v, int flag, char *s, char **f)
{
  if (*v)
  {
    char *old = *f;
    v = expand_tilde(v);
    do_strftime(v,thestring); free(v);
    *f = pari_strdup(thestring); free(old);
  }
  if (flag == d_RETURN) return strtoGENstr(*f,0);
  if (flag == d_ACKNOWLEDGE) pariputsf("   %s = \"%s\"\n",s,*f);
  return gnil;
}

static GEN
sd_logfile(char *v, int flag)
{
  GEN r = sd_filename(v, flag, "logfile", &current_logfile);
  if (*v && logfile)
  {
    fclose(logfile);
    logfile = fopen(current_logfile, "a");
    if (!logfile) err(openfiler,"logfile",current_logfile);
#ifndef WINCE
    setbuf(logfile,(char *)NULL);
#endif
  }
  return r;
}

static GEN
sd_psfile(char *v, int flag)
{ return sd_filename(v, flag, "psfile", &current_psfile); }

static GEN
sd_help(char *v, int flag)
{
  char *str;
  if (*v)
  {
    if (secure)
      err(talker,"[secure mode]: can't modify 'help' default (to %s)",v);
    if (help_prg) free(help_prg);
    help_prg = expand_tilde(v);
  }
  str = help_prg? help_prg: "none";
  if (flag == d_RETURN) return strtoGENstr(str,0);
  if (flag == d_ACKNOWLEDGE)
    pariputsf("   help = \"%s\"\n", str);
  return gnil;
}

static GEN
sd_path(char *v, int flag)
{
  if (*v)
  {
    char *old = path;
    path = pari_strdup(v); free(old);
    if (flag == d_INITRC) return gnil;
    gp_expand_path(path);
  }
  if (flag == d_RETURN) return strtoGENstr(path,0);
  if (flag == d_ACKNOWLEDGE)
    pariputsf("   path = \"%s\"\n",path);
  return gnil;
}

static GEN
sd_prompt(char *v, int flag)
{
  if (*v)
  {
    strncpy(prompt,v,MAX_PROMPT_LEN);
#ifdef macintosh
    strcat(prompt,"\n");
#endif
  }
  if (flag == d_RETURN) return strtoGENstr(prompt,0);
  if (flag == d_ACKNOWLEDGE)
    pariputsf("   prompt = \"%s\"\n",prompt);
  return gnil;
}

default_type gp_default_list[] =
{
  {"buffersize",(void*)sd_buffersize},
  {"colors",(void*)sd_colors},
  {"compatible",(void*)sd_compatible},
  {"debug",(void*)sd_debug},
  {"debugfiles",(void*)sd_debugfiles},
  {"debugmem",(void*)sd_debugmem},
  {"echo",(void*)sd_echo},
  {"format",(void*)sd_format},
  {"help",(void*)sd_help},
  {"histsize",(void*)sd_histsize},
  {"lines",(void*)sd_lines},
  {"log",(void*)sd_log},
  {"logfile",(void*)sd_logfile},
  {"output",(void*)sd_output},
  {"parisize",(void*)sd_parisize},
  {"path",(void*)sd_path},
  {"primelimit",(void*)sd_primelimit},
  {"prompt",(void*)sd_prompt},
  {"psfile",(void*)sd_psfile},
  {"realprecision",(void*)sd_realprecision},
  {"secure",(void*)sd_secure},
  {"seriesprecision",(void*)sd_seriesprecision},
  {"simplify",(void*)sd_simplify},
  {"strictmatch",(void*)sd_strictmatch},
  {"timer",(void *)sd_timer},
  {NULL,NULL} /* sentinel */
};

static void
help_default()
{
  default_type *dft;

  for (dft=gp_default_list; dft->fun; dft++)
    ((void (*)(ANYARG)) dft->fun)("", d_ACKNOWLEDGE);
}

static GEN
setdefault(char *s,char *v, int flag)
{
  default_type *dft;

  if (!*s) { help_default(); return gnil; }
  for (dft=gp_default_list; dft->fun; dft++)
    if (!strcmp(s,dft->name))
    {
      if (flag == d_EXISTS) return gun;
      return ((GEN (*)(ANYARG)) dft->fun)(v,flag);
    }
  if (flag == d_EXISTS) return gzero;
  err(talker,"unknown default: %s",s);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                             HELP                               **/
/**                                                                **/
/********************************************************************/
static int
has_ext_help()
{
  if (help_prg)
  {
    char *buf = pari_strdup(help_prg), *s = buf;
    FILE *file;

    while (*s && *s != ' ') s++;
    *s = 0; file = (FILE *) fopen(buf,"r");
    if (file) { fclose(file); return 1; }
    free(buf);
  }
  return 0;
}
 
static int
compare_str(char **s1, char **s2) { return strcmp(*s1, *s2); }

/* Print all elements of list in columns, pausing every nbli lines
 * if nbli is non-zero.
 * list is a NULL terminated list of function names
 */
void
print_fun_list(char **list, int nbli)
{
  long i=0, j=0, maxlen=0, nbcol,len, w = term_width();
  char **l;

  while (list[i]) i++;
  qsort (list, i, sizeof(char *), (QSCOMP)compare_str);

  for (l=list; *l; l++)
  {
    len = strlen(*l);
    if (len > maxlen) maxlen=len;
  }
  maxlen++; nbcol= w / maxlen;
  if (nbcol * maxlen == w) nbcol--;
  if (!nbcol) nbcol = 1;

  pariputc('\n'); i=0;
  for (l=list; *l; l++)
  {
    pariputs(*l); i++;
    if (i >= nbcol)
    {
      i=0; pariputc('\n');
      if (nbli && j++ > nbli) { j = 0; hit_return(); }
      continue;
    }
    len = maxlen - strlen(*l);
    while (len--) pariputc(' ');
  }
  if (i) pariputc('\n');
}

#define LIST_LEN 1023
static void
commands(int n)
{
  int hashpos, s = 0, olds = LIST_LEN;
  entree *ep;
  char **list = (char **) gpmalloc((olds+1)*sizeof(char *));

  for (hashpos = 0; hashpos < functions_tblsz; hashpos++)
    for (ep = functions_hash[hashpos]; ep; ep = ep->next)
      if ((n<0 && ep->menu) || ep->menu == n)
      {
        list[s++] = ep->name;
        if (s >= olds)
        {
	  int news = olds + (LIST_LEN + 1)*sizeof(char *);
          list = (char**) gprealloc(list,news,olds);
	  olds = news;
        }
      }
  list[s]=NULL; print_fun_list(list,term_height()-4); free(list);
}

static void
print_user_fun(entree *ep)
{
  gp_args *f= (gp_args*)ep->args;
  GEN q = (GEN)ep->value, *arg = f->arg;
  int i, narg;


  q++; /* skip initial NULL */
  pariputs(ep->name); pariputc('(');
  narg = f->narg;
  for (i=1; i<=narg; i++, arg++)
  {
    entree *ep = varentries[*q++];
    pariputs(ep? ep->name:"#");
    if (!gcmp0(*arg)) { pariputc('='); bruteall(*arg,'g',-1,1); }
    if (i == narg) { arg++; break; }
    pariputs(", ");
  }
  pariputs(") = ");
  narg = f->nloc;
  if (narg)
  {
    pariputs("local(");
    for (i=1; i<=narg; i++, arg++)
    {
      entree *ep = varentries[*q++];
      pariputs(ep? ep->name:"#");
      if (!gcmp0(*arg)) { pariputc('='); bruteall(*arg,'g',-1,1); }
      if (i == narg) break;
      pariputs(", ");
    }
    pariputs("); ");
  }
  pariputs((char*)q);
}

static void
print_user_member(entree *ep)
{
  GEN q = (GEN)ep->value;
  entree *ep2;

  q++; /* skip initial NULL */
  ep2 = varentries[*q++];
  pariputs(ep2? ep2->name:"#");
  pariputsf(".%s = ", ep->name);
  pariputs((char*)q);
}

static void
user_fun()
{
  entree *ep;
  int hash;

  for (hash = 0; hash < functions_tblsz; hash++)
    for (ep = functions_hash[hash]; ep; ep = ep->next)
      if (EpVALENCE(ep) == EpUSER)
      {
	pariputc(LBRACE); print_user_fun(ep);
	pariputc(RBRACE); pariputs("\n\n");
      }
}

static void
user_member()
{
  entree *ep;
  int hash;

  for (hash = 0; hash < functions_tblsz; hash++)
    for (ep = members_hash[hash]; ep; ep = ep->next)
      if (EpVALENCE(ep) == EpMEMBER)
      {
	pariputc(LBRACE); print_user_member(ep);
	pariputc(RBRACE); pariputs("\n\n");
      }
}

static void
community()
{
  pariputs("The standard distribution of GP/PARI includes a reference manual, a tutorial\n\
and a reference card and you should ask the person who installed PARI on\n\
your system where they can be found. You can also download them\n\
from the PARI WWW site http://hasse.mathematik.tu-muenchen.de/ntsw/pari/\n\
\n\
Three mailing lists are devoted to PARI:\n\
  - pari-announce (moderated) to announce major version changes.\n\
  - pari-dev for everything related to the development of PARI, including\n\
    suggestions, technical questions, bug reports and patch submissions.\n\
  - pari-users for everything else !\n\
To subscribe, send an empty message to <list name>-subscribe@list.cr.yp.to\n\
You can only send messages to these lists if you have subscribed !\n\
An archive is kept at the address\n\
  http://hasse.mathematik.tu-muenchen.de/ntsw/pari/lists/archive\n\n\
In case you don't want to subscribe, you can reach the authors directly by\n\
email: pari@math.u-bordeaux.fr (answer not guaranteed).");
}

static void
gentypes(void)
{
  pariputs("List of the PARI types:\n\
  t_INT    : long integers     [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_REAL   : long real numbers [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_INTMOD : integermods       [ code ] [ mod  ] [ integer ]\n\
  t_FRAC   : irred. rationals  [ code ] [ num. ] [ den. ]\n\
  t_FRACN  : rational numbers  [ code ] [ num. ] [ den. ]\n\
  t_COMPLEX: complex numbers   [ code ] [ real ] [ imag ]\n\
  t_PADIC  : p-adic numbers    [ cod1 ] [ cod2 ] [ p ] [ p^r ] [ int ]\n\
  t_QUAD   : quadratic numbers [ cod1 ] [ mod  ] [ real ] [ imag ]\n\
  t_POLMOD : poly mod          [ code ] [ mod  ] [ polynomial ]\n\
  -------------------------------------------------------------\n\
  t_POL    : polynomials       [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_SER    : power series      [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_RFRAC  : irred. rat. func. [ code ] [ num. ] [ den. ]\n\
  t_RFRACN : rational function [ code ] [ num. ] [ den. ]\n\
  t_QFR    : real qfb          [ code ] [ a ] [ b ] [ c ] [ del ]\n\
  t_QFI    : imaginary qfb     [ code ] [ a ] [ b ] [ c ]\n\
  t_VEC    : row vector        [ code ] [  x_1  ] ... [  x_k  ]\n\
  t_COL    : column vector     [ code ] [  x_1  ] ... [  x_k  ]\n\
  t_MAT    : matrix            [ code ] [ col_1 ] ... [ col_k ]\n\
  t_LIST   : list              [ code ] [ cod2 ] [ x_1 ] ... [ x_k ]\n\
  t_STR    : string            [ code ] [ man_1 ] ... [ man_k ]\n\
\n");
}

static void
menu_commands(void)
{
  pariputs("Help topics:\n\
  0: list of user-defined identifiers (variable, alias, function)\n\
  1: Standard monadic or dyadic OPERATORS\n\
  2: CONVERSIONS and similar elementary functions\n\
  3: TRANSCENDENTAL functions\n\
  4: NUMBER THEORETICAL functions\n\
  5: Functions related to ELLIPTIC CURVES\n\
  6: Functions related to general NUMBER FIELDS\n\
  7: POLYNOMIALS and power series\n\
  8: Vectors, matrices, LINEAR ALGEBRA and sets\n\
  9: SUMS, products, integrals and similar functions\n\
 10: GRAPHIC functions\n\
 11: PROGRAMMING under GP\n\
 12: The PARI community\n\
\n\
Further help (list of relevant functions): ?n (1<=n<=11).\n\
Also:\n\
  ? functionname (short on-line help)\n\
  ?\\             (keyboard shortcuts)\n\
  ?.             (member functions)\n");
  if (has_ext_help()) pariputs("\
Extended help looks available:\n\
  ??             (opens the full user's manual in a dvi previewer)\n\
  ??  tutorial   (same with the GP tutorial)\n\
  ??  refcard    (same with the GP reference card)\n\
\n\
  ??  keyword    (long help text about \"keyword\" from the user's manual)\n\
  ??? keyword    (a propos: list of related functions).");
}

static void
slash_commands(void)
{
  pariputs("#       : enable/disable timer\n\
##      : print time for last result\n\
\\\\      : comment up to end of line\n\
\\a {n}  : print result in raw format (readable by PARI)\n\
\\b {n}  : print result in beautified format\n\
\\c      : list all commands (same effect as ?*)\n\
\\d      : print all defaults\n\
\\e {n}  : enable/disable echo (set echo=n)\n\
\\g {n}  : set debugging level\n\
\\gf{n}  : set file debugging level\n\
\\gm{n}  : set memory debugging level\n\
\\h {m-n}: hashtable information\n\
\\l {f}  : enable/disable logfile (set logfile=f)\n\
\\m {n}  : print result in prettymatrix format\n\
\\p {n}  : change real precision\n\
\\ps{n}  : change series precision\n\
\\q      : quit completely this GP session\n\
\\r {f}  : read in a file\n\
\\s {n}  : print stack information\n\
\\t      : print the list of PARI types\n\
\\u      : print the list of user-defined functions\n\
\\um     : print the list of user-defined member functions\n\
\\v      : print current version of GP\n\
\\w {nf} : write to a file\n\
\\x {n}  : print complete inner structure of result\n\
\\y {n}  : disable/enable automatic simplification (set simplify=n)\n\
\n\
{f}=optional filename. {n}=optional integer\n");
}

static void
member_commands(void)
{
  pariputs("Member functions, followed by relevant objects\n\n\
a1-a6, b2-b8, c4-c6 : coeff. of the curve.            ell\n\
area : area                                           ell\n\
bnf  : big number field                                        bnf, bnr\n\
clgp : class group                                             bnf, bnr\n\
cyc  : cyclic decomposition (SNF)               clgp           bnf, bnr\n\
diff, codiff: different and codifferent                    nf, bnf, bnr\n\
disc : discriminant                                   ell, nf, bnf, bnr\n\
e, f : inertia/residues degree            prid\n\
fu   : fundamental units                                       bnf, bnr\n\
futu : [u,w] where u=unit group, w=torsion                     bnf, bnr\n\
gen  : generators                         prid, clgp           bnf, bnr\n\
j    : j-invariant                                    ell\n\
mod  : modulus\n\
nf   : number field                                            bnf, bnr\n\
no   : number of elements                       clgp           bnf, bnr\n\
omega, eta: [omega1,omega2] and [eta1, eta2]          ell\n\
p    : rational prime contained in prid   prid\n\
pol  : defining polynomial                                 nf, bnf, bnr\n\
reg  : regulator                                               bnf, bnr\n\
roots: roots                                          ell  nf, bnf, bnr\n\
sign : signature                                           nf, bnf, bnr\n\
t2   : t2 matrix                                           nf, bnf, bnr\n\
tate : Tate's [u^2,u,q]                               ell\n\
tu   : torsion unit and its order                              bnf, bnr\n\
tufu : [w,u] where u=unit group, w=torsion                     bnf, bnr\n\
w    : Mestre's w                                     ell\n\
zk   : integral basis                                      nf, bnf, bnr\n\
zkst : structure of (Z_K/m)^* (valid for idealstar also)            bnr\n");
}

#define MAX_LINE_LEN 255
static void
external_help(char *s, int num)
{
  long nbli = term_height()-3, li = 0;
  char buf[MAX_LINE_LEN+1], *str, *opt = "", *ar = "";
  pariFILE *z;
  FILE *f;

  if (!help_prg) err(talker,"no external help program");
  str = gpmalloc(strlen(help_prg) + strlen(s) + 64);
  if (num < 0)
    opt = "-k";
  else if (s[strlen(s)-1] != '@')
    { ar = thestring; sprintf(ar,"@%d",num); }
  sprintf(str,"%s -fromgp %s %c%s%s%c",help_prg,opt, SHELL_Q,s,ar,SHELL_Q);
  z = try_pipe(str,0); f = z->file;
  free(str);
  while (fgets(buf,MAX_LINE_LEN,f))
  {
    if (!strncmp("ugly_kludge_done",buf,16)) break;
    buf[MAX_LINE_LEN]=0; pariputs(buf);
    if (++li > nbli) { hit_return(); li = 0; }
  }
  pari_fclose(z);
}

char *keyword_list[]={
  "operator",
  "user",
  "member",
  "integer",
  "real",
  "readline",
  "refcard",
  "tutorial",
  "nf",
  "bnf",
  "bnr",
  "ell",
  NULL
};

static int
ok_external_help(char *s)
{
  long n;
  if (!*s) return 1;
  if (!isalpha((int)*s)) return 3; /* operator or section number */
  if (!strncmp(s,"t_",2)) return 2; /* type name */

  for (n=0; keyword_list[n]; n++)
    if (!strcmp(s,keyword_list[n])) return 3;
  return 0;
}

/* don't mess readline display */
static void
aide_err(char *s1, char *s2, int flag)
{
  if ((flag & h_RL) == 0) err(talker, "%s: %s", s1, s2);
  pariputsf("%s: %s\n", s1, s2);
}

static void
aide0(char *s, int flag)
{
  long n, long_help = flag & h_LONG;
  entree *ep,*ep1;

  s = get_sep(s);
  if (isdigit((int)*s))
  {
    n=atoi(s);
    if (n == 12) { community(); return; }
    if (n<0 || n > 12)
      err(talker2,"no such section in help: ?",s,s);
    if (long_help) external_help(s,3); else commands(n);
    return;
  }
  if (flag & h_APROPOS) { external_help(s,-1); return; }
  if (long_help && (n = ok_external_help(s))) { external_help(s,n); return; }
  switch (*s)
  {
    case '*' : commands(-1); return;
    case '\0': menu_commands(); return;
    case '\\': slash_commands(); return;
    case '.' : member_commands(); return;
  }
  ep = is_entry(s);
  if (ep && long_help)
  {
    if (!strcmp(ep->name, "default"))
    {
      char *t = s+7;
      if (*t == '/' && is_default(t+1))
      {
        external_help(t+1, 2);
        return;
      }
    }
  }
  if (!ep)
  {
    n = is_default(s)? 2: 3;
    if (long_help)
      external_help(s,n);
    else
    {
      if (n == 2) { aide_err(s,"default",flag); return; }
      n = whatnow(s,1);
      if (n) err(obsoler,s,s, s,n);
      aide_err(s,"unknown identifier",flag);
    }
    return;
  }

  ep1 = ep;  ep = do_alias(ep);
  if (ep1 != ep) pariputsf("%s is aliased to:\n\n",s);

  switch(EpVALENCE(ep))
  {
    case EpUSER:
      print_user_fun(ep); if (!ep->help) return;
      pariputs("\n\n"); long_help=0; break;

    case EpGVAR:
    case EpVAR:
      if (!ep->help) { aide_err(s, "user defined variable",flag); return; }
      long_help=0; break;

    case EpINSTALL:
      if (!ep->help) { aide_err(s, "installed function",flag); return; }
      long_help=0; break;
  }
  if (long_help) { external_help(ep->name,3); return; }
  if (ep->help) { print_text(ep->help); return; }

  err(bugparier,"aide (no help found)");
}

void
aide(char *s, int flag)
{
  if ((flag & h_RL) == 0)
  {
    if (*s == '?') { flag |= h_LONG; s++; }
    if (*s == '?') { flag |= h_APROPOS; s++; }
  }
  term_color(c_HELP); aide0(s,flag); term_color(c_NONE);
  if ((flag & h_RL) == 0) pariputc('\n');
}

/********************************************************************/
/**                                                                **/
/**                         METACOMMANDS                           **/
/**                                                                **/
/********************************************************************/

static void
print_entree(entree *ep, long hash)
{
  pariputsf(" %s ",ep->name); pariputsf(VOIR_STRING1,(ulong)ep);
  pariputsf(":\n   hash = %3ld, valence = %3ld, menu = %2ld, code = %s\n",
            hash, ep->valence, ep->menu, ep->code? ep->code: "NULL");
  if (ep->next)
  {
    pariputsf("   next = %s ",(ep->next)->name);
    pariputsf(VOIR_STRING1,(ulong)(ep->next));
  }
  pariputs("\n");
}

static void
print_hash_list(char *s)
{
  long m,n;
  entree *ep;

  if (isalpha((int)*s))
  {
    ep = is_entry_intern(s,functions_hash,&n);
    if (!ep) err(talker,"no such function");
    print_entree(ep,n); return;
  }
  if (isdigit((int)*s) || *s == '$')
  {
    m = functions_tblsz-1; n = atol(s);
    if (*s=='$') n = m;
    if (m<n) err(talker,"invalid range in print_entree");
    while (isdigit((int)*s)) s++;

    if (*s++ != '-') m = n;
    else
    {
      if (*s !='$') m = min(atol(s),m);
      if (m<n) err(talker,"invalid range in print_entree");
    }

    for(; n<=m; n++)
    {
      pariputsf("*** hashcode = %ld\n",n);
      for (ep=functions_hash[n]; ep; ep=ep->next)
	print_entree(ep,n);
    }
    return;
  }
  if (*s=='-')
  {
    for (n=0; n<functions_tblsz; n++)
    {
      m=0;
      for (ep=functions_hash[n]; ep; ep=ep->next) m++;
      pariputsf("%3ld:%3ld ",n,m);
      if (n%9 == 8) pariputc('\n');
    }
    pariputc('\n'); return;
  }
  for (n=0; n<functions_tblsz; n++)
    for (ep=functions_hash[n]; ep; ep=ep->next)
      print_entree(ep,n);
}


static void
center(char *s)
{
  long i, pad = term_width() - strlen(s);
  char *u = thestring;

  if (pad<0) pad=0; else pad >>= 1;
  for (i=0; i<pad; i++) *u++ = ' ';
  while (*s) *u++ = *s++;
  *u++='\n'; *u=0; pariputs(thestring);
}

static char *
what_readline()
{
#ifdef READLINE
 return "v"READLINE" enabled";
#else
  return "disabled";
#endif
}

static void
print_version()
{
  char buf[64];

  center(PARIVERSION); center(PARIINFO);
  sprintf(buf,"(readline %s, extended help%s available)", what_readline(),
          has_ext_help()? "": " not");
  center(buf);
}

static void
gp_head()
{
  print_version(); pariputs("\n");
  center("Copyright (C) 1989-1999 by");
  center("C. Batut, K. Belabas, D. Bernardi, H. Cohen and M. Olivier.");
  pariputs("\n\
Type ? for help, \\q to quit.\n\
Type ?12 for how to get moral (and possibly technical) support.\n\n");
  sd_realprecision  ("",d_ACKNOWLEDGE);
  sd_seriesprecision("",d_ACKNOWLEDGE);
  sd_format         ("",d_ACKNOWLEDGE);
  pariputsf("\nparisize = %ld, primelimit = %ld\n", parisize, primelimit);
}

void
gp_quit()
{
  free_graph(); freeall();
  while (bufindex) free((void *)buflist[bufindex--]);
#ifdef WINCE
#else
  if (INIT_SIG)
  {
#ifdef SIGBUS
    signal(SIGBUS,SIG_DFL);
#endif
    signal(SIGSEGV,SIG_DFL);
    signal(SIGINT,SIG_DFL);
#ifdef SIGBREAK
    signal(SIGBREAK,SIG_DFL);
#endif
  }
#endif
  term_color(c_NONE);
  pariputs_opt("Good bye!\n"); exit(0);
}

/* history management function:
 *   flag < 0, called from freeall()
 *   flag = 0, called from %num in anal.c:truc()
 *   flag > 0, called from %` in anal.c:truc(), p > 0
 */
static GEN
gp_history(long p, long flag, char *old, char *entrypoint)
{
  int er1 = 0;
  if (flag < 0) { free((void *)hist); return NULL; }
  if (!tglobal) er1 = 1;
  if (flag)
  {
    p = tglobal - p;
    if (p <= 0) er1 = 1;
  }
  else if (p > tglobal)
    err(talker2,"I can't see into the future",old,entrypoint);
  if (!p) p = tglobal;
  if (tglobal - p >= histsize) er1 = 1;
  p = (p-1) % histsize;
  if (er1 || !hist[p])
    err(talker2,"I can't remember before the big bang",old,entrypoint);
  return hist[p];
}

static void
escape(char *tch)
{
  char *s, c;

  if (compatible != NONE)
  {
    s = tch;
    while (*s)
      if (*s++ == '=')
      {
	GEN (*f)(char*, int) = NULL;
	int len = (s-tch) - 1;
	
	if (!strncmp(tch,"precision",len))         f = sd_realprecision;
	else if (!strncmp(tch,"serieslength",len)) f = sd_seriesprecision;
	else if (!strncmp(tch,"format",len))       f = sd_format;
	else if (!strncmp(tch,"prompt",len))       f = sd_prompt;
	if (f) { f(get_sep(s), d_ACKNOWLEDGE); return; }
	break;
      }
  }
  s = tch;
  switch ((c = *s++))
  {
    case 'w': case 'x': case 'a': case 'b': case 'm': /* history things */
    {
      long d;
      GEN x;
      if (c != 'w' && c != 'x') d = get_int(s,0);
      else
      {
	d = atol(s); if (*s == '-') s++;
	while (isdigit((int)*s)) s++;
      }
      x = gp_history(d, 0, tch+1,tch-1);
      switch (c)
      {
	case 'a': brute   (x, fmt.format, -1); break;
	case 'm': matbrute(x, fmt.format, -1); break;
	case 'b': sor     (x, fmt.format, -1, fmt.field); break;
	case 'x': voir(x, get_int(s, -1)); return;
        case 'w':
	{
	  GEN g[2]; g[0] = x; g[1] = NULL;
	  s = get_sep(s); if (!*s) s = current_logfile;
	  write0(s, g, f_RAW); return;
	}
      }
      pariputc('\n'); return;
    }

    case 'c': commands(-1); break;
    case 'd': help_default(); break;
    case 'e':
      s = get_sep(s);
      if (!*s) s = pariecho?"0":"1";
      sd_echo(s,d_ACKNOWLEDGE); break;
    case 'g':
      switch (*s)
      {
        case 'm': sd_debugmem(++s,d_ACKNOWLEDGE); break;
        case 'f': sd_debugfiles(++s,d_ACKNOWLEDGE); break;
        default : sd_debug(s,d_ACKNOWLEDGE); break;
      }
      break;
    case 'h': print_hash_list(s); break;
    case 'l':
      s = get_sep(s);
      if (*s)
      {
        sd_logfile(s,d_ACKNOWLEDGE);
        if (logfile) break;
      }
      sd_log(logfile?"0":"1",d_ACKNOWLEDGE);
      break;
    case 'p':
      switch (*s)
      {
        case 's': sd_seriesprecision(++s,d_ACKNOWLEDGE); break;
        default : sd_realprecision(s,d_ACKNOWLEDGE); break;
      }
      break;
    case 'q': gp_quit(); break;
    case 'r': switchin(get_sep(s)); break;
    case 's': etatpile(0); break;
    case 't': gentypes(); break;
    case 'u':
      switch (*s)
      {
        case 'm': user_member(); break;
        default: user_fun();
      }
      break;
    case 'v': print_version(); break;
    case 'y':
      s = get_sep(s);
      if (!*s) s = simplifyflag?"0":"1";
      sd_simplify(s,d_ACKNOWLEDGE); break;
    default: err(caracer1,tch-1,tch-2);
  }
}

/********************************************************************/
/*                                                                  */
/*                              GPRC                                */
/*                                                                  */
/********************************************************************/
#if defined(UNIX) || defined(__EMX__)
#  include <pwd.h>
#endif

static int
get_preproc_value(char *s)
{
  if (!strncmp(s,"EMACS",5)) return under_emacs;
  if (!strncmp(s,"READL",5))
  {
#ifdef READLINE
    return 1;
#else
    return 0;
#endif
  }
  return -1;
}

/* return $HOME or the closest we can find */
static char *
get_home(int *free_it)
{
#ifdef WINCE
  return ".";
#else
#ifndef macintosh /* getenv() for Mac ? */
  char *drv, *pth = getenv("HOME");
  if (pth) return pth;
  if ((drv = getenv("HOMEDRIVE"))
   && (pth = getenv("HOMEPATH")))
  { /* looks like WinNT */
    char *buf = gpmalloc(strlen(pth) + strlen(drv) + 1);
    sprintf(buf, "%s%s",drv,pth);
    *free_it = 1; return buf;
  }
#endif
#endif
#if defined(__EMX__) || defined(UNIX)
  {
    struct passwd *p = getpwuid(geteuid());
    if (p) return p->pw_dir;
  }
#endif
  return ".";
}

static FILE *
gprc_chk(char *s)
{
  FILE *f = fopen(s, "r");
  if (f && !quiet_mode) fprintferr("Reading GPRC: %s ...", s);
  return f;
}

/* Look for [._]gprc: $GPRC, then in $HOME, /, C:/ */
static FILE *
gprc_get()
{
  FILE *f = NULL;
  char *str, *s, c;
  long l;
#ifdef macintosh
  f = gprc_chk("gprc");
#else
#ifdef WINCE
  s = NULL;
#else
  s = getenv("GPRC");
#endif
  if (s) f = gprc_chk(s);
  if (!f)
  {
    int free_it = 0;
    s = get_home(&free_it); l = strlen(s); c = s[l-1];
    str = strcpy(gpmalloc(l+7), s);
    if (free_it) free(s);
    s = str + l;
    if (c != '/' && c != '\\') *s++ = '/';
#ifdef UNIX
    *s = '.'; /* .gprc */
#else
    *s = '_'; /* _gprc */
#endif
    strcpy(s+1, "gprc");
    f = gprc_chk(str); /* in $HOME */
    if (!f) f = gprc_chk(s); /* in . */
    if (!f) f = gprc_chk("/etc/gprc");
    if (!f) f = gprc_chk("C:/_gprc");
    free(str);
  }
#endif
  return f;
}

static int
init_brace(char *s)
{
  while (isspace((int)*s)) s++;
  if (*s == LBRACE) { *s=' '; return 1; }
  return 0;
}

/* return 1 if we deleted a '{' */
static int
init_filtre(char *s)
{
  if (filtre(s, f_INIT)) return 0; /* in comment */
  return init_brace(s);
}

static void
fix_buffer(long newlbuf, char **ptbuf, long *ptlbuf)
{
  buflist[bufindex] = *ptbuf = gprealloc(*ptbuf,newlbuf,*ptlbuf);
  *ptlbuf = paribufsize = newlbuf;
}

/* prompt = NULL --> from gprc */
static int
get_line_from_file(FILE *file, char **ptbuf, long *ptlbuf, char *prompt)
{
  int f_flag = prompt? f_REG | f_KEEPCASE: f_REG;
  int wait_for_brace;
  long len = *ptlbuf;
  char *s = *ptbuf;

  if (!fgets(s, len, file)) return 0;
  wait_for_brace = init_filtre(s);
  for(;;)
  {
    int read_more = (s[strlen(s)-1] != '\n');
    char *end = filtre(s, f_flag);
    if (*s)
    {
      if (read_more) s = end;
      else if (end[-1] == '\\')
      {
        if (*s=='?') break;
        s = end-1;
      }
      else if (end[-1] == '='&& *s != '?')
      {
        s = end;
      }
      else
      {
	if (!wait_for_brace) break;
	if (end[-1] == RBRACE) {end[-1]=0; break;}
	s = end;
      }
      len = *ptlbuf - (s - *ptbuf);
      if (len < 512)
      {
	long n = *ptlbuf << 1, l = s - *ptbuf;
	len += *ptlbuf;
	fix_buffer(n, ptbuf, ptlbuf);
	s = *ptbuf + l;
      }
    }
    if (!fgets(s, len, file)) break;
    if (!read_more && !wait_for_brace)
      wait_for_brace = init_filtre(s);
  }
  if (prompt && *ptbuf)
  {
    if (pariecho) { pariputs(prompt); pariputs(*ptbuf); pariputc('\n'); }
    else if (logfile) fprintf(logfile, "%s%s\n",prompt,*ptbuf);
    pariflush();
  }
  return 1;
}

#define err_gprc(s,t,u) { fprintferr("\n"); err(talker2,s,t,u); }

static char **
gp_initrc()
{
  char **flist, *buf, *s,*s1,*s2;
  FILE *file = gprc_get();
  long fnum = 4, find = 0, *ptlbuf = &paribufsize;

  if (!file) return NULL;
  flist = (char **) gpmalloc(fnum * sizeof(char*));
  buflist[++bufindex] = buf = gpmalloc(*ptlbuf);
  for(;;)
  {
    if (! get_line_from_file(file, &buf, ptlbuf, NULL))
    {
      if (!quiet_mode) fprintferr("Done.\n\n");
      fclose(file); free(buflist[bufindex--]);
      flist[find] = NULL; return flist;
    }
    for (s = buf; *s; )
    {
      s1 = s; if (get_sep2(s)) s++;
      s += strlen(s1); /* point to next expr */
      if (*s1 == '#')
      { /* preprocessor directive */
        int z, NOT = 0;
        s1++;
        if (strncmp(s1,"if",2)) err_gprc("unknown directive",s1,buf);
        s1 += 2;
        if (!strncmp(s1,"not",3)) { NOT = !NOT; s1 += 3; }
        if (*s1 == '!')           { NOT = !NOT; s1++; }
        z = get_preproc_value(s1);
	if (z < 0) err_gprc("unknown preprocessor variable",s1,buf);
	if (NOT) z = !z;
        if (!z) continue;
        s1 += 5;
      }
      if (!strncmp(s1,"read",4))
      { /* read file */
	s1 += 4;
	if (find == fnum-1)
	{
	  long n = fnum << 1;
	  flist = (char**)gprealloc(flist, n*sizeof(char*),
	                                   fnum*sizeof(char*));
	  fnum = n;
	}
	flist[find++] = s2 = gpmalloc(strlen(s1) + 1);
	if (*s1 == '"') (void)readstring(s1, s2);
	else strcpy(s2,s1);
      }
      else
      { /* set default */
	s2 = s1; while (*s2 && *s2 != '=') s2++;
	if (*s2 != '=') err_gprc("missing '='",s2,buf);
	*s2++ = 0;
	if (*s2 == '"') (void)readstring(s2, s2);
	setdefault(s1,s2,d_INITRC);
      }
    }
  }
}

/********************************************************************/
/*                                                                  */
/*                           GP MAIN LOOP                           */
/*                                                                  */
/********************************************************************/
/* flag:
 *   ti_NOPRINT   don't print
 *   ti_REGULAR   print elapsed time (chrono = 1)
 *   ti_LAST      print last elapsed time (##)
 *   ti_INTERRUPT received a SIGINT
 */
static char *
do_time(long flag)
{
  static long last = 0;
  long delay = (flag == ti_LAST)? last: gptimer();
  char *s;

  last = delay;
  switch(flag)
  {
    case ti_NOPRINT: return NULL;
    case ti_REGULAR:   s = "time = "; break;
    case ti_INTERRUPT: s = "user interrupt after "; break;
    case ti_LAST:      s = "  ***   last result computed in "; break;
  }
  strcpy(thestring,s); s=thestring+strlen(s);
  strcpy(s, term_get_color(c_TIME)); s+=strlen(s);
  if (delay >= 3600000)
  {
    sprintf(s, "%ldh, ", delay / 3600000); s+=strlen(s);
    delay %= 3600000;
  }
  if (delay >= 60000)
  {
    sprintf(s, "%ldmn, ", delay / 60000); s+=strlen(s);
    delay %= 60000;
  }
  if (delay >= 1000)
  {
    sprintf(s, "%ld,", delay / 1000); s+=strlen(s);
    delay %= 1000;
    if (delay < 100)
    {
      sprintf(s, "%s", (delay<10)? "00": "0");
      s+=strlen(s);
    }
  }
  sprintf(s, "%ld ms", delay); s+=strlen(s);
  strcpy(s, term_get_color(c_NONE));
  if (flag != ti_INTERRUPT) { s+=strlen(s); *s++='.'; *s++='\n'; *s=0; }
  return thestring;
}

#ifndef WINCE
static void
gp_sighandler(int sig)
{
  char *msg;
  switch(sig)
  {
    case SIGINT:
#ifdef _WIN32
# ifdef SIGBREAK
    case SIGBREAK:
# endif
      if (++win32ctrlc >= 5) _exit(3);
      signal(sig,gp_sighandler);
      return;
#endif
      msg = do_time(ti_INTERRUPT);
      break;

    case SIGSEGV:
      msg="segmentation fault: bug in GP (please report)";
      break;

#ifdef SIGBUS
    case SIGBUS:
      msg="bus error: bug in GP (please report)";
      break;
#endif
    default:
      msg="bug in signal handling (please report)";
  }
  signal(sig,gp_sighandler);
  err(talker,msg);
}
#endif
static void
brace_color(char *s, int c)
{
  if (gp_colors[c] == c_NONE) return;
#ifdef RL_PROMPT_START_IGNORE
  *s++ = RL_PROMPT_START_IGNORE;
#endif
  strcpy(s, term_get_color(c));
#ifdef RL_PROMPT_START_IGNORE
  s+=strlen(s);
  *s++ = RL_PROMPT_END_IGNORE; *s = 0;
#endif
}

static char *
do_prompt()
{
  static char buf[MAX_PROMPT_LEN + 24]; /* + room for color codes */
  char *s = buf;

  *s = 0;
  /* escape sequences bug readline, so use special bracing (if available) */
  brace_color(s, c_PROMPT);
  s += strlen(s);
  if (filtre(s, f_COMMENT)) 
    strcpy(s, COMMENTPROMPT);
  else
    do_strftime(prompt,s);
  s += strlen(s);
  brace_color(s, c_INPUT); return buf;
}

static int
read_line(char *promptbuf, char **ptbuf, long *ptlbuf)
{
  if (infile == stdin /* interactive use */
#if defined(UNIX) || defined(__EMX__)
     && (under_emacs || isatty(fileno(stdin)))
#endif
  )
  {
#ifdef READLINE
    static char *previous_hist = NULL;
    char *rlbuffer = readline(promptbuf), *s = *ptbuf;
    int wait_for_brace, wait_for_input;

    if (!rlbuffer) { pariputs("\n"); return 0; } /* EOF */
    wait_for_input = wait_for_brace = init_filtre(rlbuffer);
    for(;;)
    {
      long len = s - *ptbuf;
      char *end = filtre(rlbuffer, f_READL);
      long l = end - rlbuffer;

      if (len + l > *ptlbuf)
      {
	fix_buffer(len+l+1, ptbuf, ptlbuf);
	s = *ptbuf + len;
      }
      strcpy(s,rlbuffer); free(rlbuffer);
      if (!*s) { if (!wait_for_input) break; }
      else
      {
	s += l-1; /* *s = last input char */
	if (wait_for_brace && *s == RBRACE) {*s=0; break;}
	if (*s == '\\')
        {
          if (*rlbuffer == '?') break;
        }
        else if (*s == '=' && s[1-l] != '?')
        {
          wait_for_input = 1; s++;
        }
        else
	{
	  if (!wait_for_brace) break;
	  s++;
	}
      }
      /* read continuation line */
      if (!(rlbuffer = readline(""))) break;
      if (wait_for_input && !wait_for_brace)
        wait_for_brace = init_brace(rlbuffer);
    }
    /* bug in readline 2.0: need to unblock ^C */
# ifdef USE_SIGRELSE
    sigrelse(SIGINT);
# elif USE_SIGSETMASK
    sigsetmask(0);
# endif
    s = *ptbuf;
    if (*s)
    {
      /* update history (don't add the same entry twice) */
      if (!previous_hist || strcmp(s,previous_hist))
      {
	if (previous_hist) free(previous_hist);
	previous_hist = pari_strdup(s); add_history(s);
      }
      /* update logfile */
      if (logfile) fprintf(logfile, "%s%s\n",promptbuf,s);
    }
    return 1;
#else
    pariputs(promptbuf);
#endif /* defined(READLINE) */
  }
  else promptbuf = DFT_PROMPT;
  return get_line_from_file(infile, ptbuf, ptlbuf, promptbuf);
}

static void
chron(char *s)
{
  if (*s)
  {
    char *old = s-1;
    if (*s == '#') { pariputs(do_time(ti_LAST)); s++; }
    if (*s) err(caracer1,s,old);
  }
  else { chrono = 1-chrono; sd_timer("",d_ACKNOWLEDGE); }
}

/* bufindex != 0: we are doing an immediate read (with read, extern...) */
static GEN
gp_main_loop()
{
  long av, i,j, lbuf = paribufsize;
  char *buf, *promptbuf = prompt;
  GEN z = gnil;

  if (bufindex == MAX_BUFFER) err(talker,"too many nested files");
  buflist[++bufindex] = buf = (char *) gpmalloc(lbuf);
  for(;;)
  {
    if (! bufindex)
    {
      static long tloc, outtyp;
      tloc = tglobal; outtyp = prettyp; recover(0);
      if (setjmp(environnement))
      {
	avma = top; parisize = top - bot;
	j = tglobal - tloc; i = (tglobal-1)%histsize;
	while (j)
	{
	  gunclone(hist[i]); hist[i]=NULL;
	  if (!i) i = histsize;
	  i--; j--;
	}
        tglobal = tloc; prettyp = outtyp;
	while (bufindex) free((void *)buflist[bufindex--]);
      }
    }
    setjmp(local_environnement[bufindex]);
    added_newline = 1;
    if (paribufsize != lbuf)
      fix_buffer(paribufsize, &buf, &lbuf);

    for(;;)
    {
      if (! test_mode) promptbuf = do_prompt();
      if (! read_line(promptbuf, &buf, &lbuf))
      {
#ifdef _WIN32
	Sleep(10); if (win32ctrlc) dowin32ctrlc();
#endif
	if (popinfile()) gp_quit();
	if (bufindex) { free(buflist[bufindex--]); return z; }
      }
      else switch(*buf)
      {
	case '?': aide(buf+1, h_REGULAR); break;
        case '#': chron(buf+1); break;
        case '\\': escape(buf+1); break;
	case '\0': break;
	default: goto WORK;
      }
    }
WORK:
    if (! bufindex)
    {
      char c = buf[strlen(buf) - 1];
      gpsilent = separe(c);
    }
    if (bufindex == 0) (void)gptimer();
    av = avma;
    z = readseq(buf, strictmatch);
    if (!added_newline) pariputc('\n'); /* last output was print1() */
    if (bufindex) continue;
    if (chrono) pariputs(do_time(ti_REGULAR)); else do_time(ti_NOPRINT);
    if (z == gnil) continue;

    if (simplifyflag) z = simplify_i(z);
    i = tglobal % histsize; tglobal++;
    if (hist[i]) gunclone(hist[i]);
    hist[i] = z = gclone(z); avma = av;
    if (gpsilent) continue;

    if (test_mode) { init80(0); gp_output(z); }
    else
    {
      PariOUT *old = pariOut;
      if (DEBUGLEVEL > 4) fprintferr("prec = [%ld, %ld]\n", prec,precdl);
      term_color(c_HIST);
      sprintf(thestring, "%%%ld = ",tglobal);
      pariputs_opt(thestring);
      term_color(c_OUTPUT);
      init_lim_lines(thestring,lim_lines);
      gp_output(z); pariOut=old;
      term_color(c_NONE);
    }
    pariputc('\n'); pariflush();
  }
}

GEN
read0(char *s)
{
  switchin(s);
  return gp_main_loop();
}

static void
check_secure(char *s)
{
  if (secure)
    err(talker, "[secure mode]: system commands not allowed\nTried to run '%s'",s);
}

GEN
extern0(char *s)
{
  check_secure(s);
  infile = try_pipe(s, mf_IN)->file;
  return gp_main_loop();
}

static int
silent()
{
  if (gpsilent) return 1;
  { char c = _analyseur()[1]; return separe(c); }
}

GEN
default0(char *a, char *b, long flag)
{
  if (flag) flag=d_RETURN;
  else
    flag = silent()? d_SILENT: d_ACKNOWLEDGE;
  return setdefault(a,b,flag);
}

void
allocatemem0(unsigned long newsize)
{
  parisize = allocatemoremem(newsize);
  longjmp(local_environnement[bufindex], 0);
}

GEN
input0()
{
  long *ptlbuf = &paribufsize;
  char *buf;
  GEN x;

  if (bufindex == MAX_BUFFER) err(talker,"too many nested files");
  buflist[++bufindex] = buf = gpmalloc(*ptlbuf);
  while (! get_line_from_file(infile, &buf, ptlbuf, DFT_INPROMPT))
    if (popinfile()) { fprintferr("no input ???"); gp_quit(); }
  x = lisseq(buf);
  free(buflist[bufindex--]);
  return x;
}

void
system0(char *s)
{
#if defined(UNIX) || defined(__EMX__)
  check_secure(s);
  system(s);
#else
  err(archer);
#endif
}

void
error0(GEN *g)
{
  term_color(c_ERR);
  if (!added_newline) pariputc('\n');
  pariputs("###   User error:\n\n   ");
  print0(g,f_RAW); term_color(c_NONE);
  err_recover(talker);
}

long
setprecr(long n)
{
  long m = fmt.nb;

  if (n>0) {fmt.nb = n; prec = (long)(n*pariK1 + 3);}
  return m;
}

static void
testint(char *s, long *d)
{
  if (!s) return;
  *d = get_int(s, 0);
  if (*d <= 0) err(talker,"arguments must be positive integers");
}

static char *
read_arg(int *nread, char *t, long argc, char **argv)
{
  int i = *nread;
  if (isdigit((int)*t)) return t;
  if (*t || i==argc) usage(argv[0]);
  *nread = i+1; return argv[i];
}

static char**
read_opt(long argc, char **argv)
{
  char *b=NULL, *p=NULL, *s=NULL, **pre=(char**)1;
  int i=1;

  pari_outfile=stderr;
  while (i<argc)
  {
    char *t = argv[i++];

    if (*t++ != '-') usage(argv[0]);
    switch(*t++)
    {
      case 'b': b = read_arg(&i,t,argc,argv); break;
      case 'p': p = read_arg(&i,t,argc,argv); break;
      case 's': s = read_arg(&i,t,argc,argv); break;

      case 'e':
	if (strncmp(t,"macs",4)) usage(argv[0]);
        under_emacs = 1; break;
      case 'q':
        quiet_mode = 1; break;
      case 't':
	if (strncmp(t,"est",3)) usage(argv[0]);
        disable_color = 1; test_mode = 1; /* fall through */
      case 'f':
	pre = NULL; break;
      case '-':
        if (strcmp(t, "version") == 0) {
           print_version();
           exit(0);
        }
       /* fall through */
      default:
	usage(argv[0]);
    }
  }
  if (pre) pre = gp_initrc();

  /* override the values from gprc */
  testint(b, &paribufsize); if (paribufsize < 10) paribufsize = 10;
  testint(p, &primelimit);
  testint(s, &parisize);
  if (under_emacs) disable_color=1;
  pari_outfile=stdout; return pre;
}

#ifdef WINCE
int
WinMain(HINSTANCE hInstance, HINSTANCE hPrevInstance,
        LPWSTR lpCmdLine, int nShowCmd)
{
  char **argv = NULL;
  int argc = 1;
#else
int
main(int argc, char **argv)
{
#endif
  char **flist;

  init_defaults(1); gp_preinit(1);
  if (setjmp(environnement))
  {
    pariputs("### Errors on startup, exiting...\n\n");
    exit(1);
  }
#ifdef __MWERKS__
  argc = ccommand(&argv);
#endif
  flist = read_opt(argc,argv);
  pari_addfunctions(&pari_modules, functions_gp,helpmessages_gp);
  pari_addfunctions(&pari_modules, functions_highlevel,helpmessages_highlevel);
  pari_addfunctions(&pari_oldmodules, functions_oldgp,helpmessages_oldgp);

  init_graph(); INIT_SIG_off;
  pari_init(parisize, primelimit);
#ifndef WINCE
  pari_sig_init(gp_sighandler);
#endif
#ifdef READLINE
  init_readline();
#endif
  gp_history_fun = gp_history;
  whatnow_fun = whatnow;
  gp_expand_path(path);

  if (!quiet_mode) gp_head();
  if (flist)
  {
    long c=chrono, b=bufindex, e=pariecho;
    FILE *l=logfile;
    char **s = flist;
    bufindex = 0; chrono=0; pariecho=0; logfile=NULL;
    for ( ; *s; s++) { read0(*s); free(*s); }
    bufindex = b; chrono=c; pariecho=e; logfile=l; free(flist);
  }
  (void)gptimer(); (void)timer(); (void)timer2();
  (void)gp_main_loop();
  gp_quit(); return 0; /* not reached */
}
