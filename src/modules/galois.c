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

/**************************************************************/
/*                                                            */
/*    Galois group for degree between 8 and 11 (included)     */
/*                                                            */
/**************************************************************/
#include "pari.h"

#define NMAX 11 /* maximum degree */

typedef char *OBJ;
typedef OBJ *POBJ;
typedef OBJ PERM;
typedef POBJ GROUP;
typedef POBJ RESOLVANTE;

static long isin_G_H(GEN po, GEN *r, long n1, long n2);

static long N,EVEN,PREC,PRMAX,TSCHMAX,coeff[9][10];
static char ID[] = { 0,1,2,3,4,5,6,7,8,9,10,11 };
static char* str_base = GPDATADIR;

static long *par_vec;

/* k-1 entries filled so far
 * m = maximal allowed value, n = sum to reach with remaining elements */
static void
do_par(long k, long n, long m)
{
  long i;
  if (n <= 0)
  {
    GEN p1 = cgetg(k, t_VECSMALL);
    for (i=1; i<k; i++) p1[i] = par_vec[i];
    return;
  }
  if (n < m) m = n;
  for (i=1; i<=m; i++)
  {
    par_vec[k] = i;
    do_par(k+1, n-i, i);
  }
}

/* compute the partitions of n, as decreasing t_VECSMALLs */
static GEN
partitions(long n)
{
  pari_sp av, av1;
  long i, j, lT;
  GEN T, P;

  par_vec = new_chunk(n+1);
  av = avma; do_par(1,n,n);
  av1= avma;
  for (lT=1, P = (GEN)av1; P < (GEN)av; P += lg(P)) lT++;
  T = cgetg(lT, t_VEC);
  for (j=lT, P = (GEN)av1; P < (GEN)av; P += lg(P)) T[--j] = (long)P;

  if (DEBUGLEVEL > 7)
  {
    fprintferr("Partitions of %ld: p(%ld) = %ld\n",n,n,lT-1);
    for (i=1; i<lT; i++) fprintferr("i = %ld: %Z\n",i,(GEN)T[i]);
  }
  return T;
}

/* affect to the permutation x the N arguments that follow */
static void
_aff(char *x,...)
{
  va_list args; long i;
  va_start(args,x); for (i=1; i<=N; i++) x[i] = va_arg(args,int);
  va_end(args);
}

/* return an array of length |len| from the arguments (for galoismodulo) */
static GEN
_gr(long len,...)
{
  va_list args;
  long i, l = labs(len);
  GEN x = new_chunk(l+1);

  va_start(args,len); x[0] = len;
  for (i=1; i<=l; i++) x[i] = va_arg(args,int);
  va_end(args); return x;
}

/* return a VECSMALL of length l from the arguments (for galoismodulo11) */
static GEN
_typ(long l,...)
{
  va_list args;
  long i;
  GEN x = cgetg(l+1, t_VECSMALL);

  va_start(args,l);
  for (i=1; i<=l; i++) x[i] = va_arg(args,int);
  va_end(args); return x;
}

/* create a permutation with the N arguments of the function */
static PERM
_cr(char a,...)
{
  static char x[NMAX+1];
  va_list args;
  long i;

  va_start(args, a); x[0] = N; x[1] = a;
  for (i=2; i<=N; i++) x[i] = va_arg(args,int);
  va_end(args); return x;
}

static PERM
permmul(PERM s1, PERM s2)
{
  long i, n1 = s1[0];
  PERM s3 = gpmalloc(n1+1);
  for (i=1; i<=n1; i++) s3[i]=s1[(int)s2[i]];
  s3[0]=n1; return s3;
}

static void
printperm(PERM perm)
{
  long i, n = perm[0];
  fprintferr("(");
  for (i=1; i<=n; i++) fprintferr(" %d",perm[i]);
  fprintferr(" )\n");
}

/* return i if typ = TYP[i], 0 otherwise */
static long
numerotyp(GEN TYP, GEN galtyp)
{
  long i, nb = lg(TYP);
  for (i=1; i<nb; i++)
    if (gegal(galtyp,(GEN)TYP[i])) return i;
  return 0;
}

static int
raye(long *g, long num)
{
  long i, nb = labs(g[0]);
  for (i=1; i<=nb; i++)
    if (g[i] == num) return 0;
  return 1;
}

/* we can never determine the group completely in there */
static long
rayergroup11(long num, long *gr)
{
  long r = 0;

  if (EVEN)
    switch(num)
    {
      case 2: case 5:
        if (gr[3]) { gr[3]=0; r++; }
      case 3: case 6: case 7:
        if (gr[2]) { gr[2]=0; r++; }
      case 4:
        if (gr[1]) { gr[1]=0; r++; }
    }
  else
    switch(num)
    {
      case 2: case 3:
        if (gr[1]) { gr[1]=0; r++; }
    }
  return r;
}

static long
rayergroup(long **GR, long num, long *gr)
{
  long i,nbgr,r;

  if (!GR) return rayergroup11(num,gr);
  nbgr = lg(GR); r = 0 ;
  if (EVEN)
  {
    for (i=1; i<nbgr; i++)
      if (gr[i] && GR[i][0] < 0 && raye(GR[i],num)) { gr[i]=0; r++; }
  }
  else
  {
    for (i=1; i<nbgr; i++)
      if (gr[i] && GR[i][0] > 0 && raye(GR[i],num)) { gr[i]=0; r++; }
  }
  return r;
}

static long
galmodp(GEN pol, GEN dpol, GEN TYP, long *gr, long **GR)
{
  long p = 0, i,k,l,n,nbremain;
  byteptr d = diffptr;
  GEN p1, dtyp;

  switch(N)
  {
    case  8: nbremain = EVEN? 28: 22; break;
    case  9: nbremain = EVEN? 18: 16; break;
    case 10: nbremain = EVEN? 12: 33; break;
    default: nbremain = EVEN?  5:  3; break; /* case 11 */
  }

  dtyp = new_chunk(NMAX+1);
  k = gr[0]; for (i=1; i<k; i++) gr[i]=1;
  for (k=1; k<15; k++)
  {
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    if (!smodis(dpol,p)) continue; /* p divides dpol */

    p1 = simplefactmod(pol,stoi(p));
    p1 = (GEN)p1[1]; l = lg(p1);
    for (i=1; i<l ; i++) dtyp[i] = itos((GEN)(p1[l-i]));
    dtyp[0] = evaltyp(t_VECSMALL)|evallg(l);
    n = numerotyp(TYP,dtyp);
    if (!n) return 1; /* only for N=11 */
    nbremain -= rayergroup(GR,n,gr);
    if (nbremain==1) return 1;
  }
  return 0;
}

static long
_aux(GEN z)
{
  return signe(z)? ((expo(z)+165) >> TWOPOTBITS_IN_LONG) - lg(z)
                 :  (expo(z)+101) >> TWOPOTBITS_IN_LONG;
}

static long
suffprec(GEN z)
{
  long s,t;

  if (typ(z)==t_COMPLEX)
  {
    s=_aux((GEN)z[1]);
    t=_aux((GEN)z[2]); return (t>s)? t: s;
  }
  return _aux(z);
}

static void
preci(GEN *r, long p)
{
  GEN x;
  long d,i;

  if (p>PRMAX) err(talker,"too large precision in preci()");
  for (d=0; d<TSCHMAX; d++) for (i=1; i<=N; i++)
  {
    x = (GEN) r[d][i];
    if (typ(x)==t_COMPLEX) { setlg(x[1],p); setlg(x[2],p); } else setlg(x,p);
  }
}

static long
getpreci(GEN *r)
{
  GEN x = (GEN)r[0][1];
  return (typ(x)==t_COMPLEX)? lg(x[1]): lg(x);
}

static void
new_pol(GEN *r, long *a, long d)
{
  long i, j;
  pari_sp av;
  GEN x, p1;
  for (i=1; i<=N; i++)
  {
    av =avma; p1 = (GEN)r[0][i]; x = gaddsg(a[0], p1);
    for (j=1; j<=d; j++) x = gaddsg(a[j], gmul(p1,x));
    r[d][i] = (long) gerepileupto(av,x);
  }
}

static void
rangeroots(GEN newr, GEN oldr)
{
  long i, j, k, z[NMAX+1], t[NMAX+1];
  pari_sp av = avma;
  GEN diff,diff0;

  k = 0; /* gcc -Wall */
  for (i=1; i<=N; i++) t[i]=1;
  for (i=1; i<=N; i++)
  {
    diff0 = gun;
    for (j=1; j<=N; j++)
      if (t[j])
      {
        diff = gabs(gsub((GEN)oldr[i], (GEN)newr[j]), PREC);
        if (gcmp(diff,diff0) < 0) { diff0=diff; k=j; }
      }
    z[i]=newr[k]; t[k]=0;
  }
  avma=av; for (i=1; i<=N; i++) newr[i]=z[i];
}

/* increase the roots accuracy */
static void
moreprec(GEN po, GEN *r, long pr)
{
  if (DEBUGLEVEL) { fprintferr("$$$$$ New prec = %ld\n",pr); flusherr(); }
  if (pr > PRMAX)
  { /* recompute roots */
    GEN p1;
    long d = PRMAX + 5;

    PRMAX = (pr < d)? d: pr;
    p1 = cleanroots(po,PRMAX); rangeroots(p1,*r); *r=p1;
    for (d=1; d<TSCHMAX; d++) new_pol(r,coeff[d],d);
  }
  preci(r,pr);
}

#define setcard_obj(x,n) ((x)[0] = (char*)(n))
#define getcard_obj(x)   ((long)((x)[0]))

/* allocate a list of m arrays of length n (index 0 is codeword) */
static POBJ
alloc_pobj(long n, long m)
{
  long i, sz = (m+1)*sizeof(OBJ) + (n+1)*m;
  POBJ g = (POBJ) gpmalloc(sz);
  OBJ gpt = (OBJ) (g + (m+1));

  for (i=1; i<=m; i++) { g[i] = gpt; gpt += (n+1); }
  setcard_obj(g, m); return g;
}

/* swap args ! Return an empty RESOLVANTE */
#define allocresolv(n,m) alloc_pobj(m, n)

static GROUP
allocgroup(long n, long card)
{
  GROUP gr = alloc_pobj(n,card);
  long i;

  for (i=1; i<=card; i++) gr[i][0]=(char)n;
  return gr;
}

static char *
name(char *pre, long n, long n1, long n2, long no)
{
  static char chn[128];
  static char *base = NULL;
  char ch[6];

  if (!base) {
    base = os_getenv("GP_DATA_DIR");
    if (!base)
      base = str_base;
  }
  sprintf(chn, "%s/%s%ld_%ld_%ld", base, pre, n, n1, n2);
  if (no) { sprintf(ch,"_%ld",no); strcat(chn, ch); }
  return chn;
}

#ifdef UNIX
#  include <fcntl.h>
#endif
#ifndef O_RDONLY
#  define O_RDONLY 0
#endif

static long
galopen(char *s)
{
  long fd = os_open(s,O_RDONLY);
  if (fd == -1)
    err(talker,"galois files not available in this version, sorry");
  if (DEBUGLEVEL > 3) msgtimer("opening %s",s);
  return fd;
}

static char
bin(char c)
{
  if (c>='0' && c<='9') c=c-'0';
  else if (c>='A' && c<='Z') c=c-'A'+10;
  else if (c>='a' && c<='z') c=c-'a'+36;
  else err(talker,"incorrect value in bin()");
  return c;
}

#define BUFFS 512
/* fill in g[i][j] (i<=n, j<=m) with (buffered) data from fd */
static void
read_obj(POBJ g, long fd, long n, long m)
{
  char ch[BUFFS];
  long i,j, k = BUFFS;

  i = j = 1;
  for(;;)
  {
    if (k==BUFFS) { os_read(fd,ch,BUFFS); k=0; }
    g[i][j++] = bin(ch[k++]);
    if (j>m) { j=1; i++; if (i>n) break; }
  }
  os_close(fd); if (DEBUGLEVEL > 3) msgtimer("read_object");
}
#undef BUFFS

/* the first 8 bytes contain size data (possibly padded with \0) */
static GROUP
lirecoset(long n1, long n2, long n)
{
  GROUP gr, grptr;
  char c, ch[8];
  long no,m,cardgr,fd;

  if (n<11 || n1<8)
  {
    fd = galopen(name("COS", n, n1, n2, 0));
    os_read(fd,&c,1); m=bin(c); os_read(fd,&c,1);
    os_read(fd,ch,6); cardgr=atol(ch); gr=allocgroup(m,cardgr);
    read_obj(gr, fd,cardgr,m); return gr;
  }
  m = 11; cardgr = 45360;
  gr = grptr = allocgroup(n, 8 * cardgr);
  for (no=1; no<=8; no++)
  {
    fd = galopen(name("COS", n, n1, n2, no)); os_read(fd,ch,8);
    read_obj(grptr, fd,cardgr,m); grptr += cardgr;
  }
  return gr;
}

static RESOLVANTE
lireresolv(long n1, long n2, long n, long *nv, long *nm)
{
  RESOLVANTE b;
  char ch[5];
  long fd;

  fd = galopen(name("RES", n, n1, n2, 0));
  os_read(fd,ch,5); *nm=atol(ch);
  os_read(fd,ch,3); *nv=atol(ch);
  b = allocresolv(*nm,*nv);
  read_obj(b, fd,*nm,*nv); return b;
}

static GEN
monomial(GEN r, PERM bb, long nbv)
{
  long i; GEN p1 = (GEN)r[(int)bb[1]];

  for (i=2; i<=nbv; i++) p1 = gmul(p1, (GEN)r[(int)bb[i]]);
  return p1;
}

static GEN
gpolynomial(GEN r, RESOLVANTE aa, long nbm, long nbv)
{
  long i; GEN p1 = monomial(r,aa[1],nbv);

  for (i=2; i<=nbm; i++) p1 = gadd(p1, monomial(r,aa[i],nbv));
  return p1;
}

static void
zaux1(GEN *z, GEN *r)
{
  GEN p2,p1;
  p2=gsub(r[1],gadd(r[2],r[5]));
  p2=gmul(p2,gsub(r[2],r[5]));
  p1=gmul(p2,r[1]);
  p2=gsub(r[3],gadd(r[2],r[4]));
  p2=gmul(p2,gsub(r[4],r[2]));
  p1=gadd(p1,gmul(p2,r[3]));
  p2=gmul(r[5],gsub(r[4],r[5]));
  z[1]=gadd(p1,gmul(p2,r[4]));

  p2=gsub(r[1],gadd(r[3],r[4]));
  p2=gmul(p2,gsub(r[3],r[4]));
  p1=gmul(p2,r[1]);
  p2=gsub(r[5],gadd(r[3],r[2]));
  p2=gmul(p2,gsub(r[2],r[3]));
  p1=gadd(p1,gmul(p2,r[5]));
  p2=gmul(r[4],gsub(r[2],r[4]));
  z[2]=gadd(p1,gmul(p2,r[2]));
}

static void
zaux(GEN *z, GEN *r)
{
  zaux1(z, r); zaux1(z+2, r+5);
}

static GEN
gpoly(GEN rr, long n1, long n2)
{
  GEN p1,p2,z[6], *r = (GEN*)rr; /* syntaxic kludge */
  long i,j;

  if (N==8)
  {
    if (n1==47 && n2==46)
    {
      p1=gsub(r[3],r[4]);
      for (i=1; i<3; i++) for (j=i+1; j<5; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      for (i=5; i<8; i++) for (j=i+1; j<9; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      p2=r[1];
      for (i=2; i<5; i++) p2=gadd(p2,r[i]);
      for (i=5; i<9; i++) p2=gsub(p2,r[i]);
    }
    else /* n1==44 && n2==40 */
    {
      for (i=1; i<5; i++) z[i] = gadd(r[2*i-1],r[2*i]);
      p1 = gsub(r[1],r[2]);
      for (i=2; i<5; i++) p1 = gmul(p1,gsub(r[2*i-1],r[2*i]));
      p2=gsub(z[3],z[4]);
      for (i=1; i<3; i++) for (j=i+1; j<5; j++) p2 = gmul(p2,gsub(z[i],z[j]));
    }
    return gmul(p1,p2);
  }

  if (N==9)
  {
    if (n1==31 && n2==29)
    {
      p1=gsub(r[2],r[3]);
      for (j=2; j<4; j++) p1 = gmul(p1,gsub(r[1],r[j]));
      for (i=4; i<6; i++) for (j=i+1; j<7; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      p2 = gsub(r[8],r[9]);
      for (j=8; j<10; j++) p2 = gmul(p2,gsub(r[7],r[j]));
    }
    else /* ((n1==34 && n2==31) || (n1=33 && n2==30)) */
    {
      p1=r[1]; for (i=2; i<4; i++) p1=gadd(p1,r[i]);
      p2=r[4]; for (i=5; i<7; i++) p2=gadd(p2,r[i]);
      p1=gmul(p1,p2);
      p2=r[7]; for (i=8; i<10; i++) p2=gadd(p2,r[i]);
    }
    return gmul(p1,p2);
  }

  if (N==10)
  {
    if ((n1==45 && n2==43) || (n1==44 && n2==42))
    {
      p1=r[1]; for (i=2; i<6; i++) p1=gadd(p1,r[i]);
      p2=r[6]; for (i=7; i<11; i++) p2=gadd(p2,r[i]);
      return gmul(p1,p2);
    }
    else if ((n1==45 && n2==39) || (n1==44 && n2==37))
    {
      p1 = gadd(r[1],r[2]);
      for (i=2; i<6; i++) p1 = gmul(p1,gadd(r[2*i-1],r[2*i]));
      return p1;
    }
    else if ((n1==43 && n2==41) || (n1==33 && n2==27))
    {
      p1=gsub(r[4],r[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p1=gmul(p1,gsub(r[i],r[j]));
      p2=gsub(r[9],r[10]);
      for (i=6; i<9; i++) for (j=i+1; j<11; j++) p2=gmul(p2,gsub(r[i],r[j]));
      return gmul(p1,p2);
    }
    else if ((n1==43 && n2==33) || (n1==42 && n2==28) || (n1==41 && n2==27)
          || (n1==40 && n2==21))
    {
      p2=gadd(r[2],r[5]);
      p2=gsub(p2,gadd(r[3],r[4]));
      p1=gmul(p2,r[1]);
      p2=gsub(r[3],gadd(r[4],r[5]));
      p1=gadd(p1,gmul(p2,r[2]));
      p2=gsub(r[4],r[5]);
      p1=gadd(p1,gmul(p2,r[3]));
      z[1]=gadd(p1,gmul(r[4],r[5]));

      p2=gadd(r[7],r[10]);
      p2=gsub(p2,gadd(r[8],r[9]));
      p1=gmul(p2,r[6]);
      p2=gsub(r[8],gadd(r[9],r[10]));
      p1=gadd(p1,gmul(p2,r[7]));
      p2=gsub(r[9],r[10]);
      p1=gadd(p1,gmul(p2,r[8]));
      z[2]=gadd(p1,gmul(r[9],r[10]));
      return gadd(gsqr(z[1]), gsqr(z[2]));
    }
    else if (n1==41 && n2==40)
    {
      p1=gsub(r[4],r[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      p2=gsub(r[9],r[10]);
      for (i=6; i<9; i++) for (j=i+1; j<11; j++) p2 = gmul(p2,gsub(r[i],r[j]));
      return gadd(p1,p2);
    }
    else if ((n1==41 && n2==22) || (n1==40 && n2==11) || (n1==17 && n2==5)
            || (n1==10 && n2==4) || (n1==9 && n2==3) || (n1==6 && n2==1))
    {
      p1=gadd(r[1],r[6]);
      for (i=2; i<6; i++) p1=gmul(p1,gadd(r[i],r[i+5]));
      return p1;
    }
    else if ((n1==39 && n2==38) || (n1==29 && n2==25))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p1=gsub(r[1],r[2]);
      for (i=2; i<6; i++) p1=gmul(p1,gsub(r[2*i-1],r[2*i]));
      p2=gsub(z[4],z[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j]));
      return gmul(p1,p2);
    }
    else if ((n1==39 && n2==36) || (n1==37 && n2==34) || (n1==29 && n2==23)
          || (n1==24 && n2==15))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]); 	
      p1=gsub(z[4],z[5]); p2=gmul(gsub(z[3],z[4]),gsub(z[3],z[5]));
      for (i=1; i<3; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j])); 	
      return gmul(p1,p2);
    }
    else if ((n1==39 && n2==29) || (n1==38 && n2==25) || (n1==37 && n2==24)
          || (n1==36 && n2==23) || (n1==34 && n2==15))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p2=gadd(z[2],z[5]); p2=gsub(p2,gadd(z[3],z[4]));
      p1=gmul(p2,z[1]);
      p2=gsub(z[3],gadd(z[4],z[5]));
      p1=gadd(p1,gmul(p2,z[2]));
      p2=gsub(z[4],z[5]);
      p1=gadd(p1,gmul(p2,z[3]));
      p1=gadd(p1,gmul(z[4],z[5])); return gsqr(p1);
    }
    else if ((n1==39 && n2==22) || (n1==38 && n2==12) || (n1==36 && n2==11)
          || (n1==29 && n2== 5) || (n1==25 && n2== 4) || (n1==23 && n2== 3)
          || (n1==16 && n2== 2) || (n1==14 && n2== 1))
    {
      p1=r[1]; for (i=2; i<6; i++) p1=gadd(p1,r[2*i-1]);
      p2=r[2]; for (i=2; i<6; i++) p2=gadd(p2,r[2*i]);
      return gmul(p1,p2);
    }
    else if (n1==28 && n2==18)
    {
      zaux(z, r);
      p1=gmul(z[1],gsub(z[3],z[4]));
      p2=gmul(z[2],gadd(z[3],z[4])); return gadd(p1,p2);
    }
    else if (n1==27 && n2==20)
    {
      zaux(z, r); p1=gmul(z[1],z[3]); p2=gmul(z[2],z[4]);
      p1 = gsub(p1,p2); p2=r[1];
      for (i=2; i<6 ; i++) p2=gadd(p2,r[i]);
      for (   ; i<11; i++) p2=gsub(p2,r[i]);
      return gmul(p1,p2);
    }
    else if (n1==27 && n2==19)
    {
      zaux(z, r); p1=gmul(z[1],z[3]); p2=gmul(z[2],z[4]);
      return gsub(p1,p2);
    }
    else if ((n1==27 && n2==17) || (n1==21 && n2==9))
    {
      zaux(z, r); p1=gmul(z[1],z[3]); p2=gmul(z[2],z[4]);
      return gadd(p1,p2);
    }
    else if (n1==23 && n2==16)
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p1=gsub(z[1],gadd(z[2],z[5])); p1=gmul(p1,gsub(z[2],z[5]));
      p2=gmul(p1,z[1]); p1=gsub(z[3],gadd(z[2],z[4]));
      p1=gmul(  p1,gsub(z[4],z[2])); p2=gadd(p2,gmul(p1,z[3]));
      p1=gmul(z[5],gsub(z[4],z[5])); p2=gadd(p2,gmul(p1,z[4]));
      p1=gsub(r[1],r[2]);
      for (i=2; i<6; i++) p1=gmul(p1,gsub(r[2*i-1],r[2*i]));
      return gmul(p1,p2);
    }
    else if (n1==22 && n2==12)
    {
      for (i=1; i<6; i++) z[i]=gadd(r[i],r[i+5]);
      p1=gsub(r[1],r[6]);
      for (i=2; i<6; i++) p1=gmul(p1,gsub(r[i],r[i+5]));
      p2=gsub(z[4],z[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j]));
      return gmul(p1,p2);
    }
    else if ((n1==22 && n2==11) || (n1==5 && n2==3))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[i],r[i+5]); 	
      p1=gsub(z[4],z[5]); p2=gmul(gsub(z[3],z[4]),gsub(z[3],z[5]));
      for (i=1; i<3; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j])); 	
      return gmul(p1,p2);
    }
    else if ((n1==22 && n2==5) || (n1==12 && n2==4) || (n1==11 && n2==3))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[i],r[i+5]);
      p2=gadd(z[2],z[5]); p2=gsub(p2,gadd(z[3],z[4])); p1=gmul(p2,z[1]);
      p2=gsub(z[3],gadd(z[4],z[5])); p1=gadd(p1,gmul(p2,z[2]));
      p2=gsub(z[4],z[5]);
      p1=gadd(p1,gmul(p2,z[3])); p1=gadd(p1,gmul(z[4],z[5]));
      return gsqr(p1);
    }
    else if (n1==21 && n2==10)
    {
      zaux(z, r); p1=gmul(z[1],z[4]); p2=gmul(z[2],z[3]);
      return gsub(p1,p2);
    }
  }
  err(talker,"indefinite invariant polynomial in gpoly()");
  return NULL; /* not reached */
}

extern GEN small_to_pol_i(GEN z, long l);
extern GEN ZX_caract_sqf(GEN A, GEN B, long *lambda, long v);

static void
tschirn(GEN po, GEN *r, long pr)
{
  long i,k, v = varn(po), d = TSCHMAX + 1;
  GEN a,h,u;

  if (d >= N) err(talker,"degree too large in tschirn");
  if (DEBUGLEVEL)
    fprintferr("\n$$$$$ Tschirnhaus transformation of degree %ld: $$$$$\n",d);

  a = new_chunk(d);
  do
  {
    for (i=0; i<d; i++) a[i] = random_bits(3) + 1;
    h = small_to_pol_i(a-2, d+2);
    (void)normalizepol_i(h, d+2); setvarn(h,0);
  } while (lgef(h) <= 3 || !ZX_is_squarefree(h));
  setvarn(h, v);
  k = 0; u = ZX_caract_sqf(h, po, &k, v);
  a[1] += k; /* a may have been modified */
  if (DEBUGLEVEL>2) outerr(u);

  d = TSCHMAX;
  for (i=0; i<=d; i++) coeff[d][i] = a[i];
  preci(r,PRMAX); r[d] = cgetg(N+1,t_VEC);
  new_pol(r,a,d); preci(r,pr); TSCHMAX++;
}

static GEN
get_pol_perm(PERM S1, PERM S2, GEN rr, RESOLVANTE a,
             long nbm, long nbv)
{
  static long r[NMAX+1];
  long i;

  for (i=1; i<=N; i++) r[i] = rr[(int)S1[(int)S2[i]]];
  return a? gpolynomial(r,a,nbm,nbv): gpoly(r,nbm,nbv);
}

static void
dbg_rac(long nri,long nbracint,long numi[],GEN racint[],long multi[])
{
  long k;
  if (nbracint>nri+1)
    fprintferr("        there are %ld rational integer roots:\n",nbracint-nri);
  else if (nbracint==nri+1)
    fprintferr("        there is 1 rational integer root:\n");
  else
    fprintferr("        there is no rational integer root.\n");
  for (k=nri+1; k<=nbracint; k++)
  {
    fprintferr("          number%2ld: ",numi[k]);
    bruterr(racint[k],'g',-1); fprintferr(", order %ld.\n",multi[k]);
  }
  flusherr();
}

static GEN
is_int(GEN g)
{
  GEN gint,p1;
  pari_sp av;

  if (typ(g) == t_COMPLEX)
  {
    p1 = (GEN)g[2];
    if (signe(p1) && expo(p1) >= - (bit_accuracy(lg(p1))>>1)) return NULL;
    g = (GEN)g[1];
  }
  gint = ground(g); av=avma; p1 = subri(g,gint);
  if (signe(p1) && expo(p1) >= - (bit_accuracy(lg(p1))>>1)) return NULL;
  avma=av; return gint;
}

static PERM
isin_end(PERM S, PERM uu, PERM s0, GEN gpol, pari_sp av1)
{
  PERM vv = permmul(S,uu), ww = permmul(vv,s0);

  if (DEBUGLEVEL)
  {
    fprintferr("      testing roots reordering: ");
    bruterr(gpol,'g',-1); flusherr();
  }
  free(vv); avma = av1; return ww;
}

#define M 2521
/* return NULL if not included, the permutation of the roots otherwise */
static PERM
check_isin(GEN po,GEN *r,long nbm,long nbv, POBJ a, POBJ tau, POBJ ss, PERM s0)
{
  long pr = PREC, nogr, nocos, init, i, j, k, l, d, nrm, nri, sp;
  pari_sp av1 = avma, av2;
  long nbgr,nbcos,nbracint,nbrac,lastnbri,lastnbrm;
  static long numi[M],numj[M],lastnum[M],multi[M],norac[M],lastnor[M];
  GEN rr,ro,roint,racint[M];
  PERM uu;

  nbcos = getcard_obj(ss);
  nbgr  = getcard_obj(tau);
  lastnbri = lastnbrm = -1; sp = nbracint = nbrac = 0; /* gcc -Wall*/
  for (nogr=1; nogr<=nbgr; nogr++)
  {
    if (DEBUGLEVEL)
      { fprintferr("    ----> Group # %ld/%ld:\n",nogr,nbgr); flusherr(); }
    init = 0;
    for (d=1; ; d++)
    {
      if (d > 1)
      {
        if (DEBUGLEVEL)
        {
          fprintferr("        all integer roots are double roots\n");
          fprintferr("      Working with polynomial #%ld:\n", d); flusherr();
        }
        if (d > TSCHMAX) { tschirn(po,r,pr); av1 = avma; }
      }
      if (!init)
      {
        init = 1;
        for(;;)
        {
          av2=avma; rr = r[d-1]; nbrac = nbracint = 0;
          for (nocos=1; nocos<=nbcos; nocos++)
          {
            ro = get_pol_perm(tau[nogr], ss[nocos], rr,a,nbm,nbv);
            sp = suffprec(ro); if (sp > 0) break;
            roint = is_int(ro);
            if (roint)
            {
              nbrac++;
              if (nbrac >= M)
              {
                err(warner, "more than %ld rational integer roots\n", M);
                avma = av1; init = 0; break;
              }
              for (j=1; j<=nbracint; j++)
                if (gegal(roint,racint[j])) { multi[j]++; break; }
              if (j > nbracint)
              {
                nbracint = j; multi[j]=1; numi[j]=nocos;
                racint[j] = gerepileupto(av2,roint); av2=avma;
              }
              numj[nbrac]=nocos; norac[nbrac]=j;
            }
            avma=av2;
          }
          if (sp <= 0) break;
          avma = av1; pr+=sp; moreprec(po,r,pr); av1 = avma;
        }
        if (!init) continue;

        if (DEBUGLEVEL) dbg_rac(0,nbracint,numi,racint,multi);
        for (i=1; i<=nbracint; i++)
          if (multi[i]==1)
          {
            uu = ss[numi[i]];
            ro = DEBUGLEVEL? get_pol_perm(ID,uu,rr,a,nbm,nbv): (GEN)NULL;
            return isin_end(tau[nogr], uu, s0, ro, av1);
          }
      }
      else
      {
        nrm = nri = 0;
        for (l=1; l<=lastnbri; l++)
        {
          for(;;)
          {
            av2=avma; rr = r[d-1]; nbrac=nrm; nbracint=nri;
            for (k=1; k<=lastnbrm; k++)
              if (lastnor[k]==l)
              {
                nocos = lastnum[k];
                ro = get_pol_perm(tau[nogr], ss[nocos], rr,a,nbm,nbv);
                sp = suffprec(ro); if (sp > 0) break;
                roint = is_int(ro);
                if (roint)
                {
                  nbrac++;
                  for (j=nri+1; j<=nbracint; j++)
                    if (gegal(roint,racint[j])) { multi[j]++; break; }
                  if (j > nbracint)
                  {
                    nbracint = j; multi[j]=1; numi[j]=nocos;
                    racint[j] = gerepileupto(av2,roint); av2=avma;
                  }
                  numj[nbrac]=nocos; norac[nbrac]=j;
                }
                avma=av2;
              }
            if (sp <= 0) break;
            avma = av1; pr+=sp; moreprec(po,r,pr); av1 = avma;
          }
          if (DEBUGLEVEL) dbg_rac(nri,nbracint,numi,racint,multi);
          for (i=nri+1; i<=nbracint; i++)
            if (multi[i]==1)
            {
              uu = ss[numi[i]];
              ro = DEBUGLEVEL? get_pol_perm(ID,uu,rr,a,nbm,nbv): (GEN)NULL;
              return isin_end(tau[nogr], uu, s0, ro, av1);
            }
          avma = av1; nri=nbracint; nrm=nbrac;
        }
      }
      avma = av1; if (!nbracint) break;

      lastnbri=nbracint; lastnbrm=nbrac;
      for (j=1; j<=nbrac; j++)
        { lastnum[j]=numj[j]; lastnor[j]=norac[j]; }
    }
  }
  return NULL;
}
#undef M

/* BIBLIOTHEQUE POUR LE DEGRE 8 */

static long
galoisprim8(GEN po, GEN *r)
{
  long rep;

/* PRIM_8_1: */
  rep=isin_G_H(po,r,50,43);
  if (rep) return EVEN? 37: 43;
/* PRIM_8_2: */
  if (!EVEN) return 50;
/* PRIM_8_3: */
  rep=isin_G_H(po,r,49,48);
  if (!rep) return 49;
/* PRIM_8_4: */
  rep=isin_G_H(po,r,48,36);
  if (!rep) return 48;
/* PRIM_8_5: */
  rep=isin_G_H(po,r,36,25);
  return rep? 25: 36;
}

static long
galoisimpodd8(GEN po, GEN *r, long nh)
{
  long rep;
/* IMPODD_8_1: */
  if (nh!=47) goto IMPODD_8_6;
/* IMPODD_8_2: */
  rep=isin_G_H(po,r,47,46);
  if (!rep) goto IMPODD_8_5;
/* IMPODD_8_4: */
  rep=isin_G_H(po,r,46,28);
  if (rep) goto IMPODD_8_7; else return 46;

IMPODD_8_5:
  rep=isin_G_H(po,r,47,35);
  if (rep) goto IMPODD_8_9; else return 47;

IMPODD_8_6:
  rep=isin_G_H(po,r,44,40);
  if (rep) goto IMPODD_8_10; else goto IMPODD_8_11;

IMPODD_8_7:
  rep=isin_G_H(po,r,28,21);
  if (rep) return 21; else goto IMPODD_8_33;

IMPODD_8_9:
  rep=isin_G_H(po,r,35,31);
  if (rep) goto IMPODD_8_13; else goto IMPODD_8_14;

IMPODD_8_10:
  rep=isin_G_H(po,r,40,26);
  if (rep) goto IMPODD_8_15; else goto IMPODD_8_16;

IMPODD_8_11:
  rep=isin_G_H(po,r,44,38);
  if (rep) goto IMPODD_8_17; else goto IMPODD_8_18;

IMPODD_8_12:
  rep=isin_G_H(po,r,16,7);
  if (rep) goto IMPODD_8_19; else return 16;

IMPODD_8_13:
  rep=isin_G_H(po,r,31,21);
  return rep? 21: 31;

IMPODD_8_14:
  rep=isin_G_H(po,r,35,30);
  if (rep) goto IMPODD_8_34; else goto IMPODD_8_20;

IMPODD_8_15:
  rep=isin_G_H(po,r,26,16);
  if (rep) goto IMPODD_8_12; else goto IMPODD_8_21;

IMPODD_8_16:
  rep=isin_G_H(po,r,40,23);
  if (rep) goto IMPODD_8_22; else return 40;

IMPODD_8_17:
  rep=isin_G_H(po,r,38,31);
  if (rep) goto IMPODD_8_13; else return 38;

IMPODD_8_18:
  rep=isin_G_H(po,r,44,35);
  if (rep) goto IMPODD_8_9; else return 44;

IMPODD_8_19:
  rep=isin_G_H(po,r,7,1);
  return rep? 1: 7;

IMPODD_8_20:
  rep=isin_G_H(po,r,35,28);
  if (rep) goto IMPODD_8_7; else goto IMPODD_8_23;

IMPODD_8_21:
  rep=isin_G_H(po,r,26,17);
  if (rep) goto IMPODD_8_24; else goto IMPODD_8_25;

IMPODD_8_22:
  rep=isin_G_H(po,r,23,8);
  if (rep) goto IMPODD_8_26; else return 23;

IMPODD_8_23:
  rep=isin_G_H(po,r,35,27);
  if (rep) goto IMPODD_8_27; else goto IMPODD_8_28;

IMPODD_8_24:
  rep=isin_G_H(po,r,17,7);
  if (rep) goto IMPODD_8_19; else return 17;

IMPODD_8_25:
  rep=isin_G_H(po,r,26,15);
  if (rep) goto IMPODD_8_29; else return 26;

IMPODD_8_26:
  rep=isin_G_H(po,r,8,1);
  return rep? 1: 8;

IMPODD_8_27:
  rep=isin_G_H(po,r,27,16);
  if (rep) goto IMPODD_8_12; else return 27;

IMPODD_8_28:
  rep=isin_G_H(po,r,35,26);
  if (rep) goto IMPODD_8_15; else return 35;

IMPODD_8_29:
  rep=isin_G_H(po,r,15,7);
  if (rep) goto IMPODD_8_19;
/* IMPODD_8_30: */
  rep=isin_G_H(po,r,15,6);
  if (!rep) goto IMPODD_8_32;
/* IMPODD_8_31: */
  rep=isin_G_H(po,r,6,1);
  return rep? 1: 6;

IMPODD_8_32:
  rep=isin_G_H(po,r,15,8);
  if (rep) goto IMPODD_8_26; else return 15;

IMPODD_8_33:
  rep=isin_G_H(po,r,28,16);
  if (rep) goto IMPODD_8_12; else return 28;

IMPODD_8_34:
  rep=isin_G_H(po,r,30,21);
  return rep? 21: 30;
}

static long
galoisimpeven8(GEN po, GEN *r, long nh)
{
   long rep;
/* IMPEVEN_8_1: */
   if (nh!=45) goto IMPEVEN_8_6;
/* IMPEVEN_8_2: */
   rep=isin_G_H(po,r,45,42);
   if (!rep) goto IMPEVEN_8_5;
/* IMPEVEN_8_4: */
  rep=isin_G_H(po,r,42,34);
  if (rep) goto IMPEVEN_8_7; else goto IMPEVEN_8_8;

IMPEVEN_8_5:
  rep=isin_G_H(po,r,45,41);
  if (rep) goto IMPEVEN_8_9; else return 45;

IMPEVEN_8_6:
  rep=isin_G_H(po,r,39,32);
  if (rep) goto IMPEVEN_8_10; else goto IMPEVEN_8_11;

IMPEVEN_8_7:
  rep=isin_G_H(po,r,34,18);
  if (rep) goto IMPEVEN_8_21; else goto IMPEVEN_8_45;

IMPEVEN_8_8:
  rep=isin_G_H(po,r,42,33);
  if (rep) goto IMPEVEN_8_14; else return 42;

IMPEVEN_8_9:
  rep=isin_G_H(po,r,41,34);
  if (rep) goto IMPEVEN_8_7; else goto IMPEVEN_8_15;

IMPEVEN_8_10:
  rep=isin_G_H(po,r,32,22);
  if (rep) goto IMPEVEN_8_16; else goto IMPEVEN_8_17;

IMPEVEN_8_11:
  rep=isin_G_H(po,r,39,29);
  if (rep) goto IMPEVEN_8_18; else goto IMPEVEN_8_19;

IMPEVEN_8_12:
  rep=isin_G_H(po,r,14,4);
  return rep? 4: 14;

IMPEVEN_8_14:
  rep=isin_G_H(po,r,33,18);
  if (rep) goto IMPEVEN_8_21; else goto IMPEVEN_8_22;

IMPEVEN_8_15:
  rep=isin_G_H(po,r,41,33);
  if (rep) goto IMPEVEN_8_14; else goto IMPEVEN_8_23;

IMPEVEN_8_16:
  rep=isin_G_H(po,r,22,11);
  if (rep) goto IMPEVEN_8_24; else goto IMPEVEN_8_25;

IMPEVEN_8_17:
  rep=isin_G_H(po,r,32,13);
  if (rep) goto IMPEVEN_8_26; else goto IMPEVEN_8_27;

IMPEVEN_8_18:
  rep=isin_G_H(po,r,29,22);
  if (rep) goto IMPEVEN_8_16; else goto IMPEVEN_8_28;

IMPEVEN_8_19:
  rep=isin_G_H(po,r,39,24);
  if (rep) goto IMPEVEN_8_29; else return 39;

IMPEVEN_8_20:
  rep=isin_G_H(po,r,9,4);
  if (rep) return 4; else goto IMPEVEN_8_30;

IMPEVEN_8_21:
  rep=isin_G_H(po,r,18,10);
  if (rep) goto IMPEVEN_8_31; else goto IMPEVEN_8_32;

IMPEVEN_8_22:
  rep=isin_G_H(po,r,33,13);
  if (rep) goto IMPEVEN_8_26; else return 33;

IMPEVEN_8_23:
  rep=isin_G_H(po,r,41,29);
  if (rep) goto IMPEVEN_8_18; else goto IMPEVEN_8_33;

IMPEVEN_8_24:
  rep=isin_G_H(po,r,11,5);
  if (rep) return 5; else goto IMPEVEN_8_34;

IMPEVEN_8_25:
  rep=isin_G_H(po,r,22,9);
  if (rep) goto IMPEVEN_8_20; else return 22;

IMPEVEN_8_26:
  rep=isin_G_H(po,r,13,3);
  return rep? 3: 13;

IMPEVEN_8_27:
  rep=isin_G_H(po,r,32,12);
  if (rep) goto IMPEVEN_8_35; else return 32;

IMPEVEN_8_28:
  rep=isin_G_H(po,r,29,20);
  if (rep) goto IMPEVEN_8_36; else goto IMPEVEN_8_37;

IMPEVEN_8_29:
  rep=isin_G_H(po,r,24,14);
  if (rep) goto IMPEVEN_8_12; else goto IMPEVEN_8_38;

IMPEVEN_8_30:
  rep=isin_G_H(po,r,9,3);
  if (rep) return 3; else goto IMPEVEN_8_39;

IMPEVEN_8_31:
  rep=isin_G_H(po,r,10,2);
  return rep? 2: 10;

IMPEVEN_8_32:
  rep=isin_G_H(po,r,18,9);
  if (rep) goto IMPEVEN_8_20; else return 18;

IMPEVEN_8_33:
  rep=isin_G_H(po,r,41,24);
  if (rep) goto IMPEVEN_8_29; else return 41;

IMPEVEN_8_34:
  rep=isin_G_H(po,r,11,4);
  if (rep) return 4; else goto IMPEVEN_8_44;

IMPEVEN_8_35:
  rep=isin_G_H(po,r,12,5);
  return rep? 5: 12;

IMPEVEN_8_36:
  rep=isin_G_H(po,r,20,10);
  if (rep) goto IMPEVEN_8_31; else return 20;

IMPEVEN_8_37:
  rep=isin_G_H(po,r,29,19);
  if (rep) goto IMPEVEN_8_40; else goto IMPEVEN_8_41;

IMPEVEN_8_38:
  rep=isin_G_H(po,r,24,13);
  if (rep) goto IMPEVEN_8_26; else goto IMPEVEN_8_42;

IMPEVEN_8_39:
  rep=isin_G_H(po,r,9,2);
  return rep? 2: 9;

IMPEVEN_8_40:
  rep=isin_G_H(po,r,19,10);
  if (rep) goto IMPEVEN_8_31; else goto IMPEVEN_8_43;

IMPEVEN_8_41:
  rep=isin_G_H(po,r,29,18);
  if (rep) goto IMPEVEN_8_21; else return 29;

IMPEVEN_8_42:
  rep=isin_G_H(po,r,24,9);
  if (rep) goto IMPEVEN_8_20; else return 24;

IMPEVEN_8_43:
  rep=isin_G_H(po,r,19,9);
  if (rep) goto IMPEVEN_8_20; else return 19;

IMPEVEN_8_44:
  rep=isin_G_H(po,r,11,2);
  return rep? 2: 11;

IMPEVEN_8_45:
  rep=isin_G_H(po,r,34,14);
  if (rep) goto IMPEVEN_8_12; else return 34;
}

static long
closure8(GEN po)
{
  long rep;
  GEN r[NMAX];

  r[0] = cleanroots(po,PRMAX); preci(r,PREC);
  if (!EVEN)
  {
  /* CLOS_8_1: */
    rep=isin_G_H(po,r,50,47);
    if (rep) return galoisimpodd8(po,r,47);
  /* CLOS_8_2: */
    rep=isin_G_H(po,r,50,44);
    if (rep) return galoisimpodd8(po,r,44);
  }
  else
  {
  /* CLOS_8_3: */
    rep=isin_G_H(po,r,49,45);
    if (rep) return galoisimpeven8(po,r,45);
  /* CLOS_8_4: */
    rep=isin_G_H(po,r,49,39);
    if (rep) return galoisimpeven8(po,r,39);
  }
  return galoisprim8(po,r);
}

static GROUP
initgroup(long n, long nbgr)
{
  GROUP t = allocgroup(n,nbgr);
  t[1] = ID; return t;
}

static PERM
data8(long n1, long n2, GROUP *t)
{
  switch(n1)
  {
    case 7: if (n2!=1) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 6, 5, 8, 7);
      return ID;
    case 9: if (n2!=4) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 4, 3, 5, 6, 8, 7);
      return ID;
    case 10: if (n2!=2) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 6, 5, 8, 7);
      return ID;
    case 11:
      switch(n2)
      {
        case 2:
          *t=initgroup(N,2);
          _aff((*t)[2], 1, 2, 5, 6, 3, 4, 8, 7);
          return _cr(1, 3, 5, 8, 2, 4, 6, 7);
        case 4:
          *t=initgroup(N,1);
          return _cr(1, 3, 7, 5, 2, 4, 8, 6);
      }break;
    case 14: if (n2!=4) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 4, 3, 5, 6, 8, 7);
    case 15: if (n2!=6 && n2!=8) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 6, 5, 8, 7);
      return ID;
    case 16: if (n2!=7) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 18:
      switch(n2)
      {
        case 9: *t=initgroup(N,3);
          _aff((*t)[2], 1, 5, 3, 7, 2, 6, 4, 8);
          _aff((*t)[3], 1, 2, 3, 4, 6, 5, 8, 7);
          return ID;
        case 10: *t=initgroup(N,3);
          _aff((*t)[2], 1, 6, 3, 8, 2, 5, 4, 7);
          _aff((*t)[3], 1, 5, 3, 7, 2, 6, 4, 8);
          return ID;
      }break;
    case 19: if (n2!=9) break;
      *t=initgroup(N,1);
      return _cr(1, 5, 3, 8, 2, 6, 4, 7);
    case 20: if (n2!=10) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 22:
      switch(n2)
      {
        case 9: *t=initgroup(N,6);
          _aff((*t)[2], 1, 2, 7, 8, 3, 4, 6, 5);
          _aff((*t)[3], 1, 2, 7, 8, 3, 4, 5, 6);
          _aff((*t)[4], 1, 2, 5, 6, 3, 4, 8, 7);
          _aff((*t)[5], 1, 2, 5, 6, 3, 4, 7, 8);
          _aff((*t)[6], 1, 2, 3, 4, 5, 6, 8, 7);
          return _cr(1, 3, 5, 7, 2, 4, 6, 8);
        case 11: *t=initgroup(N,6);
          _aff((*t)[2], 1, 2, 5, 6, 7, 8, 4, 3);
          _aff((*t)[3], 1, 2, 5, 6, 7, 8, 3, 4);
          _aff((*t)[4], 1, 2, 3, 4, 7, 8, 6, 5);
          _aff((*t)[5], 1, 2, 3, 4, 7, 8, 5, 6);
          _aff((*t)[6], 1, 2, 3, 4, 5, 6, 8, 7);
          return ID;
      }break;
    case 23: if (n2!=8) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 6, 5, 8, 7);
    case 26: if (n2!=15 && n2!=17) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 28: if (n2!=21) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 7, 8, 5, 6);
    case 29: if (n2!=18 && n2!=19) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 30: if (n2!=21) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 7, 8, 5, 6);
    case 31: if (n2!=21) break;
      *t=initgroup(N,3);
      _aff((*t)[2], 1, 2, 3, 4, 7, 8, 5, 6);
      _aff((*t)[3], 1, 2, 5, 6, 7, 8, 3, 4);
      return ID;
    case 32: if (n2!=12 && n2!=13) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 33:
      switch(n2)
      {
        case 13: *t=initgroup(N,1);
          return _cr(1, 5, 2, 6, 3, 7, 4, 8);
        case 18: *t=initgroup(N,1);
          return _cr(1, 2, 5, 6, 3, 4, 7, 8);
      }break;
    case 34:
      switch(n2)
      {
        case 14: *t=initgroup(N,3);
          _aff((*t)[2], 1, 2, 3, 4, 5, 8, 6, 7);
          _aff((*t)[3], 1, 2, 3, 4, 5, 7, 8, 6);
          return _cr(1, 5, 2, 6, 3, 7, 4, 8);
        case 18: *t=initgroup(N,1);
          return _cr(1, 2, 5, 6, 3, 4, 8, 7);
      }break;
    case 39: if (n2!=24) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 40: if (n2!=23) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 41:
      switch(n2)
      {
        case 24: *t=initgroup(N,1);
          return _cr(1, 5, 2, 6, 3, 7, 4, 8);
        case 29: *t=initgroup(N,1);
          return _cr(1, 2, 5, 6, 3, 4, 7, 8);
      }break;
    case 42: if (n2!=34) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 5, 6, 8, 7);
    case 45: if (n2!=41 && n2!=42) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
    case 46: if (n2!=28) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 5, 6, 3, 4, 7, 8);
    case 47: if (n2!=35) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 5, 6, 3, 4, 7, 8);
    case 49: if (n2!=48) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return ID;
  }
  *t=initgroup(N,1); return ID;
}

static long
galoismodulo8(GEN pol, GEN dpol)
{
  long res, gr[51];
  pari_sp av = avma;
  long **GR = (long**)cgeti(49);
  GEN TYP = partitions(8);

/* List of possible types in group j: GR[j][0] = #GR[j] if
 * the group is odd, - #GR[j] if even */
  GR[ 1]= _gr(  4, 1,5,15,22);
  GR[ 2]= _gr( -3, 1,5,15);
  GR[ 3]= _gr( -2, 1,5);
  GR[ 4]= _gr( -3, 1,5,15);
  GR[ 5]= _gr( -3, 1,5,15);
  GR[ 6]= _gr(  5, 1,4,5,15,22);
  GR[ 7]= _gr(  5, 1,3,5,15,22);
  GR[ 8]= _gr(  5, 1,4,5,15,22);
  GR[ 9]= _gr( -4, 1,3,5,15);
  GR[10]= _gr( -4, 1,3,5,15);
  GR[11]= _gr( -4, 1,3,5,15);
  GR[12]= _gr( -5, 1,5,9,15,20);
  GR[13]= _gr( -4, 1,5,9,20);
  GR[14]= _gr( -4, 1,5,9,15);
  GR[15]= _gr(  6, 1,3,4,5,15,22);
  GR[16]= _gr(  5, 1,3,5,15,22);
  GR[17]= _gr(  7, 1,3,5,11,13,15,22);
  GR[18]= _gr( -4, 1,3,5,15);
  GR[19]= _gr( -5, 1,3,5,12,15);
  GR[20]= _gr( -4, 1,3,5,15);
  GR[21]= _gr(  5, 1,3,5,13,15);
  GR[22]= _gr( -4, 1,3,5,15);
  GR[23]= _gr(  7, 1,4,5,9,15,20,22);
  GR[24]= _gr( -6, 1,3,5,9,15,20);
  GR[25]= _gr( -3, 1,5,21);
  GR[26]= _gr(  8, 1,3,4,5,11,13,15,22);
  GR[27]= _gr(  8, 1,2,3,4,5,13,15,22);
  GR[28]= _gr(  7, 1,3,5,12,13,15,22);
  GR[29]= _gr( -5, 1,3,5,12,15);
  GR[30]= _gr(  7, 1,3,4,5,11,13,15);
  GR[31]= _gr(  7, 1,2,3,4,5,13,15);
  GR[32]= _gr( -6, 1,3,5,9,15,20);
  GR[33]= _gr( -6, 1,3,5,9,15,20);
  GR[34]= _gr( -5, 1,3,5,9,15);
  GR[35]= _gr( 10, 1,2,3,4,5,11,12,13,15,22);
  GR[36]= _gr( -5, 1,5,9,20,21);
  GR[37]= _gr( -5, 1,5,9,15,21);
  GR[38]= _gr( 11, 1,2,3,4,5,9,10,13,15,19,20);
  GR[39]= _gr( -7, 1,3,5,9,12,15,20);
  GR[40]= _gr( 10, 1,3,4,5,9,11,13,15,20,22);
  GR[41]= _gr( -7, 1,3,5,9,12,15,20);
  GR[42]= _gr( -8, 1,3,5,6,8,9,15,20);
  GR[43]= _gr(  8, 1,4,5,9,15,19,21,22);
  GR[44]= _gr( 14, 1,2,3,4,5,9,10,11,12,13,15,19,20,22);
  GR[45]= _gr( -9, 1,3,5,6,8,9,12,15,20);
  GR[46]= _gr( 10, 1,3,5,6,8,9,12,13,15,22);
  GR[47]= _gr( 16, 1,2,3,4,5,6,7,8,9,11,12,13,14,15,20,22);
  GR[48]= _gr( -8, 1,3,5,9,12,15,20,21);

  gr[0]=51; res = galmodp(pol,dpol,TYP,gr,GR);
  avma=av; if (!res) return 0;
  return EVEN? 49: 50;
}

/* BIBLIOTHEQUE POUR LE DEGRE 9 */
static long
galoisprim9(GEN po, GEN *r)
{
  long rep;

  if (!EVEN)
  {
  /* PRIM_9_1: */
    rep=isin_G_H(po,r,34,26);
    if (!rep) return 34;
  /* PRIM_9_2: */
    rep=isin_G_H(po,r,26,19);
    if (!rep) return 26;
  /* PRIM_9_3: */
    rep=isin_G_H(po,r,19,16);
    if (rep) return 16;
  /* PRIM_9_4: */
    rep=isin_G_H(po,r,19,15);
    return rep? 15: 19;
  }
/* PRIM_9_5: */
  rep=isin_G_H(po,r,33,32);
  if (!rep) goto PRIM_9_7;
/* PRIM_9_6: */
  rep=isin_G_H(po,r,32,27);
  return rep? 27: 32;

PRIM_9_7:
  rep=isin_G_H(po,r,33,23);
  if (!rep) return 33;
/* PRIM_9_8: */
  rep=isin_G_H(po,r,23,14);
  if (!rep) return 23;
/* PRIM_9_9: */
  rep=isin_G_H(po,r,14,9);
  return rep? 9: 14;
}

static long
galoisimpodd9(GEN po, GEN *r)
{
  long rep;

/* IMPODD_9_1: */
  rep=isin_G_H(po,r,31,29);
  if (!rep) goto IMPODD_9_5;
/* IMPODD_9_2: */
  rep=isin_G_H(po,r,29,20);
  if (!rep) return 29;
IMPODD_9_3:
  rep=isin_G_H(po,r,20,12);
  if (!rep) return 20;
IMPODD_9_4:
  rep=isin_G_H(po,r,12,4);
  return rep? 4: 12;

IMPODD_9_5:
  rep=isin_G_H(po,r,31,28);
  if (!rep) goto IMPODD_9_9;
/* IMPODD_9_6: */
  rep=isin_G_H(po,r,28,22);
  if (!rep) return 28;
IMPODD_9_7:
  rep=isin_G_H(po,r,22,13);
  if (!rep) return 22;
IMPODD_9_8:
  rep=isin_G_H(po,r,13,4);
  return rep? 4: 13;

IMPODD_9_9:
  rep=isin_G_H(po,r,31,24);
  if (!rep) return 31;
/* IMPODD_9_10: */
  rep=isin_G_H(po,r,24,22);
  if (rep) goto IMPODD_9_7;
/* IMPODD_9_11: */
  rep=isin_G_H(po,r,24,20);
  if (rep) goto IMPODD_9_3;
/* IMPODD_9_12: */
  rep=isin_G_H(po,r,24,18);
  if (!rep) return 24;
/* IMPODD_9_13: */
  rep=isin_G_H(po,r,18,13);
  if (rep) goto IMPODD_9_8;
/* IMPODD_9_14: */
  rep=isin_G_H(po,r,18,12);
  if (rep) goto IMPODD_9_4;
/* IMPODD_9_15: */
  rep=isin_G_H(po,r,18,8);
  if (!rep) return 18;
/* IMPODD_9_16: */
  rep=isin_G_H(po,r,8,4);
  return rep? 4: 8;
}

static long
galoisimpeven9(GEN po, GEN *r)
{
  long rep;

/* IMPEVEN_9_1: */
  rep=isin_G_H(po,r,30,25);
  if (!rep) goto IMPEVEN_9_7;
/* IMPEVEN_9_2: */
  rep=isin_G_H(po,r,25,17);
  if (!rep) return 25;
IMPEVEN_9_3:
  rep=isin_G_H(po,r,17,7);
  if (!rep) goto IMPEVEN_9_5;
IMPEVEN_9_4:
  rep=isin_G_H(po,r,7,2);
  return rep? 2: 7;

IMPEVEN_9_5:
  rep=isin_G_H(po,r,17,6);
  if (!rep) return 17;
IMPEVEN_9_6:
  rep=isin_G_H(po,r,6,1);
  return rep? 1: 6;

IMPEVEN_9_7:
  rep=isin_G_H(po,r,30,21);
  if (!rep) return 30;
/* IMPEVEN_9_8: */
  rep=isin_G_H(po,r,21,17);
  if (rep) goto IMPEVEN_9_3;
/* IMPEVEN_9_9: */
  rep=isin_G_H(po,r,21,11);
  if (!rep) goto IMPEVEN_9_13;
/* IMPEVEN_9_10: */
  rep=isin_G_H(po,r,11,7);
  if (rep) goto IMPEVEN_9_4;
/* IMPEVEN_9_11: */
  rep=isin_G_H(po,r,11,5);
  if (!rep) return 11;
/* IMPEVEN_9_12: */
  rep=isin_G_H(po,r,5,2);
  return rep? 2: 5;

IMPEVEN_9_13:
  rep=isin_G_H(po,r,21,10);
  if (!rep) return 21;
/* IMPEVEN_9_14: */
  rep=isin_G_H(po,r,10,6);
  if (rep) goto IMPEVEN_9_6;
/* IMPEVEN_9_15: */
  rep=isin_G_H(po,r,10,3);
  if (!rep) return 10;
/* IMPEVEN_9_16: */
  rep=isin_G_H(po,r,3,1);
  return rep? 1: 3;
}

static long
closure9(GEN po)
{
  long rep;
  GEN r[NMAX];

  r[0] = cleanroots(po,PRMAX); preci(r,PREC);
  if (!EVEN)
  {
  /* CLOS_9_1: */
    rep=isin_G_H(po,r,34,31);
    if (rep) return galoisimpodd9(po,r);
  }
  else
  {
  /* CLOS_9_2: */
    rep=isin_G_H(po,r,33,30);
    if (rep) return galoisimpeven9(po,r);
  }
  return galoisprim9(po,r);
}

static PERM
data9(long n1, long n2, GROUP *t)
{
  switch(n1)
  {
    case 6: if (n2!=1) break;
      *t=initgroup(N,3);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 9, 7);
      _aff((*t)[3], 1, 2, 3, 4, 5, 6, 9, 7, 8);
      return ID;
    case 7: if (n2!=2) break;
      *t=initgroup(N,3);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 9, 7);
      _aff((*t)[3], 1, 2, 3, 4, 5, 6, 9, 7, 8);
      return ID;
    case 8: if (n2!=4) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 4, 7, 2, 5, 8, 3, 6, 9);
      return ID;
    case 12: if (n2!=4) break;
      *t=initgroup(N,3);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 9, 7);
      _aff((*t)[3], 1, 2, 3, 4, 5, 6, 9, 7, 8);
      return ID;
    case 13: if (n2!=4) break;
      *t=initgroup(N,1);
      return _cr(1, 4, 7, 2, 5, 8, 3, 6, 9);
    case 14: if (n2!=9) break;
      *t=initgroup(N,3);
      _aff((*t)[2], 1, 2, 3, 5, 6, 4, 9, 7, 8);
      _aff((*t)[3], 1, 2, 3, 6, 4, 5, 8, 9, 7);
      return ID;
    case 17: if (n2!=6) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 7, 8, 9, 4, 5, 6);
      return ID;
    case 21: if (n2!=10) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 7, 8, 9, 4, 5, 6);
      return ID;
    case 33: if (n2!=32) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 7, 9, 8);
      return ID;
  }
  *t=initgroup(N,1); return ID;
}

static long
galoismodulo9(GEN pol, GEN dpol)
{
  long res, gr[35];
  pari_sp av = avma;
  long **GR = (long**) cgeti(33);
  GEN TYP = partitions(9);

  /* 42 TYPES ORDONNES CROISSANT (T[1],...,T[30])*/

  GR[ 1]= _gr( -3, 1,12,30);
  GR[ 2]= _gr( -2, 1,12);
  GR[ 3]= _gr( -4, 1,5,12,30);
  GR[ 4]= _gr(  4, 1,4,12,26);
  GR[ 5]= _gr( -3, 1,5,12);
  GR[ 6]= _gr( -4, 1,10,12,30);
  GR[ 7]= _gr( -3, 1,10,12);
  GR[ 8]= _gr(  5, 1,4,5,12,26);
  GR[ 9]= _gr( -4, 1,5,12,18);
  GR[10]= _gr( -6, 1,5,10,12,25,30);
  GR[11]= _gr( -5, 1,5,10,12,25);
  GR[12]= _gr(  5, 1,4,10,12,26);
  GR[13]= _gr(  5, 1,4,10,12,26);
  GR[14]= _gr( -4, 1,5,12,18);
  GR[15]= _gr(  5, 1,5,12,18,29);
  GR[16]= _gr(  6, 1,4,5,12,18,26);
  GR[17]= _gr( -5, 1,6,10,12,30);
  GR[18]= _gr(  7, 1,4,5,10,12,25,26);
  GR[19]= _gr(  7, 1,4,5,12,18,26,29);
  GR[20]= _gr(  9, 1,4,6,9,10,12,24,26,30);
  GR[21]= _gr( -7, 1,5,6,10,12,25,30);
  GR[22]= _gr(  7, 1,4,6,10,12,26,30);
  GR[23]= _gr( -6, 1,5,10,12,18,25);
  GR[24]= _gr( 11, 1,4,5,6,9,10,12,24,25,26,30);
  GR[25]= _gr( -7, 1,3,6,8,10,12,30);
  GR[26]= _gr(  9, 1,4,5,10,12,18,25,26,29);
  GR[27]= _gr( -5, 1,5,12,27,30);
  GR[28]= _gr( 12, 1,2,3,4,6,7,8,10,11,12,26,30);
  GR[29]= _gr( 12, 1,3,4,6,8,9,10,12,15,24,26,30);
  GR[30]= _gr(-11, 1,3,5,6,8,10,12,14,17,25,30);
  GR[31]= _gr( 19, 1,2,3,4,5,6,7,8,9,10,11,12,14,15,17,24,25,26,30);
  GR[32]= _gr( -7, 1,5,10,12,25,27,30);

  gr[0]=35; res = galmodp(pol,dpol,TYP,gr,GR);
  avma=av; if (!res) return 0;
  return EVEN? 33: 34;
}

/* BIBLIOTHEQUE POUR LE DEGRE 10 */
static long
galoisprim10(GEN po, GEN *r)
{
  long rep;
  if (EVEN)
  {
  /* PRIM_10_1: */
    rep=isin_G_H(po,r,44,31);
    if (!rep) return 44;
  /* PRIM_10_2: */
    rep=isin_G_H(po,r,31,26);
    if (!rep) return 31;
  /* PRIM_10_3: */
    rep=isin_G_H(po,r,26,7);
    return rep? 7: 26;
  }
  else
  {
  /* PRIM_10_4: */
    rep=isin_G_H(po,r,45,35);
    if (!rep) return 45;
  /* PRIM_10_5: */
    rep=isin_G_H(po,r,35,32);
    if (!rep) goto PRIM_10_7;
  /* PRIM_10_6: */
    rep=isin_G_H(po,r,32,13);
    return rep? 13: 32;

   PRIM_10_7:
    rep=isin_G_H(po,r,35,30);
    return rep? 30: 35;
  }
}

static long
galoisimpeven10(GEN po, GEN *r, long nogr)
{
  long rep;
  if (nogr==42)
  {
 /* IMPEVEN_10_1: */
    rep=isin_G_H(po,r,42,28);
    if (!rep) return 42;
 /* IMPEVEN_10_2: */
    rep=isin_G_H(po,r,28,18);
    return rep? 18: 28;
  }
  else
  {
 /* IMPEVEN_10_3: */
    rep=isin_G_H(po,r,37,34);
    if (!rep) goto IMPEVEN_10_5;
 /* IMPEVEN_10_4: */
    rep=isin_G_H(po,r,34,15);
    if (rep) goto IMPEVEN_10_7; else return 34;

  IMPEVEN_10_5:
    rep=isin_G_H(po,r,37,24);
    if (!rep) return 37;
 /* IMPEVEN_10_6: */
    rep=isin_G_H(po,r,24,15);
    if (!rep) return 24;
  IMPEVEN_10_7:
    rep=isin_G_H(po,r,15,8);
    return rep? 8: 15;
  }
}

static long
galoisimpodd10(GEN po, GEN *r, long nogr)
{
  long rep;
  if (nogr==43)
  {
 /*  IMPODD_10_1: */
    rep=isin_G_H(po,r,43,41);
    if (!rep) goto IMPODD_10_3;
 /* IMPODD_10_2: */
    rep=isin_G_H(po,r,41,40);
    if (rep) goto IMPODD_10_4; else goto IMPODD_10_5;

   IMPODD_10_3:
    rep=isin_G_H(po,r,43,33);
    if (rep) goto IMPODD_10_6; else return 43;

   IMPODD_10_4:
    rep=isin_G_H(po,r,40,21);
    if (rep) goto IMPODD_10_7; else goto IMPODD_10_8;

   IMPODD_10_5:
    rep=isin_G_H(po,r,41,27);
    if (rep) goto IMPODD_10_9; else goto IMPODD_10_10;

   IMPODD_10_6:
    rep=isin_G_H(po,r,33,27);
    if (rep) goto IMPODD_10_9; else return 33;

   IMPODD_10_7:
    rep=isin_G_H(po,r,21,10);
    if (rep) goto IMPODD_10_12; else goto IMPODD_10_13;

   IMPODD_10_8:
    rep=isin_G_H(po,r,40,12);
    if (rep) goto IMPODD_10_14; else goto IMPODD_10_15;

   IMPODD_10_9:
    rep=isin_G_H(po,r,27,21);
    if (rep) goto IMPODD_10_7; else goto IMPODD_10_16;

   IMPODD_10_10:
    rep=isin_G_H(po,r,41,22);
    if (!rep) return 41;
 /* IMPODD_10_11: */
    rep=isin_G_H(po,r,22,12);
    if (rep) goto IMPODD_10_14; else goto IMPODD_10_18;

   IMPODD_10_12:
    rep=isin_G_H(po,r,10,4);
    return rep? 4: 10;

   IMPODD_10_13:
    rep=isin_G_H(po,r,21,9);
    if (rep) goto IMPODD_10_19; else return 21;
   IMPODD_10_14:
    rep=isin_G_H(po,r,12,4);
    return rep? 4: 12;

   IMPODD_10_15:
    rep=isin_G_H(po,r,40,11);
    if (rep) goto IMPODD_10_20; else return 40;
   IMPODD_10_16:
    rep=isin_G_H(po,r,27,20);
    if (!rep) goto IMPODD_10_21;
 /* IMPODD_10_17: */
    rep=isin_G_H(po,r,20,10);
    if (rep) goto IMPODD_10_12; return 20;

   IMPODD_10_18:
    rep=isin_G_H(po,r,22,11);
    if (rep) goto IMPODD_10_20; else goto IMPODD_10_23;

   IMPODD_10_19:
    rep=isin_G_H(po,r,9,6);
    if (rep) goto IMPODD_10_24; else goto IMPODD_10_25;

   IMPODD_10_20:
    rep=isin_G_H(po,r,11,3);
    if (rep) goto IMPODD_10_26; else return 11;

   IMPODD_10_21:
    rep=isin_G_H(po,r,27,19);
    if (rep) goto IMPODD_10_27;
 /* IMPODD_10_22: */
    rep=isin_G_H(po,r,27,17);
    if (rep) goto IMPODD_10_28; else return 27;

   IMPODD_10_23:
    rep=isin_G_H(po,r,22,5);
    if (rep) goto IMPODD_10_29; else return 22;

   IMPODD_10_24:
    rep=isin_G_H(po,r,6,2);
    if (rep) return 2; else goto IMPODD_10_30;

   IMPODD_10_25:
    rep=isin_G_H(po,r,9,3);
    if (!rep) return 9;
   IMPODD_10_26:
    rep=isin_G_H(po,r,3,2);
    if (rep) return 2; else goto IMPODD_10_31;

   IMPODD_10_27:
    rep=isin_G_H(po,r,19,9);
    if (rep) goto IMPODD_10_19; else return 19;

   IMPODD_10_28:
    rep=isin_G_H(po,r,17,10);
    if (rep) goto IMPODD_10_12; else goto IMPODD_10_32;

   IMPODD_10_29:
    rep=isin_G_H(po,r,5,4);
    if (rep) return 4; else goto IMPODD_10_33;

   IMPODD_10_30:
    rep=isin_G_H(po,r,6,1);
    return rep? 1: 6;

   IMPODD_10_31:
    rep=isin_G_H(po,r,3,1);
    return rep? 1: 3;

   IMPODD_10_32:
    rep=isin_G_H(po,r,17,9);
    if (rep) goto IMPODD_10_19; else goto IMPODD_10_60;

   IMPODD_10_33:
    rep=isin_G_H(po,r,5,3);
    if (rep) goto IMPODD_10_26; else return 5;

   IMPODD_10_60:
    rep=isin_G_H(po,r,17,5);
    if (rep) goto IMPODD_10_29; else return 17;
  }
  else
  {
  /* IMPODD_10_34: */
    rep=isin_G_H(po,r,39,38);
    if (!rep) goto IMPODD_10_36;
  /* IMPODD_10_35: */
    rep=isin_G_H(po,r,38,25);
    if (rep) goto IMPODD_10_37; else goto IMPODD_10_38;

   IMPODD_10_36:
    rep=isin_G_H(po,r,39,36);
    if (rep) goto IMPODD_10_39; else goto IMPODD_10_40;

   IMPODD_10_37:
    rep=isin_G_H(po,r,25,4);
    return rep? 4: 25;

   IMPODD_10_38:
    rep=isin_G_H(po,r,38,12);
    if (rep) goto IMPODD_10_41; else return 38;

   IMPODD_10_39:
    rep=isin_G_H(po,r,36,23);
    if (rep) goto IMPODD_10_42; else goto IMPODD_10_43;

   IMPODD_10_40:
    rep=isin_G_H(po,r,39,29);
    if (rep) goto IMPODD_10_44; else goto IMPODD_10_45;

   IMPODD_10_41:
    rep=isin_G_H(po,r,12,4);
    return rep? 4: 12;

   IMPODD_10_42:
    rep=isin_G_H(po,r,23,16);
    if (rep) goto IMPODD_10_46; else goto IMPODD_10_47;

   IMPODD_10_43:
    rep=isin_G_H(po,r,36,11);
    if (rep) goto IMPODD_10_48; else return 36;

   IMPODD_10_44:
    rep=isin_G_H(po,r,29,25);
    if (rep) goto IMPODD_10_37; else goto IMPODD_10_49;

   IMPODD_10_45:
    rep=isin_G_H(po,r,39,22);
    if (rep) goto IMPODD_10_50; else return 39;

   IMPODD_10_46:
    rep=isin_G_H(po,r,16,2);
    return rep? 2: 16;

   IMPODD_10_47:
    rep=isin_G_H(po,r,23,14);
    if (rep) goto IMPODD_10_51; else goto IMPODD_10_52;

   IMPODD_10_48:
    rep=isin_G_H(po,r,11,3);
    if (rep) goto IMPODD_10_53; else return 11;

   IMPODD_10_49:
    rep=isin_G_H(po,r,29,23);
    if (rep) goto IMPODD_10_42; else goto IMPODD_10_54;

   IMPODD_10_50:
    rep=isin_G_H(po,r,22,12);
    if (rep) goto IMPODD_10_41; else goto IMPODD_10_55;

   IMPODD_10_51:
    rep=isin_G_H(po,r,14,1);
    return rep? 1: 14;

   IMPODD_10_52:
    rep=isin_G_H(po,r,23,3);
    if (!rep) return 23;
   IMPODD_10_53:
    rep=isin_G_H(po,r,3,2);
    if (rep) return 2; else goto IMPODD_10_57;

   IMPODD_10_54:
    rep=isin_G_H(po,r,29,5);
    if (rep) goto IMPODD_10_58; else return 29;

   IMPODD_10_55:
    rep=isin_G_H(po,r,22,11);
    if (rep) goto IMPODD_10_48;
 /* IMPODD_10_56: */
    rep=isin_G_H(po,r,22,5);
    if (rep) goto IMPODD_10_58; else return 22;

   IMPODD_10_57:
    rep=isin_G_H(po,r,3,1);
    return rep? 1: 3;

   IMPODD_10_58:
    rep=isin_G_H(po,r,5,4);
    if (rep) return 4;
 /* IMPODD_10_59: */
    rep=isin_G_H(po,r,5,3);
    if (rep) goto IMPODD_10_53; else return 5;
  }
}

static long
closure10(GEN po)
{
  long rep;
  GEN r[NMAX];

  r[0] = cleanroots(po,PRMAX); preci(r,PREC);
  if (EVEN)
  {
  /* CLOS_10_1: */
    rep=isin_G_H(po,r,44,42);
    if (rep) return galoisimpeven10(po,r,42);
  /* CLOS_10_2: */
    rep=isin_G_H(po,r,44,37);
    if (rep) return galoisimpeven10(po,r,37);
  }
  else
  {
  /* CLOS_10_3: */
    rep=isin_G_H(po,r,45,43);
    if (rep) return galoisimpodd10(po,r,43);
  /* CLOS_10_4: */
    rep=isin_G_H(po,r,45,39);
    if (rep) return galoisimpodd10(po,r,39);
  }
  return galoisprim10(po,r);
}

static PERM
data10(long n1,long n2,GROUP *t)
{
  switch(n1)
  {
    case 6: if (n2!=2) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
    case 9: if (n2!=3 && n2!=6) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
      return ID;
    case 10: *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
      return ID;
    case 14: case 16:*t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 17: if (n2!=5) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
      return ID;
    case 19: case 20: *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
      return ID;
    case 21: if (n2!=10) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
    case 23: if (n2!=3) break;
      *t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 25: *t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 26: *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 4, 9, 6, 8, 10, 3, 7, 5);
      return _cr(1, 2, 3, 10, 6, 5, 7, 4, 8, 9);
    case 27: if (n2!=17 && n2!=21) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
      return ID;
    case 28: *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
      return ID;
    case 29: if (n2!=5) break;
      *t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 32: *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 4, 9, 6, 8, 10, 3, 7, 5);
      return _cr(1, 2, 3, 10, 6, 5, 7, 4, 8, 9);
    case 36: if (n2!=11) break;
      *t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 38: if (n2!=12) break;
      *t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 39: if (n2!=22) break;
      *t=initgroup(N,1);
      return _cr(1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 40: if (n2!=12) break;
      *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 5, 6, 7, 8, 10, 9);
    case 41: if (n2!=22 && n2!=40) break;
      *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 7, 8, 10, 9);
      return ID;
  }
  *t=initgroup(N,1); return ID;
}

static long
galoismodulo10(GEN pol, GEN dpol)
{
  long res, gr[46];
  pari_sp av = avma;
  long **GR = (long**) cgeti(45);
  GEN TYP = partitions(10);

  GR[ 1]= _gr(  4, 1,6,30,42);
  GR[ 2]= _gr(  3, 1,6,30);
  GR[ 3]= _gr(  5, 1,5,6,30,42);
  GR[ 4]= _gr(  4, 1,5,23,30);
  GR[ 5]= _gr(  7, 1,5,6,22,23,30,42);
  GR[ 6]= _gr(  5, 1,6,24,30,42);
  GR[ 7]= _gr( -4, 1,5,14,30);
  GR[ 8]= _gr( -4, 1,3,5,30);
  GR[ 9]= _gr(  6, 1,5,6,24,30,42);
  GR[10]= _gr(  5, 1,5,23,24,30);
  GR[11]= _gr(  7, 1,5,6,11,30,33,42);
  GR[12]= _gr(  7, 1,5,6,11,23,30,33);
  GR[13]= _gr(  7, 1,4,5,14,23,30,34);
  GR[14]= _gr(  8, 1,2,3,4,5,6,30,42);
  GR[15]= _gr( -6, 1,3,5,18,22,30);
  GR[16]= _gr(  7, 1,3,5,6,17,23,30);
  GR[17]= _gr(  8, 1,5,6,22,23,24,30,42);
  GR[18]= _gr( -6, 1,5,22,24,30,40);
  GR[19]= _gr(  7, 1,5,6,22,24,30,42);
  GR[20]= _gr(  6, 1,5,22,23,24,30);
  GR[21]= _gr(  9, 1,3,5,6,23,24,26,30,42);
  GR[22]= _gr( 11, 1,3,5,6,11,13,22,23,30,33,42);
  GR[23]= _gr( 12, 1,2,3,4,5,6,17,18,22,23,30,42);
  GR[24]= _gr( -7, 1,3,5,18,22,30,40);
  GR[25]= _gr(  8, 1,3,5,18,22,23,30,39);
  GR[26]= _gr( -5, 1,5,14,22,30);
  GR[27]= _gr( 10, 1,3,5,6,22,23,24,26,30,42);
  GR[28]= _gr( -8, 1,3,5,22,24,26,30,40);
  GR[29]= _gr( 14, 1,2,3,4,5,6,17,18,22,23,30,39,40,42);
  GR[30]= _gr(  8, 1,5,6,14,22,30,39,42);
  GR[31]= _gr( -6, 1,5,14,22,30,40);
  GR[32]= _gr(  8, 1,4,5,14,22,23,30,34);
  GR[33]= _gr( 14, 1,3,5,6,15,17,22,23,24,26,29,30,40,42);
  GR[34]= _gr( -9, 1,3,5,11,13,18,22,30,32);
  GR[35]= _gr( 12, 1,4,5,6,14,22,23,30,34,39,40,42);
  GR[36]= _gr( 18, 1,2,3,4,5,6,11,12,13,17,18,22,23,30,31,32,33,42);
  GR[37]= _gr(-12, 1,3,5,11,13,16,18,22,30,32,35,40);
  GR[38]= _gr( 18, 1,3,4,5,6,11,13,15,17,18,21,22,23,30,32,33,35,39);
  GR[39]= _gr( 24, 1,2,3,4,5,6,11,12,13,15,16,17,18,21,22,23,30,31,32,33,35,39,40,42);
  GR[40]= _gr( 14, 1,3,5,6,7,9,11,23,24,26,27,30,33,42);
  GR[41]= _gr( 18, 1,3,5,6,7,9,11,13,16,20,22,23,24,26,27,30,33,42);
  GR[42]= _gr(-17, 1,3,5,7,9,11,13,16,18,20,22,24,26,27,30,35,40);
  GR[43]= _gr( 32, 1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,20,22,23,24,25,26,27,28,29,30,33,35,40,42);
  GR[44]= _gr(-22, 1,3,5,7,9,11,13,14,16,18,20,22,24,26,27,30,32,35,36,38,40,41);

  gr[0]=46; res = galmodp(pol,dpol,TYP,gr,GR);
  avma=av; if (!res) return 0;
  return EVEN? 44: 45;
}

/* BIBLIOTHEQUE POUR LE DEGRE 11 */

static long
closure11(GEN po)
{
  long rep;
  GEN r[NMAX];

  r[0] = cleanroots(po,PRMAX); preci(r,PREC);
  if (EVEN)
  {
  /* EVEN_11_1: */
    rep=isin_G_H(po,r,7,6);
    if (!rep) return 7;
  /* EVEN_11_2: */
    rep=isin_G_H(po,r,6,5);
    if (!rep) return 6;
  /* EVEN_11_3: */
    rep=isin_G_H(po,r,5,3);
    if (!rep) return 5;
  /* EVEN_11_4: */
    rep=isin_G_H(po,r,3,1);
    return rep? 1: 3;
  }
  else
  {
  /* ODD_11_1: */
    rep=isin_G_H(po,r,8,4);
    if (!rep) return 8;
  /* ODD_11_2: */
    rep=isin_G_H(po,r,4,2);
    return rep? 2: 4;
  }
}

static PERM
data11(long n1, GROUP *t)
{
  switch(n1)
  {
    case 5: *t=initgroup(N,1);
      return _cr(1, 2, 3, 7, 8, 6, 11, 5, 9, 4, 10);
    case 6: *t=initgroup(N,1);
      return _cr(1, 2, 3, 4, 6, 10, 11, 9, 7, 5, 8);
    case 7: *t=initgroup(N,2);
      _aff((*t)[2], 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10);
      return ID;
  }
  *t=initgroup(N,1); return ID;
}

static long
galoismodulo11(GEN pol, GEN dpol)
{
  long res, gr[6] = {0, 1, 1, 1, 1, 1};
  pari_sp av = avma;
  GEN *TYP = (GEN*)cgetg(EVEN? 9: 6, t_VEC);

  TYP[1] = _typ(1, 11);
  if (EVEN)
  {
    TYP[2] = _typ(3, 8,2,1);
    TYP[3] = _typ(3, 6,3,2);
    TYP[4] = _typ(3, 5,5,1);
    TYP[5] = _typ(5, 4,4,1,1,1);
    TYP[6] = _typ(5, 3,3,3,1,1);
    TYP[7] = _typ(7, 2,2,2,2,1,1,1);
    TYP[8] = _typ(11, 1,1,1,1,1,1,1,1,1,1,1);
  }
  else
  {
    TYP[2] = _typ(2, 10,1);
    TYP[3] = _typ(3, 5,5,1);
    TYP[4] = _typ(6, 2,2,2,2,2,1);
    TYP[5] = _typ(11, 1,1,1,1,1,1,1,1,1,1,1);
  }
  res = galmodp(pol,dpol,(GEN)TYP,gr,NULL);
  avma=av; if (!res) return 0;
  return EVEN? 7: 8;
}

/* return 1 iff we need to read a resolvent */
static long
init_isin(long n1, long n2, GROUP *tau, GROUP *ss, PERM *s0)
{
  long fl = 1;
  if (DEBUGLEVEL) {
    fprintferr("\n*** Entering isin_%ld_G_H_(%ld,%ld)\n",N,n1,n2); flusherr();
  }
  switch(N)
  {
    case 8:
      if ((n1==47 && n2==46) || (n1==44 && n2==40)) fl=0;
      *s0=data8(n1,n2,tau); break;
    case 9:
      if ((n1==31 && n2==29) || (n1==34 && n2==31) || (n1==33 && n2==30)) fl=0;
      *s0=data9(n1,n2,tau); break;
    case 10:
      if ((n1==45 && (n2==43||n2==39))
       || (n1==44 && (n2==42||n2==37))
       || (n1==43 && (n2==41||n2==33))
       || (n1==42 && n2==28)
       || (n1==41 && (n2==40||n2==27||n2==22))
       || (n1==40 && (n2==21||n2==11))
       || (n1==39 && (n2==38||n2==36||n2==29||n2==22))
       || (n1==38 && (n2==25||n2==12))
       || (n1==37 && (n2==34||n2==24))
       || (n1==36 && (n2==23||n2==11))
       || (n1==34 && n2==15)
       || (n1==33 && n2==27)
       || (n1==29 && (n2==25||n2==23||n2==5))
       || (n1==28 && n2==18)
       || (n1==27 && (n2==20||n2==19||n2==17))
       || (n1==25 && n2==4)
       || (n1==24 && n2==15)
       || (n1==23 && (n2==16||n2==3))
       || (n1==22 && (n2==12||n2==11||n2==5))
       || (n1==21 && (n2==10||n2==9))
       || (n1==17 && n2==5)
       || (n1==16 && n2==2)
       || (n1==14 && n2==1)
       || (n1==12 && n2==4)
       || (n1==11 && n2==3)
       || (n1==10 && n2==4)
       || (n1== 9 && n2==3)
       || (n1== 6 && n2==1)
       || (n1== 5 && n2==3)) fl = 0;
      *s0=data10(n1,n2,tau); break;
    case 11:
      *s0=data11(n1,tau); break;
  }
  *ss = lirecoset(n1,n2,N); return fl;
}

static long
isin_G_H(GEN po, GEN *r, long n1, long n2)
{
  long nbv,nbm,i,j;
  PERM s0, ww;
  RESOLVANTE a;
  GROUP ss,tau;

  if (init_isin(n1,n2, &tau, &ss, &s0))
    a = lireresolv(n1,n2,N,&nbv,&nbm);
  else
    { a = NULL; nbm=n1; nbv=n2; }
  ww = check_isin(po,r,nbm,nbv,a,tau,ss,s0);
  if (getpreci(r) != PREC) preci(r,PREC);
  free(ss); free(tau); if (a) free(a);
  if (ww)
  {
    long z[NMAX+1];

    if (DEBUGLEVEL)
    {
      fprintferr("\n    Output of isin_%ld_G_H(%ld,%ld): %ld",N,n1,n2,n2);
      fprintferr("\n    Reordering of the roots: "); printperm(ww);
      flusherr();
    }
    for (i=0; i<TSCHMAX; i++)
    {
      GEN p1 = r[i];
      for (j=1; j<=N; j++) z[j]=p1[(int)ww[j]];
      for (j=1; j<=N; j++) p1[j]=z[j];
    }
    free(ww); return n2;
  }
  if (DEBUGLEVEL)
  {
    fprintferr("    Output of isin_%ld_G_H(%ld,%ld): not included.\n",N,n1,n2);
    flusherr();
  }
  return 0;
}

GEN
galoisbig(GEN pol, long prec)
{
  GEN dpol, res = cgetg(4,t_VEC);
  long *tab, t;
  pari_sp av = avma;
  long tab8[]={0,
    8,8,8,8,8,16,16,16,16,16, 16,24,24,24,32,32,32,32,32,32,
    32,32,48,48,56,64,64,64,64,64, 64,96,96,96,128,168,168,192,192,192,
    192,288,336,384,576,576,1152,1344,20160,40320};
  long tab9[]={0,
    9,9,18,18,18,27,27,36,36,54, 54,54,54,72,72,72,81,108,144,162,
    162,162,216,324,324,432,504,648,648,648, 1296,1512,181440,362880};
  long tab10[]={0,
    10,10,20,20,40,50,60,80,100,100, 120,120,120,160,160,160,200,200,200,200,
    200,240,320,320,320,360,400,400,640,720, 720,720,800,960,1440,
    1920,1920,1920,3840,7200,14400,14400,28800,1814400,3628800};
  long tab11[]={0, 11,22,55,110,660,7920,19958400,39916800};

  N = degpol(pol); dpol = ZX_disc(pol); EVEN = carreparfait(dpol);
  prec += 2 * (MEDDEFAULTPREC-2);
  PREC = prec;
  if (DEBUGLEVEL)
  {
    fprintferr("Galoisbig (prec=%ld): reduced polynomial #1 = %Z\n",prec,pol);
    fprintferr("discriminant = %Z\n", dpol);
    fprintferr("%s group\n", EVEN? "EVEN": "ODD"); flusherr();
  }
  PRMAX = prec+5; TSCHMAX = 1; ID[0] = N;
  switch(N)
  {
    case 8: t = galoismodulo8(pol,dpol);
      if (!t) t = closure8(pol);
      tab=tab8; break;

    case 9: t = galoismodulo9(pol,dpol);
      if (!t) t = closure9(pol);
      tab=tab9; break;

    case 10: t = galoismodulo10(pol,dpol);
      if (!t) t = closure10(pol);
      tab=tab10; break;

    case 11: t = galoismodulo11(pol,dpol);
      if (!t) t = closure11(pol);
      tab=tab11; break;

    default: err(impl,"galois in degree > 11");
      return NULL; /* not reached */
  }
  avma = av;
  res[1]=lstoi(tab[t]);
  res[2]=lstoi(EVEN? 1 : -1);
  res[3]=lstoi(t); return res;
}
