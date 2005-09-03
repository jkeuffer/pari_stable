/* $Id$

Copyright (C) 2005  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/********************************************************************/
/**                                                                **/
/**  INTERFACE TO JOHN CREMONA ELLIPTIC CURVES DATABASE            **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static long
strtoclass(const char *s)
{
  int c=0;
  while (*s && *s<='9') s++;
  if (!*s) return -1;
  while ('A'<=*s && *s<='Z')
    c=26*c+*(s++)-'A';
  return c;
}

/*Take a curve name like "100A2" and set
 * f to the conductor, (100)
 * c to the isogeny class (in base 26), ("A" or 1)
 * i to the curve index (2).
 * return 0 if garbage is found at the end.
 */
static int
ellparsename(const char *s, long *f, long *c, long *i)
{
  *f=-1; *c=-1; *i=-1;
  if (*s<'0' || *s>'9') return !*s;
  *f=0;
  while ('0'<=*s && *s<='9')
    *f=10**f+*(s++)-'0';
  if (*s<'A' || *s>'Z') return !*s;
  *c=0;
  while ('A'<=*s && *s<='Z')
    *c=26**c+*(s++)-'A';
  if (*s<'0' || *s>'9') return !*s;
  *i=0;
  while ('0'<=*s && *s<='9')
    *i=10**i+*(s++)-'0';
  return !*s;
}

GEN
ellcondfile(long f)
{
  long n=f/1000;
  char *s = gpmalloc(strlen(pari_datadir) + 13 + 20);
  FILE *stream;
  GEN V;
  sprintf(s, "%s/elldata/ell%ld", pari_datadir, n);
  stream = fopen(s,"r");
  if (!stream) 
    err(talker,"Elliptic curves files not available for conductor %ld\n"
               "[missing %s]",f,s);
  V = gp_read_stream(stream);
  if (!V || typ(V)!=t_VEC )
    err(talker,"Elliptic files %s not compatible\n",s);
  fclose(stream);
  free(s); 
  return V;
}

GEN
ellcondlist(long f)
{
  pari_sp ltop=avma;
  GEN  V=ellcondfile(f);
  long i;
  for (i=1; i<lg(V); i++)
    if (cmpis(gmael(V,i,1), f)>=0)
      break;
  if (i==lg(V) || !equalis(gmael(V,i,1), f))
  {
    avma=ltop; 
    return cgetg(1,t_VEC);
  }
  return gerepilecopy(ltop, vecslice(gel(V,i),2, lg(gel(V,i))-1)); 
}

static GEN 
ellsearchbyname(GEN V, GEN name)
{
  long j;
  for (j=1; j<lg(V); j++)
    if (gequal(gmael(V,j,1), name))
      return gel(V,j);
  err(talker,"No such elliptic curve");
  return NULL;
}

static GEN
ellsearchbyclass(GEN V, long c)
{
  long i,j,n;
  GEN res;
  for (n=0,j=1; j<lg(V); j++)
    if (strtoclass(GSTR(gmael(V,j,1)))==c)
      n++;
  res=cgetg(n+1,t_VEC);
  for (i=1,j=1; j<lg(V); j++)
    if (strtoclass(GSTR(gmael(V,j,1)))==c)
      res[i++]=V[j];
  return res;
}

GEN
ellsearch(GEN A)
{
  pari_sp ltop=avma;
  long f, c, i;
  GEN V;
  if (typ(A)==t_INT)
  {
    f=itos(A); 
    c=-1; 
    i=-1;
  } else if (typ(A)==t_STR) {
    if (!ellparsename(GSTR(A),&f,&c,&i))
      err(talker,"Incorrect curve name in ellsearch");
  } else {
    err(typeer,"ellsearch");
    return NULL;
  }
  V=ellcondlist(f);
  if (c<0) 
    return V;
  if (i<0) 
    return gerepilecopy(ltop, ellsearchbyclass(V,c));
  return gerepilecopy(ltop, ellsearchbyname(V,A));
}

GEN
ellsearchcurve(GEN name)
{
  pari_sp ltop=avma;
  long f, c, i;
  if (!ellparsename(GSTR(name),&f,&c,&i))
    err(talker,"Incorrect curve name in ellsearch");
  if (f<0 || c<0 || i<0)
    err(talker,"Incomplete curve name in ellsearch");
  return gerepilecopy(ltop, ellsearchbyname(ellcondlist(f), name));
}

GEN
ellidentify(GEN E)
{
  pari_sp ltop=avma;
  GEN V, M, G = ellglobalred(E);
  long j;
  V = ellcondlist(itos(gel(G,1)));
  M = coordch(vecslice(E,1,5),gel(G,2));
  for (j=1; j<lg(V); j++)
    if (gequal(gmael(V,j,2), M))
      return gerepilecopy(ltop, mkvec2(gel(V,j),gel(G,2)));
  err(talker,"No such elliptic curve in database");
  return NULL;
}

GEN
ellgenerators(GEN E)
{
  pari_sp ltop=avma;
  GEN V=ellidentify(E);
  GEN gens=gmael(V,1,3);
  GEN W=pointchinv(gens,gel(V,2));
  return gerepileupto(ltop,W);
}
