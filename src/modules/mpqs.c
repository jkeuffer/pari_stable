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

/* Written by Thomas Papanikolaou and Xavier Roblot
 *
 * Implementation of the Self-Initializing Multi-Polynomial Quadratic Sieve
 * based on code developed as part of the LiDIA project
 * (http://www.informatik.tu-darmstadt.de/TI/LiDIA/Welcome.html)
 */
#include "pari.h"

#ifndef SEEK_SET
#  define SEEK_SET 0
#endif

#ifdef __CYGWIN32__
/* otherwise fseek() goes crazy due to silent \n <--> LF translations */
#  define WRITE "wb"
#  define READ "rb"
#else
#  define WRITE "w"
#  define READ "r"
#endif

#ifdef MPQS_DEBUG_VERYVERBOSE
#  ifndef MPQS_DEBUG_VERBOSE
#  define MPQS_DEBUG_VERBOSE
#  endif
#endif

#ifdef MPQS_DEBUG_VERBOSE
#  ifndef MPQS_DEBUG
#  define MPQS_DEBUG
#  endif
#endif

#define MPQS_STRING_LENGTH         (4 * 1024)
#define MPQS_CANDIDATE_ARRAY_SIZE  2000
#define MPQS_PRIMES_FOR_MULTIPLIER 5
/* `large primes' must be smaller than
 *   max(MPQS_LP_BOUND, largest_prime_in_FB) * MPQS_LP_FACTOR
 */
#define MPQS_LP_BOUND              125000 /* works for 32 and 64bit */
#define MPQS_LP_FACTOR             80

typedef ulong *mpqs_gauss_row;
typedef long *mpqs_gauss_indices;
typedef mpqs_gauss_row *mpqs_gauss_matrix;

/* BEGIN: global variables to disappear as soon as possible */
/* names for temp. files, set in mpqs_get_filename */
static char *FREL_str;
static char *FNEW_str;
static char *LPREL_str;
static char *LPNEW_str;
static char *TMP_str;
static char *COMB_str;

/* our own pointer to PARI's or to our own prime diffs table.
 * NB the latter is never freed, unless we need to replace it with
 * an even larger one. */
static byteptr mpqs_diffptr = NULL;
static long mpqs_prime_count = 0;

/* END: global variables to disappear as soon as possible */

/******************************/

/**
 ** determines a unique name for a file based on a short nickname
 **/

/* name is allocated on the stack */
static char *
mpqs_get_filename(char *s)
{
  char *buf;

  s = pari_unique_filename(s);
  buf = (char*) new_chunk((strlen(s) / sizeof(long)) + 2);
  return strcpy(buf, s);
}

/**
 ** compares two `large prime' relations according to their
 ** first element (the large prime itself).
 **/

static int
mpqs_relations_cmp(const void *a, const void *b)
{
  char **sa = (char **) a;
  char **sb = (char **) b;
  long qa = strtol(*sa, NULL, 10);
  long qb = strtol(*sb, NULL, 10);
  /* atol() isn't entirely portable for the Full Relations case where the
     strings of digits are too long to fit into a long --GN */
  if (qa < qb) return -1;
  else if (qa > qb) return 1;
  else return strcmp(*sa, *sb);
}

/**
 ** Given a file "filename" containing full or `large prime' relations,
 ** this function rearranges the file so that relations are sorted by
 ** their first elements. Works also for sorting full relations.
 ** Works in memory, discards duplicate lines, and overwrites the
 ** original file.
 **/

#define bummer(fn) err(talker, "error whilst writing to file %s", fn)
#define min_bufspace 120	/* use new buffer when < min_bufspace left */
#define buflist_size 1024	/* size of list-of-buffers blocks */

static long
mpqs_sort_lp_file(char *filename)
{
  pariFILE *pTMP;
  FILE *TMP;
  char *old_s, **sort_table = (char**)avma, *buf, *cur_line;
  static char **buflist_head = NULL;
  char **buflist, **next_buflist;
  long i, j, bufspace, length, count;
  pari_sp av=avma;

  if (!buflist_head)
  {
    buflist_head = (char **) gpmalloc(buflist_size * sizeof(char *));
    buflist = buflist_head;
    *buflist++ = NULL;		/* flag this as last and only buflist block */
  }
  else
    buflist = buflist_head + 1;
  /* this block will never be freed, and extra blocks may be allocated as
     needed and linked ahead of it.  NB it turns out that whilst extra
     buflist blocks might have been needed when we were still sorting
     entire FREL files  (more than 1023 buffers, corresponding to about
     20000 lines of c.200 characters),  they should never be touched now
     that we only sort LPNEW and FNEW files, which are rather shorter.
     But the code might as well stay around for paranoia, or for future
     upgrades to handling even larger numbers (and factor bases and thus
     relations files).  It only costs one comparison per buffer allocation.
     --GN */

  pTMP = pari_fopen(filename, READ);
  TMP = pTMP->file;
  /* get first buffer and read first line, if any, into it */
  buf = (char *) gpmalloc(MPQS_STRING_LENGTH * sizeof(char));
  cur_line = buf;
  bufspace = MPQS_STRING_LENGTH;

  if (fgets(cur_line, bufspace, TMP) == NULL)
  {				/* file empty */
    avma = av;
    free(buf);
    pari_fclose(pTMP);
    return 0;
  }
  /* enter first buffer into buflist */
  *buflist++ = buf;		/* can't overflow the buflist block */
  length = strlen(cur_line) + 1; /* count the \0 byte as well */
  bufspace -= length;

  /* at start of loop, one line from the file is sitting in cur_line inside
     buf, the next will go into cur_line + length, and there's room for
     bufspace further characters in buf.
     The loop reads another line if one exists, and if this overruns the
     current buffer, it allocates a fresh one --GN */

  for (i=0, sort_table--; /* until end of file */; i++, sort_table--)
  {
    /* sort_table is allocated on the stack, 0x100 cells at a time. Hence the
     * stack must be left alone in the rest of the loop to keep the array
     * connected. In particular, buffers can't be new_chunk'ed --KB */
    if ((i & 0xff) == 0) (void)new_chunk(0x100);
    *sort_table = cur_line;
    cur_line += length;

    /* if very little room is left, allocate a fresh buffer before
       attempting to read a line, and remember to free it if no
       further line is forthcoming.  This avoids some copying of
       partial lines --GN */
    if (bufspace < min_bufspace)
    {
      if (
#ifdef MPQS_DEBUG
	  1 ||
#endif
	  DEBUGLEVEL >= 7)
	fprintferr("MQPS: short of space -- another buffer for sorting\n");
      buf = (char *) gpmalloc(MPQS_STRING_LENGTH * sizeof(char));
      cur_line = buf;
      bufspace = MPQS_STRING_LENGTH;
      if (fgets(cur_line, bufspace, TMP) == NULL)
      {
	free(buf); break;
      }
      else
      {
	/* remember buffer for later deallocation */
	if (buflist - buflist_head >= buflist_size)
	{
	  /* need another buflist block */
	  next_buflist =
	    (char **) gpmalloc(buflist_size * sizeof(char *));
	  *next_buflist = (char *)buflist_head; /* link */
	  buflist_head = next_buflist;
	  buflist = buflist_head + 1;
	}
	*buflist++ = buf;
	length = strlen(cur_line) + 1;
	bufspace -= length;
	continue;
      }
    }

    /* normal case:  try fitting another line into the current buffer,
       break if none exists */
    if (fgets(cur_line, bufspace, TMP) == NULL) break;
    length = strlen(cur_line) + 1;
    bufspace -= length;

    /* check whether we got the entire line or only part of it */
    if (bufspace == 0 && cur_line[length-2] != '\n')
    {
      long lg1;
      if (
#ifdef MPQS_DEBUG
	  1 ||
#endif
	  DEBUGLEVEL >= 7)
	fprintferr("MQPS: line wrap -- another buffer for sorting\n");
      buf = (char *) gpmalloc(MPQS_STRING_LENGTH * sizeof(char));
      /* remember buffer for later deallocation */
      if (buflist - buflist_head >= buflist_size)
      {
	/* need another buflist block */
	next_buflist =
	  (char **) gpmalloc(buflist_size * sizeof(char *));
	*next_buflist = (char *)buflist_head; /* link */
	buflist_head = next_buflist;
	buflist = buflist_head + 1;
      }
      *buflist++ = buf;

      /* copy what we've got to the new buffer */
      (void)strcpy(buf, cur_line); /* cannot overflow */
      cur_line = buf + length - 1; /* point at the \0 byte */
      bufspace = MPQS_STRING_LENGTH - length + 1;
      /* read remainder of line */
      if (fgets(cur_line, bufspace, TMP) == NULL)
	err(talker,"MPQS: relations file truncated?!\n");
      lg1 = strlen(cur_line);
      length += lg1;		/* we already counted the \0 once */
      bufspace -= (lg1 + 1);	/* but here we must take it into account */
      cur_line = buf;		/* back up to the beginning of the line */
    }
  } /* for */

  pari_fclose(pTMP);

#if 0				/* caught above, can no longer happen */
  if (i == 0)
  {
    avma = av; return 0;
  }
#endif

  /* sort the whole lot in place by swapping pointers */
  qsort(sort_table, i, sizeof(char *), mpqs_relations_cmp);

  /* copy results back to the original file, skipping exact duplicates */
  pTMP = pari_fopen(filename, WRITE); /* NOT safefopen */
  TMP = pTMP->file;
  old_s = sort_table[0];
  if (fputs(sort_table[0], TMP) < 0)
    bummer(filename);
  count = 1;
  for(j = 1; j < i; j++)
  {
    if (strcmp(old_s, sort_table[j]) != 0)
    {
      if (fputs(sort_table[j], TMP) < 0)
	bummer(filename);
      count++;
    }
    old_s = sort_table[j];
  }
  pari_fclose(pTMP);
  if (
#ifdef MPQS_DEBUG
      1 ||
#endif
      DEBUGLEVEL >= 6)
    fprintferr("MPQS: done sorting one file.\n");

  /* deallocate buffers and any extraneous buflist blocks except the first */
  while (*--buflist)
  {
    if (buflist != buflist_head) /* not a linkage pointer */
      free((void *) *buflist);	/* free a buffer */
    else			/* linkage pointer */
    {
      next_buflist = (char **)(*buflist);
      free((void *)buflist_head); /* free a buflist block */
      buflist_head = next_buflist;
      buflist = buflist_head + buflist_size;
    }
  }
#if 0
  for (j = 0; j < i; j++)
  {
    buf = (char *)(sort_table[j]) - 1;
    if (*buf)			/* check: deallocation flag or \0 ? */
      free(buf);
  }
#endif
  avma = av; return count;
}

/**
 ** appends contents of file fp1 to file fp of name filename
 ** (auxiliary routine for merge sort) and returns number of
 ** lines copied.
 ** fp assumed open for appending and fp1 for reading;  fp will
 ** be closed afterwards.
 **/

static long
mpqs_append_file(pariFILE *f, FILE *fp1)
{
  FILE *fp = f->file;
  char line[MPQS_STRING_LENGTH];
  long c = 0;
  while (fgets(line, MPQS_STRING_LENGTH, fp1) != NULL)
  {
    if (fputs(line, fp) < 0)
      err(talker, "error whilst appending to file %s", f->name);
    c++;
  }
  if (fflush(fp))
    err(warner, "error whilst flushing file %s", f->name);
  pari_fclose(f);
  return c;
}

/**
 ** Does a merge-sort on the files LPREL and LPNEW;
 ** assumes that LPREL and LPNEW are already sorted.
 ** Creates/truncates the TMP file, writes result to it and closes it
 ** (via a call to mpqs_append_file()).
 ** Instead of LPREL, LPNEW we may also call this with FREL, FNEW.
 ** In the latter case mode should be 1 (and we return the count of
 ** all full relations), in the former 0 (and we return the count
 ** of frels we expect to be able to combine out of the present lprels).
 ** Moreover, if mode is 0, the combinable lprels are written out to a
 ** separate file (COMB) which we also create and close (the caller
 ** will find it exists iff our return value is nonzero), and we keep
 ** only one occurrence of each `large prime' in TMP (i.e. in the future
 ** LPREL file). --GN
 **/

#define swap_lines { \
		       line_tmp = line_new_old; \
		       line_new_old = line_new; \
		       line_new = line_tmp; \
		   }
		
static long
mpqs_mergesort_lp_file0(FILE *LPREL, FILE *LPNEW, long mode)
{
  /* TMP (renamed upon return) and COMB (deleted upon return) guaranteed not
   * to exist yet  --> safefopen for both temp files */
  pariFILE *pTMP = pari_safefopen(TMP_str, WRITE);
  FILE *TMP = pTMP->file;
  pariFILE *pCOMB = NULL;
  FILE *COMB = NULL; /* gcc -Wall */
  char line1[MPQS_STRING_LENGTH], line2[MPQS_STRING_LENGTH];
  char line[MPQS_STRING_LENGTH];
  char *line_new = line1, *line_new_old = line2, *line_tmp;
  long q_new, q_new_old = -1, q, i = 0, c = 0;
  long comb_in_progress;

  /* if LPNEW is empty, copy LPREL to TMP.  Could be done by a rename
     if we didn't want to count the lines (again)... however, this
     case will not normally happen */

  if (fgets(line_new, MPQS_STRING_LENGTH, LPNEW) == NULL)
  {
    i = mpqs_append_file(pTMP, LPREL);
    return (mode ? i : 0);
  }
  /* we now have a line_new from LPNEW */

  /* if LPREL is empty, copy LPNEW to TMP... almost. */

  if (fgets(line, MPQS_STRING_LENGTH, LPREL) == NULL)
  {
    if (fputs(line_new, TMP) < 0)
      bummer(TMP_str);
    if (mode)			/* full relations mode */
    {
      i = mpqs_append_file(pTMP, LPNEW);
      return i + 1;		/* COMB cannot be open here */
    }

    /* LP mode:  check for combinable relations */
    q_new_old = atol(line_new);
    /* we need to retain a copy of the old line just for a moment, because
       we may yet have to write it to COMB, too.  Do this simply by swapping
       the two buffers */
    swap_lines;
    comb_in_progress = 0;
    i = 0;

    while (fgets(line_new, MPQS_STRING_LENGTH, LPNEW) != NULL)
    {
      q_new = atol(line_new);
      if (q_new_old == q_new)
      {
	/* found combinables, check whether we're already busy on this
	   particular `large prime' */
	if (!comb_in_progress)
	{
	  /* if not, write first line to COMB, creating and opening the
	     file first if it isn't open yet */
	  if (!pCOMB)
	  {
	    pCOMB = pari_safefopen(COMB_str, WRITE);
	    COMB = pCOMB->file;
	  }
	  if (fputs(line_new_old, COMB) < 0)
	    bummer(COMB_str);
	  comb_in_progress = 1;
	}
	/* in any case, write the current line, and count it */
	if (fputs(line_new, COMB) < 0)
	  bummer(COMB_str);
	i++;
      }
      else
      {				/* not combinable */
	q_new_old = q_new;
	comb_in_progress = 0;
	/* and dump it to the TMP file */
	if (fputs(line_new, TMP) < 0)
	  bummer(TMP_str);
	/* and stash it away for a moment */
	swap_lines;
	comb_in_progress = 0;
      }
    } /* while */
    if (pCOMB) pari_fclose(pCOMB);
    pari_fclose(pTMP);
    return i;
  }

  /* normal case: both LPNEW and LPREL are not empty */
  q_new = atol(line_new);
  q = atol(line);

  for(;;)			/* main merging loop */
  {
    comb_in_progress = 0;
    i = 0;

    /* first the harder case:  let LPNEW catch up with LPREL, and possibly
       overtake it, checking for combinables coming from LPNEW alone */

    while (q > q_new)
    {
      if (mode || !comb_in_progress)
      {
	if (fputs(line_new, TMP) < 0)
	  bummer(TMP_str);
      }
      if (mode)
	c++;			/* in FREL mode, count lines written */
      else if (!comb_in_progress)
      {
	q_new_old = q_new;
	swap_lines;
      }
      if (fgets(line_new, MPQS_STRING_LENGTH, LPNEW) == NULL)
      {
	if (fputs(line, TMP) < 0)
	  bummer(TMP_str);
	if (mode) c++; else c += i;
	i = mpqs_append_file(pTMP, LPREL);
	if (pCOMB) pari_fclose(pCOMB);
	return (mode ? c + i : c);
      }
      q_new = atol(line_new);
      if (mode) continue;
      /* LP mode only: */
      if (q_new_old != q_new)
      {				/* not combinable */
	comb_in_progress = 0;
	/* next loop iteration will deal with it, or the loop may end */
      }
      else
      {
	/* found combinables, check whether we're already busy on this
	   `large prime' */
	if (!comb_in_progress)
	{
	  if (!pCOMB)
	  {
	    pCOMB = pari_safefopen(COMB_str, WRITE);
	    COMB = pCOMB->file;
	  }
	  if (fputs(line_new_old, COMB) < 0)
	    bummer(COMB_str);
	  comb_in_progress = 1;
	}
	/* in any case, write the current line, and count it */
	if (fputs(line_new, COMB) < 0)
	  bummer(COMB_str);
	i++;
      }
    } /* while q > q_new */

    /* q <= q_new */

    if (!mode) c += i;		/* accumulate count of combinables */
    i = 0;			/* and clear it */
    comb_in_progress = 0;	/* redundant */

    /* now let LPREL catch up with LPNEW, and possibly overtake it */

    while (q < q_new)
    {
      if (fputs(line, TMP) < 0)
	bummer(TMP_str);
      if (mode) c++;
      if (fgets(line, MPQS_STRING_LENGTH, LPREL) == NULL)
      {
	if (fputs(line_new, TMP) < 0)
	  bummer(TMP_str);
	i = mpqs_append_file(pTMP, LPNEW);
	if (pCOMB) pari_fclose(pCOMB);
	return (mode ? c + i + 1 : c);
      }
      else
	q = atol(line);
    }

    /* q >= q_new */

    /* Finally, it may happen that q == q_new, indicating combinables whose
       `large prime' is already represented in LPREL, and appears now once
       or more often in LPNEW.  Thus in this sub-loop we advance LPNEW.
       The `line' from LPREL is left alone, and will be written to TMP the
       next time around the main for loop;  we only write it to COMB here --
       unless all we find is an exact duplicate of the line we already have,
       that is.  (There can be at most one such, and if so it will simply be
       discarded, whether we are in LP or full relations mode.) */

    while (q == q_new)
    {
      if (strcmp(line_new, line) == 0)
      {
	/* duplicate -- move right ahead to the next LPNEW line */
	;			/* do nothing here */
      }	/* end duplicate case */
      else if (mode)
      {
	/* full relations mode: write line_new out first, keep line */
	if (fputs(line_new, TMP) < 0)
	  bummer(TMP_str);
	c++;
      }	/* end full relations case */
      else
      {
	/* LP mode, and combinable relation */
	if (!comb_in_progress)
	{
	  if (!pCOMB)
	  {
	    pCOMB = pari_safefopen(COMB_str, WRITE);
	    COMB = pCOMB->file;
	  }
	  if (fputs(line, COMB) < 0)
	    bummer(COMB_str);
	  comb_in_progress = 1;
	}
	if (fputs(line_new, COMB) < 0)
	  bummer(COMB_str);
	i++;
      }	/* end combinable LP case */
      /* NB comb_in_progress is cleared by q_new becoming bigger than q,
	 and thus the current while loop terminating, the next time through
	 the main for loop */

      /* common ending: get another line_new, if any */
      if (fgets(line_new, MPQS_STRING_LENGTH, LPNEW) == NULL)
      {
	if (fputs(line, TMP) < 0)
	  bummer(TMP_str);
	if (mode) c++; else c += i;
	i = mpqs_append_file(pTMP, LPREL);
	if (pCOMB) pari_fclose(pCOMB);
	return (mode ? c + i : c);
      }
      else
	q_new = atol(line_new);
    } /* while */

    if (!mode) c += i;		/* accumulate count of combinables */
  } /* for */
}

static long
mpqs_mergesort_lp_file(char *REL_str, char *NEW_str, long mode)
{
  pariFILE *pREL = pari_fopen(REL_str, READ);
  pariFILE *pNEW = pari_fopen(NEW_str, READ);
  long tp = mpqs_mergesort_lp_file0(pREL->file, pNEW->file, mode);

  pari_fclose(pREL);
  pari_fclose(pNEW);
  pari_unlink(REL_str);
  if (rename(TMP_str,REL_str))
    err(talker, "can\'t rename file %s to %s", TMP_str, REL_str);
  if (
#ifdef MPQS_DEBUG
	   1 ||
#endif
	   DEBUGLEVEL >= 6)
    fprintferr("MPQS: renamed file %s to %s\n", TMP_str, REL_str);
  return tp;
}

/******************************/
/**
 ** return next prime larger than p, using *primes_ptr on the
 ** diffptr table first and pari's other wits after that
 **/

static byteptr
mpqs_iterate_primes(long *p, byteptr primes_ptr)
{
  long prime = *p;
  if (*primes_ptr)
    NEXT_PRIME_VIADIFF(prime,primes_ptr);
  else
  {
    pari_sp av = avma;
    prime = itos(nextprime(stoi(prime + 1)));
    avma = av;
  }
  *p = prime;
  return primes_ptr;
}


/**
 ** return the multiplier k for N to use in MPQS
 **/

long
mpqs_find_k(GEN N, long tries)
{
  static long cand_table[] = { 1,3,5,7,11,13,15,17,19,21,23,
                               29,31,33,35,37,39,41,43,47,51,53,
                               55,57,59,61,65,67,69,71,73,79,83,
                               85,89,91,93,95,97,101,103,105,107,
                               109,113,127,131,137,139};
  pari_sp av = avma;
  long best_k = 1, k, p, N_mod_4 = smodis(N, 4), x;
  GEN kN;
  double best_value = 1, value, dp;
  long i, j;
  byteptr primes_ptr;

  for (i = 0; i < MPQS_PRIMES_FOR_MULTIPLIER; i++)
  {
    k = cand_table[i];
    x = (k * N_mod_4) % 4;
    if (x == 1)
    {
      value = -0.7 * log2 ((double) k);
      kN = mulis(N, k);
      if (smodis(kN, 8) == 1)
	value += 1.38629;

      j = 0; p = 0;
      primes_ptr = diffptr;
      while (j <= tries)
      {
	primes_ptr = mpqs_iterate_primes(&p, primes_ptr);
	if (kross(smodis(kN, p), p) == 1)
        {
	  j++;
	  dp = log2((double) p) / p;
	  value += (k % p == 0) ? dp : 2 * dp;
	}
      }

      if (value > best_value)
      {
	best_value = value;
	best_k = k;
      }
    }
  }
  avma = av; return best_k;
}

/******************************/
/**
 ** guesstimate up to what size we're going to need precomputed
 ** small primes
 **/

static long
mpqs_find_maxprime(long size)
{
  double x;

  if (size < 16000)
    return 176000;

  x  = log((double)size);
  x += log(x);
  x -= 0.9427;
  x *= size;

  return (long)x;
}

/**
 ** return the number of primes initialized in PARI
 **/

static long
mpqs_count_primes(void)
{
  byteptr p = mpqs_diffptr;
  long gaps = 0;

  for ( ; *p; p++)
      if (*p == DIFFPTR_SKIP)
	  gaps++;
  return (p - mpqs_diffptr - gaps);
}

/**
 ** create a factor base of size primes p_i with the
 ** property that legendre(k*N, p_i) == 0, 1
 ** FB[0] contains the size of the factor base;  FB[FB[0]+1] is the
 ** last prime p_i.
 ** FB[1] contains -1 which allows to handle negative values of Q(x).
 ** If a prime factor of N is found during the construction, it
 ** is returned in f, otherwise f = 0  (such a factor will necessarily
 ** fit into a C long).
 **/

static long*
mpqs_create_FB(long size, GEN kN, long k, long *f)
{
  long i, kr, p = 0;
  long *FB;
  byteptr primes_ptr;

  FB = (long *) calloc(size + 3, sizeof(long));
  if (!FB) err(memer);
  FB[0] = size;
  FB[1] = -1;
  /* pick up PARI's current differences-of-small-primes array */
  /* unless we already have our own.  We must then reset it to NULL */
  /* so we will not use a stale one the next time we are called */
  if (!mpqs_diffptr) mpqs_diffptr = diffptr;

  if ((mpqs_prime_count ? mpqs_prime_count : mpqs_count_primes())
      < 3 * size)
  {
    long newsize = 3 * mpqs_find_maxprime(size);
    if (mpqs_diffptr != diffptr) free((void *) mpqs_diffptr);
    if (DEBUGLEVEL >= 2)
    {
      fprintferr("MPQS: precomputing auxiliary primes up to %ld\n",
		 newsize);
    }
    mpqs_diffptr = initprimes(newsize);
    /* count 'em once and remember the result */
    mpqs_prime_count = mpqs_count_primes();
  }

  if (
#ifdef MPQS_DEBUG
      1 ||
#endif
      DEBUGLEVEL >= 7)
    fprintferr("MPQS: FB [-1");
  primes_ptr = mpqs_diffptr;
  for (i = 2; i < size + 2; )
  {
    primes_ptr = mpqs_iterate_primes(&p, primes_ptr);

    /* testing p!=k was only correct because MPQS_PRIMES_FOR_MULTIPLIER
       is so small that the composite values k > 1 will never be chosen.
       Fixing this just in case someone increases that parameter one day...
       --GN */
    if (p > k || k%p)
    {
      kr = kross(smodis(kN, p), p);
      if (kr != -1)
      {
	if (kr == 0)
	{
	  if (
#ifdef MPQS_DEBUG
	      1 ||
#endif
	      DEBUGLEVEL >= 7)
	    fprintferr(",%ld...] Wait a second --\n", p);
	  *f = p;
	  return FB;
	}
	if (
#ifdef MPQS_DEBUG
	    1 ||
#endif
	    DEBUGLEVEL >= 7)
	  fprintferr(",%ld", p);
	FB[i] = p, i++;
      }
    }
  }

  if (
#ifdef MPQS_DEBUG
      1 ||
#endif
      DEBUGLEVEL >= 7)
  {
    fprintferr("]\n");
    flusherr();
  }

  FB[i] = 0;
  if (DEBUGLEVEL >= 6)
    fprintferr("MPQS: last available index in FB is %ld\n", i - 1);

  *f = 0;
  return FB;
}

/******************************/

/**
 ** see below for the format of the parameter table.
 ** These values are somewhat experimental and can be improved by
 ** further extensive testing.
 ** Tentative entries for 9...14 digits by GN, entry for 15 changed
 ** Tentative entries for 81...100 digits by GN, entry for 74 changed
 ** total_no_of_primes_for_A (penultimate entries in each row) increased
 ** throughout, partly so as to offset the effect of changed bin_index
 ** increment strategy --GN
 ** Added entries to govern sort intervals, commented out unused numbers
 ** of digits --GN
 **/

static double
mpqs_parameters[99][8] =
{
  {  /*9*/ 0.8,     900,    20,  3, 13,  2, 70,  8},
  { /*10*/ 0.8,     900,    21,  3, 12,  2, 70,  8},
  { /*11*/ 0.8,     920,    22,  3, 12,  2, 70,  6},
  { /*12*/ 0.8,     960,    24,  3, 12,  2, 70,  6},
  { /*13*/ 0.8,    1020,    26,  3, 12,  2, 70,  6},
  { /*14*/ 0.8,    1100,    29,  3, 12,  2, 70,  6},
  { /*15*/ 0.8,    1200,    32,  3, 12,  2, 60,  8},
  { /*16*/ 0.8,    1400,    35,  3, 12,  2, 60,  8},
  { /*17*/ 0.8,    3000,    40,  3, 12,  2, 60,  8},
  { /*18*/ 0.8,    3000,    60,  3, 12,  2, 50, 10},
  { /*19*/ 0.8,    3600,    80,  3, 13,  2, 50, 10},
  { /*20*/ 0.8,    4000,   100,  3, 13,  2, 40, 10},
  { /*21*/ 0.8,    4300,   100,  3, 13,  2, 40, 10},
  { /*22*/ 0.8,    4500,   120,  3, 13,  3, 40, 10},
  { /*23*/ 0.8,    4800,   140,  3, 14,  3, 30, 10},
  { /*24*/ 0.8,    5000,   160,  3, 14,  4, 30, 10},
  { /*25*/ 0.8,    5000,   180,  3, 14,  4, 30, 10},
  { /*26*/ 0.9,    6000,   200,  5, 10,  4, 30, 10},
  { /*27*/ 1.17,   6000,   220,  5, 10,  5, 30, 10},
  { /*28*/ 1.17,   6500,   240,  5, 10,  5, 30, 10},
  { /*29*/ 1.17,   6500,   260,  5, 10,  5, 30, 10},
  { /*30*/ 1.36,   7000,   325,  5, 10,  5, 20, 10},
  { /*31*/ 1.36,   7000,   355,  5, 10,  5, 20, 10},
  { /*32*/ 1.36,   7500,   375,  5, 10,  5, 20, 10},
  { /*33*/ 1.43,   7500,   400,  6, 11,  6, 20, 10},
  { /*34*/ 1.43,   7500,   425,  6, 11,  6, 20, 10},
  { /*35*/ 1.43,   7500,   550,  6, 11,  6, 20, 10},
  { /*36*/ 1.43,   8000,   650,  6, 11,  6, 20, 10},
  { /*37*/ 1.69,   9000,   750,  6, 11,  7, 20, 10},
  { /*38*/ 1.69,  10000,   850,  6, 11,  7, 20, 10},
  { /*39*/ 1.69,  11000,   950,  6, 11,  7, 20, 10},
  { /*40*/ 1.69,  14000,  1000,  6, 11,  7, 20, 10},
  { /*41*/ 1.69,  14000,  1150,  6, 11,  8, 10, 10},
  { /*42*/ 1.69,  15000,  1300,  6, 11,  8, 10, 10},
  { /*43*/ 1.69,  15000,  1600,  6, 11,  8, 10, 10},
  { /*44*/ 1.69,  15000,  1900,  7, 12,  9, 10, 10},
  { /*45*/ 1.69,  15000,  2200,  7, 12,  9, 10, 10},
  { /*46*/ 1.69,  20000,  2500,  7, 12,  9, 10, 10},
  { /*47*/ 1.69,  25000,  2500,  7, 12, 10, 10, 10},
  { /*48*/ 1.69,  27500,  2700,  7, 12, 10, 10, 10},
  { /*49*/ 1.69,  30000,  2800,  7, 12, 10, 10, 10},
  { /*50*/ 1.75,  35000,  2900,  7, 12, 10, 10, 10},
  { /*51*/ 1.75,  40000,  3000,  7, 12, 10, 10, 10},
  { /*52*/ 1.85,  50000,  3200,  7, 12, 11, 10, 10},
  { /*53*/ 1.85,  50000,  3500,  7, 12, 11, 10, 10},
  { /*54*/ 1.95,  80000,  3800,  7, 13, 11, 10, 10},
  { /*55*/ 1.95,  90000,  4100,  7, 13, 11, 10, 10},
  { /*56*/ 1.95, 100000,  4400,  7, 13, 11, 10, 10},
  { /*57*/ 1.95,  80000,  4700,  8, 14, 12, 10, 10},
  { /*58*/ 1.95,  80000,  5000,  8, 14, 12, 10, 10},
  { /*59*/ 2.15, 130000,  5500,  8, 14, 12, 10,  8},
  { /*60*/ 2.15, 140000,  5800,  8, 14, 12, 10,  8},
  { /*61*/ 2.15, 150000,  6100,  8, 14, 13, 10,  8},
  { /*62*/ 2.15, 160000,  6400,  8, 14, 13, 10,  8},
  { /*63*/ 2.35, 170000,  6700,  8, 14, 13, 10,  8},
  { /*64*/ 2.35, 180000,  7000,  8, 14, 13, 10,  8},
  { /*65*/ 2.35, 190000,  7300,  8, 14, 13, 10,  8},
  { /*66*/ 2.35, 200000,  7600,  8, 14, 13, 10,  8},
  { /*67*/ 2.4,  150000,  7900,  8, 14, 13, 10,  8},
  { /*68*/ 2.4,  150000,  8200,  8, 15, 13, 10,  8},
  { /*69*/ 2.4,  130000,  8600,  8, 15, 13,  8,  6},
  { /*70*/ 2.45, 130000,  8800,  8, 15, 13,  8,  6},
  { /*71*/ 2.45, 130000,  8800,  9, 16, 13,  8,  6},
  { /*72*/ 2.4,  260000,  9400,  9, 16, 13,  5,  5},
  { /*73*/ 2.4,  270000,  9700,  9, 16, 13,  5,  5},
  { /*74*/ 2.4,  280000,  9800,  9, 16, 13,  5,  5},
  { /*75*/ 2.6,  140000,  9000,  9, 17, 13,  5,  5},
  { /*76*/ 2.6,  160000,  9400,  9, 17, 13,  5,  5},
  { /*77*/ 2.6,  180000,  9600,  9, 17, 13,  5,  5},
  { /*78*/ 2.6,  200000,  9800,  9, 17, 13,  5,  5},
  { /*79*/ 2.65, 220000, 10000,  9, 18, 13,  5,  5},
  { /*80*/ 2.65, 250000, 10500,  9, 18, 13,  5,  5},
  /* entries below due to Thomas Denny */
  { /*81*/ 3.1, 1500000, 16000,  9, 18, 15,  4,  4},
  { /*82*/ 3.1, 1500000, 17000,  9, 18, 15,  4,  4},
  { /*83*/ 3.1, 1500000, 18500,  9, 19, 16,  4,  4},
  { /*84*/ 3.2, 1500000, 20000,  9, 19, 16,  4,  4},
  { /*85*/ 3.2, 1500000, 21500,  9, 19, 16,  4,  4},
  { /*86*/ 3.2, 1500000, 23000,  9, 19, 16,  4,  4},
  { /*87*/ 3.2, 1500000, 25000,  9, 20, 17,  4,  4},
  { /*88*/ 3.3, 1500000, 27000,  9, 20, 17,  4,  4},
  { /*89*/ 3.3, 1500000, 28000,  9, 20, 17,  4,  4},
  { /*90*/ 3.5, 2000000, 30500,  9, 20, 17,  2,  2},
  { /*91*/ 3.6, 2000000, 32000,  9, 21, 18,  2,  2},
  { /*92*/ 3.6, 2000000, 35000,  9, 21, 18,  2,  2},
  { /*93*/ 3.7, 2000000, 37000,  9, 21, 18,  2,  2},
  { /*94*/ 3.7, 2000000, 39500,  9, 22, 18,  2,  2},
  { /*95*/ 3.7, 2500000, 41500,  9, 22, 18,  2,  2},
  { /*96*/ 3.8, 2500000, 45000, 10, 23, 18,  2,  2},
  { /*97*/ 3.8, 2500000, 47500, 10, 23, 18,  2,  2},
  { /*98*/ 3.7, 3000000, 51000, 10, 24, 18,  2,  2},
  { /*99*/ 3.8, 3000000, 53000, 10, 24, 18,  2,  2},
  {/*100*/ 3.8, 3500000, 51000, 10, 25, 18,  2,  2},
  {/*101*/ 3.8, 3500000, 54000, 10, 25, 18,  2,  2},
  {/*102*/ 3.8, 3500000, 57000, 10, 26, 18,  2,  2},
  {/*103*/ 3.9, 4000000, 61000, 10, 26, 18,  2,  2},
  {/*104*/ 3.9, 4000000, 66000, 10, 27, 18,  2,  2},
  {/*105*/ 3.9, 4000000, 70000, 10, 27, 18,  2,  2},
  {/*106*/ 3.9, 4000000, 75000, 10, 28, 18,  2,  2},
  {/*107*/ 3.9, 4000000, 80000, 10, 30, 18,  2,  2},
};

/**
 ** Return the appropriate parameters for the initialization of MPQS
 **
 ** the parameter table for mpqs has the following format:
 **
 ** [d    -- decimal digits -- commented out]
 ** e    -- approximation accuracy
 ** M    -- size sieving interval
 ** s    -- size FB,
 ** fA   -- # prime factors in A
 ** pA   -- total # primes for determination of A,
 ** [maxB -- how many Bs to use before choosing a new A -- determined by fA]
 ** si   -- initial sieving index
 ** isoi -- initial sorting interval
 ** fsoi -- followup sorting interval increment
 **/

static void
mpqs_read_parameters(ulong d, double *e, ulong *M, ulong *s, ulong *os,
		     ulong *fA, ulong *pA, long *maxB, ulong *si,
		     ulong *isoi, ulong *fsoi)
{
  long i = d;
  if (i < 9) i = 9;
  if (i > 107) i = 107;
  i -= 9;

  *e = mpqs_parameters[i][0];
  *M = (ulong)mpqs_parameters[i][1];
  *s = (ulong)mpqs_parameters[i][2];
  if (*s >= 200) *os = *s + 70;
  else *os = (ulong)(*s * 1.35);
  *fA = (ulong)mpqs_parameters[i][3];
  *pA = (ulong)mpqs_parameters[i][4];
#if 0
  *maxB = (long) pow(2.0, mpqs_parameters[i][3] - 1.0);
#else
  *maxB = 1l << (*fA - 1);
#endif
  *si = (ulong)mpqs_parameters[i][5];
  *isoi = 10 * (ulong)mpqs_parameters[i][6]; /* percentages scaled by 10 */
  *fsoi = 10 * (ulong)mpqs_parameters[i][7];
}

/******************************/

/**
 ** increment *x (!=0) to a larger value which has the same number of 1s
 ** in its binary representation.  Cases which wrap around can be detected
 ** by the caller afterwards as long as we keep total_no_of_primes_for_A
 ** strictly less than BITS_IN_LONG.
 **
 ** Switch for the fast cases moved into here --GN
 **
 ** Changed switch to increment *x in all cases to the next larger number
 ** which (a) has the same count of 1 bits and (b) does not arise from the
 ** old value by moving a single 1 bit one position to the left  (which was
 ** undesirable for the sieve). --GN based on discussion with TP
 **/
static void
mpqs_increment(ulong *x)
{
  ulong r1_mask, r01_mask, slider=1;

  /* ultra-fast 32-way computed jump handles 22 out of 32 cases */
  switch (*x & 0x1f)
  {
  case 29:
    (*x)++; break;		/* this does shift a single bit, but we'll
				   postprocess this case */
  case 26:
    (*x) += 2; break;		/* again */
  case 1: case 3: case 6: case 9: case 11:
  case 17: case 19: case 22: case 25: case 27:
    (*x) += 3; return;
  case 20:
    (*x) += 4; break;		/* again */
  case 5: case 12: case 14: case 21:
    (*x) += 5; return;
  case 2: case 7: case 13: case 18: case 23:
    (*x) += 6; return;
  case 10:
    (*x) += 7; return;
  case 8:
    (*x) += 8; break;		/* and again */
  case 4: case 15:
    (*x) += 12; return;
  default:			/* 0, 16, 24, 28, 30, 31 */
    /* isolate rightmost 1 */
    r1_mask = ((*x ^ (*x - 1)) + 1) >> 1;
    /* isolate rightmost 1 which has a 0 to its left */
    r01_mask = ((*x ^ (*x + r1_mask)) + r1_mask) >> 2;
    /* simple cases.  Both of these shift a single bit one position to the
       left, and will need postprocessing */
    if (r1_mask == r01_mask) { *x += r1_mask; break; }
    if (r1_mask == 1) { *x += r01_mask; break; }
    /* general case -- idea:
       add r01_mask, kill off as many 1 bits as possible to its right
       while at the same time filling in 1 bits from the LSB. */
    if (r1_mask == 2) { *x += (r01_mask>>1) + 1; return; }
    while (r01_mask > r1_mask && slider < r1_mask)
    {
      r01_mask >>= 1; slider <<= 1;
    }
    *x += r01_mask + slider - 1;
    return;
  }
  /* post-process all cases which couldn't be finalized above.  If we get
     here, slider still has its original value. */
  r1_mask = ((*x ^ (*x - 1)) + 1) >> 1;
  r01_mask = ((*x ^ (*x + r1_mask)) + r1_mask) >> 2;
  if (r1_mask == r01_mask) { *x += r1_mask; return; }
  if (r1_mask == 1) { *x += r01_mask; return; }
  if (r1_mask == 2) { *x += (r01_mask>>1) + 1; return; }
  while (r01_mask > r1_mask && slider < r1_mask)
  {
    r01_mask >>= 1; slider <<= 1;
  }
  *x += r01_mask + slider - 1;
  return;
}

static long
mpqs_invsmod(long b, long p)
{
  long v1 = 0, v2 = 1, v3, r, oldp = p;

  while (b > 1)
  {
    v3 = v1 - (p / b) * v2; v1 = v2; v2 = v3;
    r = p % b; p = b; b = r;
  }

  if (v2 < 0) v2 += oldp;
  return v2;
}

/**
 ** compute coefficients of the sieving polynomial for self initializing
 ** variant. Coefficients A and B are returned and several tables are
 ** updated.  See Thomas Sosnowski's diploma thesis.
 **/

static void
mpqs_self_init(GEN A, GEN B, GEN N, GEN kN, long *FB, long *sqrt_mod_p_kN,
               long *start_1, long *start_2, ulong no_of_primes_in_A,
               ulong total_no_of_primes_for_A, ulong M, long **inv_A_H_i,
               long *Q_prime, long *Q_prime_glob, GEN* H_i, long index_i,
               long start_index_FB_for_A, long *inv_A2, GEN inv_A4,
               ulong *bin_index, GEN *f)
{
  pari_sp av;
  GEN p1, p2;
  ulong size_of_FB, nu_2;
  long i, j, p, M_mod_p, tmp, tmp1, tmp2;

  *f = NULL;
  if (index_i == 0)
  {
    /* compute first polynomial with new A */
    if (!*bin_index)
    {
      *bin_index = (1ul << no_of_primes_in_A) - 1;
    }
    else
      mpqs_increment(bin_index);
    if (*bin_index >= (1ul << total_no_of_primes_for_A)) /* wraparound */
    {
      if (DEBUGLEVEL >= 2)
	fprintferr("MPQS: bin_index wraparound\n");
      /* complain:  caller should increase some parameters... */
      return;
      /* caller should repeat the above test; if we simply increase the
	 total_no_of_primes_for_A, then bin_index now contains something
	 suitable for carrying on -- we'll probably end up not using
	 that particular index and skipping ahead to the next one, but
	 this isn't a problem.  OTOH total_no_of_primes_for_A should now
	 be so large that this should never happen except for ridiculous
	 input, like asking mpqs to factor 27, in which case it will act
	 as a safeguard against an infinite loop --GN */
    }

    /* determine primes used for A in this iteration */
    for (i = 0, j = 0; (ulong)j < total_no_of_primes_for_A; j++)
    {
      if (*bin_index & (1 << j))
      {
	Q_prime[i] = Q_prime_glob[j];
	i++;
      }
    }

    /*
     * compute coefficient A using
     * A = prod (Q_prime[i], 0 < i < no_of_primes_in_A)
     */

    av = avma;
    p1 = stoi(Q_prime[0]);
    for (i = 1; (ulong)i < no_of_primes_in_A; i++)
      p1 = mulis(p1, Q_prime[i]);
    affii(p1, A);
    avma = av;

    /*
     * let bound := no_of_primes_in_A. Compute H_i, 0 <= i < bound.
     */

    for (i = 0; (ulong)i < no_of_primes_in_A; i++)
    {
      av = avma;
      p = Q_prime[i];
      p1 = divis(A, p);
      tmp = smodis(p1, p);
      p1 = mulis(p1, mpqs_invsmod(tmp, p));
      tmp = itos(mpsqrtmod(modis(kN, p), stoi(p)));
      p1 = mulis(p1, tmp);
      affii(modii(p1, A), H_i[i]);
      avma = av;
    }

    /*
     * Each B is of the form sum(v_i * H_i, 0 <= i < bound)
     * where each v_j is +1 or -1. This has to be done only once
     * (for index_i==0) for the coefficient A; if index_i > 0 then
     * there is a linear recursion for B
     */

    /* compute actual B coefficient, by taking all v_i == 1 */
    av = avma;
    p1 = H_i[0];
    for (i = 1; (ulong)i < no_of_primes_in_A; i++)
      p1 = addii(p1, H_i[i]);
    affii(p1, B);
    avma = av;

    /* ensure B = 1 mod 4 */
    if (mod2(B) == 0)
    {
      /* B += (A % 4) * A; */
      av = avma;
      p1 = addii(B, mulsi(mod4(A), A));
      affii(p1, B);
      avma = av;
    }

    /* compute inv_A2[i] = 1/(2*A) mod p_i */
    av = avma;
    p1 = shifti(A, 1);
    size_of_FB = FB[0] + 1;
    for (i = 2; (ulong)i <= size_of_FB; i++)
      inv_A2[i] = mpqs_invsmod(smodis(p1, FB[i]), FB[i]);
    avma = av;

    /* compute inv_A_H_i[i][j] = 1/A * H_i[i] mod p_j */
    for (i = 0; (ulong)i < no_of_primes_in_A; i++)
    {
      for (j = 2; (ulong)j <= size_of_FB; j++)
      {
	av = avma;
	p1 = mulis(H_i[i], inv_A2[j] << 1);
	inv_A_H_i[i][j] = smodis(p1, FB[j]);
	avma = av;
      }
    }

    /* compute the roots z1, z2, of the polynomial Q(x) mod p_j and
     * initialize start_1[i] with the first value p_i | Q(z1 + i p_j)
     * initialize start_2[i] with the first value p_i | Q(z2 + i p_j)
     */
    for (j = 2; (ulong)j <= size_of_FB; j++)
    {
      p = FB[j];
      M_mod_p = M % p;

      tmp = p - smodis(B, p); /* tmp = -B mod p */

      tmp1 = (tmp - sqrt_mod_p_kN[j]) % p;
      if (tmp1 < 0) tmp1 += p;
      tmp1 = mulssmod(tmp1, inv_A2[j], p);
      tmp1 = (tmp1 + M_mod_p) % p;

      tmp2 = (tmp + sqrt_mod_p_kN[j]) % p;
      if (tmp2 < 0) tmp2 += p;
      tmp2 = mulssmod(tmp2, inv_A2[j], p);
      tmp2  = (tmp2 + M_mod_p) % p;

      start_1[j] = (tmp1 < 0) ? tmp1 + p : tmp1;
      start_2[j] = (tmp2 < 0) ? tmp2 + p : tmp2;
    }

    /* determine 1/(4A) mod kN */
    av = avma;
    if (!invmod(shifti(A,2), kN, &p1)) /* --GN */
    {
      /* inv_A4 is a factor > 1 of kN.  This cannot actually happen.
         Catch it anyway, it doesn't cost more than two comparisons
	 against 0 / NULL */
      p1 = mppgcd(p1, N);
      *f = gerepileupto(av, p1);
      return;			/* we certainly can't use the current poly */
    }
    affii(p1, inv_A4);
    avma = av;
  }
  else
  {
    /* no "real" computation -- use recursive formula
     * first: update of B, compute B[index_i], index_i > 0
     */

    /* compute nu_2 = nu_2(index_i) */
    nu_2 = 0;
    j = index_i;
    while ((j & 1) == 0)
    {
      nu_2++;
      j >>= 1;
    }

    av = avma;
    p1 = shifti(H_i[nu_2], 1);

    if ((((j+1)/2) & 1) == 1)
    {
      i = -1;
      p1 = subii(B, p1);
    }
    else
    {
      i = 1;
      p1 = addii(B, p1);
    }
    affii(p1, B);
    avma = av;

    /* determine new starting positions for sieving */
    size_of_FB = FB[0] + 1;

    if (i == -1)
    {
      for (j = 2; (ulong)j <= size_of_FB; j++)
      {
	p = FB[j];
	start_1[j] += inv_A_H_i[nu_2][j];
	if (start_1[j] >= p)
	  start_1[j] -= p;
	start_2[j] += inv_A_H_i[nu_2][j];
	if (start_2[j] >= p)
	  start_2[j] -= p;
      }
    }
    else
    {
      for (j = 2; (ulong)j <= size_of_FB; j++)
      {
	p = FB[j];
	start_1[j] -= inv_A_H_i[nu_2][j];
	if (start_1[j] < 0)
	  start_1[j] += p;
	start_2[j] -= inv_A_H_i[nu_2][j];
	if (start_2[j] < 0)
	  start_2[j] += p;
      }
    }
  }

  /* p=2 is a special case */
  if (FB[2] == 2)
  {
    start_1[2] = 0; start_2[2] = 1;
  }


  /* now compute zeros of polynomials that have only one zero mod p
     because p divides the coefficient A */

  /* compute coefficient -C */
  av = avma;
  p1 = subii(kN, sqri(B));
  p2 = divii(p1, shifti(A, 2));

  for (j = 1; (ulong)j <= total_no_of_primes_for_A; j++)
    if (*bin_index & (1 << (j-1)))
    {
      p = FB[start_index_FB_for_A + j];
      tmp = mpqs_invsmod(smodis(B, p), p);
      tmp2 = smodis (p2, p);
      tmp = mulssmod(tmp2, tmp, p);
      start_1[start_index_FB_for_A + j] =
	start_2[start_index_FB_for_A + j] = (tmp + M) % p;
    }
  avma = av;

#ifdef MPQS_DEBUG
  {
    /*
     * check correctness of the roots z1, z2 mod p_i by evaluting
     * A * z1^2 + B * z1 + C mod p_i and checking against 0 mod p_i
     * C is written as (B*B-kN)/(4*A)
     */
    size_of_FB = FB[0] + 1;
    for (j = 3; j <= size_of_FB; j++)
    {
      av = avma;
      p = FB[j];
      M_mod_p = M % p;

      p1 = mulis(A, start_1[j] - M_mod_p);
      p1 = addii(p1, B);
      p1 = mulis(p1, start_1[j] - M_mod_p);
      p2 = divii(subii(sqri(B), kN), shifti(A, 2));
      p1 = addii(p1, p2);
      if (smodis(p1, p) != 0)
      {
	fprintferr("MPQS: (1) j = %ld p = %ld\n", j, p);
	fprintferr("MPQS: (1) index_i = %ld\n", index_i);
	fprintferr("MPQS: A = %Z\n", A);
	fprintferr("MPQS: B = %Z\n", B);
	fprintferr("MPQS: C = %Z\n", p1);
	fprintferr("MPQS: z1 = %ld\n", start_1[j] - M_mod_p);
	err(talker, "MPQS: self_init: found wrong polynomial in (1)");
      }

      p1 = mulis(A, start_2[j]-M_mod_p);
      p1 = addii(p1, B);
      p1 = mulis(p1, start_2[j]-M_mod_p);
      p2 = divii(subii(sqri(B), kN), shifti(A, 2));
      p1 = addii(p1, p2);
      if (smodis(p1, p) != 0)
      {
	fprintferr("MPQS: (2) j = %ld p = %ld\n", j, p);
	fprintferr("MPQS: (2) index_i = %ld\n", index_i);
	fprintferr("MPQS: A = %Z\n", A);
	fprintferr("MPQS: B = %Z\n", B);
	fprintferr("MPQS: C = %Z\n", p1);
	fprintferr("MPQS: z2 = %ld\n", start_2[j] - M_mod_p);
	err(talker, "MPQS: self_init: found wrong polynomial in (2)");
      }
      avma = av;
    }
    if (DEBUGLEVEL >= 4)
      fprintferr("MPQS: checking of roots of Q(x) was successful\n");
  }
#endif

}

/******************************/

/**
 **  Main sieving routine:
 **
 **  FB     is a pointer to an array which holds the factor base
 **  log_FB is a pointer to an array which holds the approximations for
 **         the logarithms of the factor base elements
 **  start_1, start_2
 **         are arrays for starting points for different FB elements
 **  sieve_array
 **         points to a sieve array
 **  sieve_array_end
 **         points to the end of the sieve array
 **  M      is the size of the sieving interval
 **  starting_sieving_index
 **         marks the first FB element which is used for sieving
 **
 **/

#ifdef INLINE
 INLINE
#endif
void
mpqs_sieve_p(unsigned char *begin, unsigned char *end,
             long p_times_4, long p, unsigned char log_p)
{
  register unsigned char *e = end - p_times_4;
  while (e - begin >= 0)	/* signed comparison --GN2000Jun02 */
  {
    (*begin) += log_p, begin += p;
    (*begin) += log_p, begin += p;
    (*begin) += log_p, begin += p;
    (*begin) += log_p, begin += p;
  }
  while (end - begin >= 0)	/* again --GN2000Jun02 */
    (*begin) += log_p, begin += p;
}

static void
mpqs_sieve(long *FB, unsigned char *log_FB, long *start_1, long *start_2,
	   unsigned char *sieve_array, unsigned char *sieve_array_end,
	   ulong M, ulong starting_sieving_index)
{
  register long p_times_4, p, *ptr_FB, start1, start2, l;
  register unsigned char log_p;

  memset (sieve_array, 0, (M << 1) * sizeof (unsigned char));

  l = starting_sieving_index;
  ptr_FB = &FB[l];

  while ((p = *ptr_FB++) != 0)
  {
    p_times_4 = p * 4;
    log_p = log_FB[l];
    start1 = start_1[l];
    start2 = start_2[l];

    /* sieve with FB[l] from start_1[l] */
    /* if start1 != start2 sieve with FB[l] from start_2[l] */
    if (start1 == start2)
      mpqs_sieve_p(sieve_array + start1, sieve_array_end,
		   p_times_4, p, log_p);
    else
    {
      mpqs_sieve_p(sieve_array + start1, sieve_array_end,
		   p_times_4, p, log_p);
      mpqs_sieve_p(sieve_array + start2, sieve_array_end,
		   p_times_4, p, log_p);
    }

    l++;
  }
}

/******************************/

static long
mpqs_eval_sieve(unsigned char *sieve_array, ulong M, long *candidates)
{
  ulong M_2 = M << 1;
  int i = 0, count, q, r;
  unsigned char *ptr = sieve_array;

  r = M_2 % 4;
  q = M_2  - r;
  count = 0;
  for (i = 0; i < q; i += 4, ptr += 4)
  {
    if (*(ptr+0) > 128) { candidates[count] = i+0; count++; }
    if (*(ptr+1) > 128) { candidates[count] = i+1; count++; }
    if (*(ptr+2) > 128) { candidates[count] = i+2; count++; }
    if (*(ptr+3) > 128) { candidates[count] = i+3; count++; }
  }
  switch (r)
  {
    case 3:
      if (*(ptr+0) > 128) { candidates[count] = i+0; count++; }
      if (*(ptr+1) > 128) { candidates[count] = i+1; count++; }
      if (*(ptr+2) > 128) { candidates[count] = i+2; count++; }
      break;
    case 2:
      if (*(ptr+0) > 128) { candidates[count] = i+0; count++; }
      if (*(ptr+1) > 128) { candidates[count] = i+1; count++; }
      break;
    case 1:
      if (*(ptr+0) > 128) { candidates[count] = i+0; count++; }
      break;
    default:
      break;
  }
  candidates[count] = 0;
  return count;
}

/**
 **  Main relation routine:
 **
 **  FB     is a pointer to an array which holds the factor base
 **  log_FB is a pointer to an array which holds the approximations for
 **         the logarithms of the factor base elements
 **  start_1, start_2
 **         are arrays for starting points for different FB elements
 **  M      is the size of the sieving interval
 **
 **/

static void
mpqs_add_factor(char **last, ulong ei, ulong pi) {
  sprintf(*last, " %lu %lu", ei, pi);
  *last += strlen(*last);
}

/* concatenate " 0" */
static void
mpqs_add_0(char **last) {
  char *s = *last;
  *s++ = ' ';
  *s++ = '0';
  *s++ = 0; *last = s;
}

/**
 ** divide and return the remainder.  Leaves both the quotient and
 ** the remainder on the stack as GENs;  the caller should clean up.
 **/

#ifdef INLINE
 INLINE
#else
 static
#endif
ulong
mpqs_div_rem(GEN x, long y, GEN *q)
{
  GEN r;
  *q = dvmdis(x, y, &r);
  if (signe(r)) return (ulong)(r[2]);
  return 0;
}

#ifdef DEBUG
static GEN
mpqs_factorback(long *FB, char *relations, GEN kN)
{
  char *s, *t = pari_strdup(relations);
  GEN pi_ei, prod = gun;
  long pi, ei;

  s = strtok(t, " \n");
  while (s != NULL)
  {
    ei = atol(s);
    if (ei == 0) break;
    s = strtok(NULL, " \n");
    pi = atol(s);
    pi_ei = powmodulo(stoi(FB[pi]), stoi(ei), kN);
    prod = modii(mulii(prod, pi_ei), kN);
    s = strtok(NULL, " \n");
  }
  free(t); return prod;
}
#endif

static long
mpqs_eval_candidates(GEN A, GEN inv_A4, GEN B, GEN kN, long k,
		     double sqrt_kN,
		     long *FB, long *start_1, long *start_2,
		     ulong M, long bin_index, long *candidates,
		     long number_of_candidates, long lp_bound,
		     long start_index_FB_for_A,
		     FILE *FREL, FILE *LPREL)
     /* NB FREL, LPREL are actually FNEW, LPNEW when we get called */
{
  double a, b, inv_2_a;
  pari_sp av;
  long z1, z2, number_of_relations = 0;
  char *relations;
  ulong i, pi, size_of_FB;
#ifdef MPQS_DEBUG_VERBOSE
  static char complaint[256], complaint0[256];
  complaint[0] = '\0';
#endif

  /* roots of Q(X), used to find sign(Q(x)) after reducing mod kN */
  a = gtodouble(A); inv_2_a = 1 / (2.0 * a);
  b = gtodouble(B);
  z1 = (long) ((-b - sqrt_kN) * inv_2_a);
  z2 = (long) ((-b + sqrt_kN) * inv_2_a);

  /* Worst case:  
   * + leading " 1 1"
   * + trailing " 0\n" with final NUL character
   * + in between up to size_of_FB pairs each consisting of an exponent, a
   *   subscript into FB, and two spaces.
   * Subscripts into FB fit into 5 digits, and exponents fit into 3 digits
   * with room to spare -- anything needing 3 or more digits for the
   * subscript must come with an exponent of at most 2 digits. Moreover the
   * product of the first 58 primes is larger than 10^110, so there cannot be
   * more than 60 pairs in all, even if size_of_FB > 10^4. --GN */
  size_of_FB = FB[0];		/* one less than usually: don't count FB[1] */
  if (size_of_FB > 60) size_of_FB = 60;
  relations = (char *) gpmalloc((8 + size_of_FB * 9) * sizeof(char));

  av = avma;
  for (i = 0; i < (ulong)number_of_candidates; i++, avma = av)
  {
    GEN Qx, A_2x_plus_B, Y;
    long powers_of_2, p, bi;
    long x = candidates[i];
    long x_minus_M = x - M;
    char *relations_end = relations;

    *relations_end = 0;
#ifdef MPQS_DEBUG_VERYVERBOSE
    fprintferr("%c", (char)('0' + i%10));
#endif

    /* A_2x_plus_B = (A*(2x)+B), Qx = (A*(2x)+B)^2/(4*A) = Q(x) */
    A_2x_plus_B = modii(addii(mulis(A, x_minus_M << 1), B), kN);
    Y = subii(kN, A_2x_plus_B);
    if (absi_cmp(A_2x_plus_B, Y) < 0) Y = A_2x_plus_B;
    /* absolute value of smallest absolute residue of A_2x_plus_B mod kN */

    Qx = modii(sqri(Y), kN);

    /* Most of the time, gcd(Qx, kN) = 1 or k.  However, it may happen that
     * Qx is a multiple of N, esp. when N is small, leading to havoc below --
     * so we have to be a bit careful.  Of course we cannot afford to compute
     * the gcd each time through this loop unless we are debugging... --GN */
#ifdef MPQS_DEBUG
    {
      long ks;
      pari_sp av1 = avma;
      GEN g = mppgcd(Qx, kN);
/*    if ((ks = kronecker(divii(Qx, g), divii(kN, g))) != 1) */
      if (is_pm1(g))
      {
	if ((ks = kronecker(Qx, kN)) != 1)
	{
	  fprintferr("\nMPQS: 4*A*Q(x) = %Z\n", Qx);
	  fprintferr("\tKronecker symbol %ld\n", ks);
	  err(talker, "MPQS: 4*A*Q(x) is not a square (mod kN)");
	}
      }
#  ifdef MPQS_DEBUG_VERBOSE
      else if (cmpis(g,k) /* != 0 */ )
      {
	char *gs = GENtostr(g);
	sprintf(complaint, "\nMPQS: gcd(4*A*Q(x), kN) = %s\n", gs);
	free(gs);
	if (strcmp(complaint, complaint0))
	{
	  fprintferr(complaint);
	  strcpy(complaint0, complaint);
	}
      }
#  endif
      avma = av1;
    }
#endif

    Qx = modii(mulii(Qx, inv_A4), kN);

    /* check the sign of Qx */
    if (z1 < x_minus_M && x_minus_M < z2)
    {
       Qx = subii(kN, Qx);
       mpqs_add_factor(&relations_end, 1, 1); /* i = 1, ei = 1, pi */
    }
    if (!signe(Qx))
    {
#ifdef MPQS_DEBUG_VERBOSE
      fprintferr("<+>");
#endif
      continue;
    }

    /* divide by powers of 2;  we're really dealing with 4*A*Q(x), so we
     * remember an extra factor 2^2 */
    powers_of_2 = vali(Qx);
    Qx = shifti(Qx, -powers_of_2);
    mpqs_add_factor(&relations_end, powers_of_2 + 2, 2);

    /* we handled the case p = 2 already */
    bi = bin_index;
#ifdef MPQS_DEBUG_VERBOSE
    fprintferr("a");
#endif
    /* FB[3 .. start_index_FB_for_A] do not divide A.
     * p = FB[start_index_FB_for_A+j+1] divides A (to the first power)
     * iff the 2^j bit in bin_index is set */
    for (pi = 3; (p = FB[pi]) != 0; pi++)
    {
      long tmp_p = x % p;
      ulong ei = 0;
      GEN Qx_div_p;

      if (bi && pi > (ulong)start_index_FB_for_A)
      {
	ei = bi & 1;	/* either 0 or 1 */
	bi >>= 1;
      }

      if (tmp_p == start_1[pi] || tmp_p == start_2[pi])
      { /* p divides Q(x) and possibly A */
        long remd_p = mpqs_div_rem(Qx, p, &Qx_div_p);
	if (remd_p) break; /* useless candidate: abort */

        do
        {
	  ei++; Qx = Qx_div_p;
	  remd_p = mpqs_div_rem(Qx, p, &Qx_div_p);
        } while (remd_p == 0);
      }
      if (ei)			/* p might divide A but not Q(x) */
        mpqs_add_factor(&relations_end, ei, pi);
    }
    if (p)
    {
#ifdef MPQS_DEBUG_VERBOSE
      fprintferr("\b<");
#endif
      continue; /* loop aborted: useless candidate */
    }

#ifdef MPQS_DEBUG_VERBOSE
    fprintferr("\bb");
#endif
    if (is_pm1(Qx))
    {
      char *Qxstring = GENtostr(Y);
      mpqs_add_0(&relations_end);
      fprintf(FREL, "%s :%s\n", Qxstring, relations);
      free(Qxstring);
      number_of_relations++;

#ifdef MPQS_DEBUG
      {
        pari_sp av1 = avma;
	GEN rhs = mpqs_factorback(FB, relations, kN);
	GEN Qx_2 = modii(sqri(Y), kN);
	if (!egalii(Qx_2, rhs))
	{
#ifdef MPQS_DEBUG_VERBOSE
	  fprintferr("\b(!)\n");
#endif
	  fprintferr("MPQS: %Z @ %Z :%s\n", Y, Qx, relations);
	  fprintferr("\tQx_2 = %Z\n", Qx_2);
	  fprintferr("\t rhs = %Z\n", rhs);
	  err(talker, "MPQS: wrong full relation found!!");
	}
#ifdef MPQS_DEBUG_VERBOSE
	else
	  fprintferr("\b(:)");
#endif
	avma = av1;
      }
#endif
    }
    else if (cmpis(Qx, lp_bound) > 0)
    { /* TODO: check for double large prime */
#ifdef MPQS_DEBUG_VERBOSE
      fprintferr("\b.");
#endif
    }
    else if (k==1 || cgcd(k, itos(Qx)) == 1)
    { /* if (mpqs_isprime(itos(Qx))) */
      char *Qxstring = GENtostr(Y);
      char *L1string = GENtostr(Qx);
      mpqs_add_0(&relations_end);
      fprintf(LPREL, "%s @ %s :%s\n", L1string, Qxstring, relations);
      free(Qxstring);
      free(L1string);

#ifdef MPQS_DEBUG
      {
        pari_sp av1 = avma;
        GEN rhs = mpqs_factorback(FB, relations, kN);
	GEN Qx_2 = modii(sqri(Y), kN);

        rhs = modii(mulii(rhs, Qx), kN);
	if (!egalii(Qx_2, rhs))
	{
#ifdef MPQS_DEBUG_VERBOSE
	  fprintferr("\b(!)\n");
#endif
	  fprintferr("MPQS: %Z @ %Z :%s\n", Y, Qx, relations);
	  fprintferr("\tQx_2 = %Z\n", Qx_2);
	  fprintferr("\t rhs = %Z\n", rhs);
	  err(talker, "MPQS: wrong large prime relation found!!");
	}
#ifdef MPQS_DEBUG_VERBOSE
	else
	  fprintferr("\b(;)");
#endif
	avma = av1;
      }
#endif
    }
#ifdef MPQS_DEBUG_VERBOSE
    else
      fprintferr("\b<k>");
#endif
  } /* for */

#ifdef MPQS_DEBUG_VERBOSE
  fprintferr("\n");
#endif
  free(relations); return number_of_relations;
}

/******************************/

/**
 ** combines the large prime relations in COMB to full
 ** relations in FNEW.  FNEW is assumed to be open for
 ** writing / appending.
 **/

typedef struct
{
  long q;
  char Y  [MPQS_STRING_LENGTH];
  char ep [MPQS_STRING_LENGTH];
} mpqs_lp_entry;

static void
mpqs_combine_exponents(long *ei, long ei_size, char *r1, char *r2)
{
  char ej [MPQS_STRING_LENGTH], ek [MPQS_STRING_LENGTH];
  char *s;
  long e, p;

  memset(ei, 0, ei_size * sizeof(long));
  strcpy(ej, r1);
  strcpy(ek, r2);

  s = strtok(ej, " \n");
  while (s != NULL)
  {
    e = atol(s);
    if (e == 0)
      break;
    s = strtok(NULL, " \n");
    p = atol(s);
    ei[p] += e;
    s = strtok(NULL, " \n");
  }

  s = strtok(ek, " \n");
  while (s != NULL)
  {
    e = atol(s);
    if (e == 0)
      break;
    s = strtok(NULL, " \n");
    p = atol(s);
    ei[p] += e;
    s = strtok(NULL, " \n");
  }

}

static long
mpqs_combine_large_primes(FILE *COMB, FILE *FNEW, long size_of_FB,
			  GEN N, GEN kN, GEN *f
#ifdef MPQS_DEBUG
  , long *FB
#endif
)
{
  char buf [MPQS_STRING_LENGTH], *s1, *s2;
  char new_relation [MPQS_STRING_LENGTH];
  mpqs_lp_entry e[2];		/* we'll use the two alternatingly */
  long *ei, ei_size = size_of_FB + 2;
  long old_q;
  GEN inv_q, Y1, Y2, new_Y, new_Y1;
  long i, l, c = 0;
  pari_sp av = avma, av2;

  *f = NULL;
  if (fgets(buf, MPQS_STRING_LENGTH, COMB) == NULL)
    return 0;			/* nothing there -- should not happen */

  /* put first lp relation in row 0 of e */
  s1 = buf; s2 = strchr(s1, ' '); *s2 = '\0';
  e[0].q = atol(s1);
  s1 = s2 + 3; s2 = strchr(s1, ' '); *s2 = '\0';
  strcpy(e[0].Y, s1);
  s1 = s2 + 3;  s2 = strchr(s1, '\n'); *s2 = '\0';
  strcpy(e[0].ep, s1);

  i = 1;			/* second relation will go into row 1 */
  old_q = e[0].q;

  while (!invmod(stoi(old_q), kN, &inv_q)) /* can happen --GN */
  {
    inv_q = mppgcd(inv_q, N);
    if (is_pm1(inv_q) || egalii(inv_q, N)) /* pity */
    {
#ifdef MPQS_DEBUG
      fprintferr("MPQS: skipping relation with non-invertible q\n");
#endif
      avma = av;
      if (fgets(buf, MPQS_STRING_LENGTH, COMB) == NULL)
	return 0;
      s1 = buf; s2 = strchr(s1, ' '); *s2 = '\0';
      e[0].q = atol(s1);
      s1 = s2 + 3; s2 = strchr(s1, ' '); *s2 = '\0';
      strcpy(e[0].Y, s1);
      s1 = s2 + 3;  s2 = strchr(s1, '\n'); *s2 = '\0';
      strcpy(e[0].ep, s1);
      old_q = e[0].q;
      continue;
    }
    *f = gerepileupto(av, inv_q);
    return c;
  }
  Y1 = lisexpr(e[0].Y);
  av2 = avma;			/* preserve inv_q and Y1 */

  ei = (long *) gpmalloc(ei_size * sizeof(long));

  while (fgets(buf, MPQS_STRING_LENGTH, COMB) != NULL)
  {
    s1 = buf; s2 = strchr(s1, ' '); *s2 = '\0';
    e[i].q = atol(s1);
    s1 = s2 + 3; s2 = strchr(s1, ' '); *s2 = '\0';
    strcpy(e[i].Y, s1);
    s1 = s2 + 3;  s2 = strchr(s1, '\n'); *s2 = '\0';
    strcpy(e[i].ep, s1);

    if (e[i].q != old_q)
    {
      /* switch to combining a new bunch, swapping the rows */
      old_q = e[i].q;
      avma = av;		/* discard old inv_q and Y1 */
      if (!invmod(stoi(old_q), kN, &inv_q)) /* can happen --GN */
      {
	inv_q = mppgcd(inv_q, N);
	if (is_pm1(inv_q) || egalii(inv_q, N)) /* pity */
	{
#ifdef MPQS_DEBUG
	  fprintferr("MPQS: skipping relation with non-invertible q\n");
#endif
	  avma = av;
	  old_q = -1;		/* sentinel */
	  av2 = avma;
	  continue;		/* discard this combination */
	}
	*f = gerepileupto(av, inv_q);
	free (ei);
	return c;
      }
      Y1 = lisexpr(e[i].Y);
      i = 1 - i;		/* subsequent relations go to other row */
      av2 = avma;		/* preserve inv_q and Y1 */
      continue;
    }
    /* count and combine the two we've got, and continue in the same row */
    c++;

    mpqs_combine_exponents(ei, ei_size, e[1-i].ep, e[i].ep);
    if (DEBUGLEVEL >= 6)
    {
      fprintferr("MPQS: combining\n");
      fprintferr("    {%ld @ %s : %s}\n", old_q, e[1-i].Y, e[1-i].ep);
      fprintferr("  * {%ld @ %s : %s}\n", e[i].q, e[i].Y, e[i].ep);
    }
    Y2 = lisexpr(e[i].Y);
    new_Y = modii(mulii(mulii(Y1, Y2), inv_q), kN);
    new_Y1 = subii(kN, new_Y);
    if (absi_cmp(new_Y1, new_Y) < 0) new_Y = new_Y1;
    s1 = GENtostr(new_Y);
    strcpy(new_relation, s1);
    free(s1);
    strcat(new_relation, " :");
    if (ei[1] % 2)
      strcat(new_relation, " 1 1");
    for (l = 2; l < ei_size; l++)
    {
      if (ei[l])
      {
	sprintf(buf, " %ld %ld", ei[l], l);
	strcat(new_relation, buf);
      }
    }
    strcat(new_relation, " 0");
    if (DEBUGLEVEL >= 6) fprintferr(" == {%s}\n", new_relation);
    strcat(new_relation, "\n");

#ifdef MPQS_DEBUG
    {
      char ejk [MPQS_STRING_LENGTH];
      GEN Qx_2, prod_pi_ei, pi_ei;
      char *s;
      long pi, exi;
      pari_sp av1 = avma;
      Qx_2 = modii(sqri(new_Y), kN);

      strcpy(ejk, new_relation);
      s = strchr(ejk, ':') + 2;
      s = strtok(s, " \n");

      prod_pi_ei = gun;
      while (s != NULL)
      {
	exi = atol(s);
	if (exi == 0) break;
	s = strtok(NULL, " \n");
	pi = atol(s);
	pi_ei = powmodulo(stoi(FB[pi]), stoi(exi), kN);
	prod_pi_ei = modii(mulii(prod_pi_ei, pi_ei), kN);
	s = strtok(NULL, " \n");
      }
      avma = av1;

      if (!egalii(Qx_2, prod_pi_ei))
      {
	free(ei);
	err(talker,
	    "MPQS: combined large prime relation is false");
      }
    }
#endif

    if (fputs(new_relation, FNEW) < 0)
    {
      free(ei);
      bummer(FNEW_str);
    }
    avma = av2;
  } /* while */

  free(ei);

  if (DEBUGLEVEL >= 4)
    fprintferr("MPQS: combined %ld full relation%s\n",
	       c, (c!=1 ? "s" : ""));
  return c;
}

/******************************/

#ifdef LONG_IS_64BIT

#define MPQS_GAUSS_BITS 64
static unsigned long mpqs_mask_bit[]  =
{
  0x8000000000000000UL, 0x4000000000000000UL,
  0x2000000000000000UL, 0x1000000000000000UL,
  0x0800000000000000UL, 0x0400000000000000UL,
  0x0200000000000000UL, 0x0100000000000000UL,
  0x0080000000000000UL, 0x0040000000000000UL,
  0x0020000000000000UL, 0x0010000000000000UL,
  0x0008000000000000UL, 0x0004000000000000UL,
  0x0002000000000000UL, 0x0001000000000000UL,
  0x0000800000000000UL, 0x0000400000000000UL,
  0x0000200000000000UL, 0x0000100000000000UL,
  0x0000080000000000UL, 0x0000040000000000UL,
  0x0000020000000000UL, 0x0000010000000000UL,
  0x0000008000000000UL, 0x0000004000000000UL,
  0x0000002000000000UL, 0x0000001000000000UL,
  0x0000000800000000UL, 0x0000000400000000UL,
  0x0000000200000000UL, 0x0000000100000000UL,
  0x0000000080000000UL, 0x0000000040000000UL,
  0x0000000020000000UL, 0x0000000010000000UL,
  0x0000000008000000UL, 0x0000000004000000UL,
  0x0000000002000000UL, 0x0000000001000000UL,
  0x0000000000800000UL, 0x0000000000400000UL,
  0x0000000000200000UL, 0x0000000000100000UL,
  0x0000000000080000UL, 0x0000000000040000UL,
  0x0000000000020000UL, 0x0000000000010000UL,
  0x0000000000008000UL, 0x0000000000004000UL,
  0x0000000000002000UL, 0x0000000000001000UL,
  0x0000000000000800UL, 0x0000000000000400UL,
  0x0000000000000200UL, 0x0000000000000100UL,
  0x0000000000000080UL, 0x0000000000000040UL,
  0x0000000000000020UL, 0x0000000000000010UL,
  0x0000000000000008UL, 0x0000000000000004UL,
  0x0000000000000002UL, 0x0000000000000001UL
};

#else

#define MPQS_GAUSS_BITS 32
static unsigned long mpqs_mask_bit[]  =
{
  0x80000000UL, 0x40000000UL, 0x20000000UL, 0x10000000UL,
  0x08000000UL, 0x04000000UL, 0x02000000UL, 0x01000000UL,
  0x00800000UL, 0x00400000UL, 0x00200000UL, 0x00100000UL,
  0x00080000UL, 0x00040000UL, 0x00020000UL, 0x00010000UL,
  0x00008000UL, 0x00004000UL, 0x00002000UL, 0x00001000UL,
  0x00000800UL, 0x00000400UL, 0x00000200UL, 0x00000100UL,
  0x00000080UL, 0x00000040UL, 0x00000020UL, 0x00000010UL,
  0x00000008UL, 0x00000004UL, 0x00000002UL, 0x00000001UL
};

#endif

static mpqs_gauss_matrix
mpqs_gauss_create_matrix(long rows, long cols)
{
  mpqs_gauss_matrix m;
  long i, j, words = cols / MPQS_GAUSS_BITS;
  if (cols % MPQS_GAUSS_BITS)
    words++;
  m = (mpqs_gauss_row *) gpmalloc(rows * sizeof(mpqs_gauss_row));
  for (i = 0; i < rows; i++)
  {
    m[i] = (ulong *) gpmalloc(words * sizeof(ulong));
    for (j = 0; j < words; j++)
      m[i][j] = 0UL;
  }
  return m;
}

static void
mpqs_gauss_destroy_matrix(mpqs_gauss_matrix m, long rows, long cols)
{
  long i;
  (void) cols;
  for (i = 0; i < rows; i++)
    free(m[i]);
  free(m);
}

static ulong
mpqs_gauss_get_bit(mpqs_gauss_matrix m, long i, long j)
{
  return m[i][j / MPQS_GAUSS_BITS] & mpqs_mask_bit[j % MPQS_GAUSS_BITS];
}

static void
mpqs_gauss_set_bit(mpqs_gauss_matrix m, long i, long j)
{
  m[i][j / MPQS_GAUSS_BITS] |= mpqs_mask_bit[j % MPQS_GAUSS_BITS];
}

static void
mpqs_gauss_clear_bit(mpqs_gauss_matrix m, long i, long j)
{
  m[i][j / MPQS_GAUSS_BITS] &= ~mpqs_mask_bit[j % MPQS_GAUSS_BITS];
}

/* output an mpqs_gauss_matrix in PARI format */
/* TODO -- this should do a little intelligent wrapping... GN */
static void
mpqs_gauss_print_matrix(mpqs_gauss_matrix m, long rows, long cols)
{
  long i, j;
  fprintferr("\n[");
  for (i = 0; i < rows; i++)
  {
    for (j = 0; j < cols - 1; j++)
    {
      if (mpqs_gauss_get_bit(m, i, j))
        fprintferr("1, ");
      else
        fprintferr("0, ");
    }

    if (mpqs_gauss_get_bit(m, i, j))
      fprintferr("1");
    else
      fprintferr("0");
    if (i != rows - 1)
      fprintferr("; ");
  }
  fprintferr("]\n");
}

/* x ^= y : row addition over F_2 */
static void
mpqs_gauss_add_rows(mpqs_gauss_row y, mpqs_gauss_row x, long k, long n)
{
  long i, q, r;
  n = n - k;
  r = n % 8; q = n - r + k; i = 0 + k;
  for (; i < q; i += 8)
  {
    x[0+i] ^= y[0+i]; x[1+i] ^= y[1+i];
    x[2+i] ^= y[2+i]; x[3+i] ^= y[3+i];
    x[4+i] ^= y[4+i]; x[5+i] ^= y[5+i];
    x[6+i] ^= y[6+i]; x[7+i] ^= y[7+i];
  }
  switch (r)
  {
    case 7: x[i] ^= y[i], i++;
    case 6: x[i] ^= y[i], i++;
    case 5: x[i] ^= y[i], i++;
    case 4: x[i] ^= y[i], i++;
    case 3: x[i] ^= y[i], i++;
    case 2: x[i] ^= y[i], i++;
    case 1: x[i] ^= y[i], i++;
    default: ;
  }
}

/* create and read an mpqs_gauss_matrix from a relation file FREL (opened
   by caller).  Also record the position of each relation in the file for
   later use
   rows = size_of_FB+1, cols = rel */
static mpqs_gauss_matrix
mpqs_gauss_read_matrix(FILE *FREL, long rows, long cols, long *fpos)
{
  mpqs_gauss_matrix m;
  long i = 0, e, p;
  char buf[MPQS_STRING_LENGTH], *s;

  m = mpqs_gauss_create_matrix(rows, cols);
  if ((fpos[0] = ftell(FREL)) < 0)
    err(talker, "ftell error on full relations file");
  while (fgets(buf, MPQS_STRING_LENGTH, FREL) != NULL)
  {
    s = strchr(buf, ':') + 2;
    s = strtok(s, " \n");
    while (s != NULL)
    {
      e = atol(s);
      if (e == 0)
	break;
      s = strtok(NULL, " \n");
      p = atol(s);
      if (e & 1)
	mpqs_gauss_set_bit(m, p - 1, i);
      s = strtok(NULL, " \n");
    }
    i++;
    if (i < cols && (fpos[i] = ftell(FREL)) < 0)
      err(talker, "ftell error on full relations file");
  }
  if (i != cols)
  {
    fprintferr("MPQS: full relations file %s than expected",
	       i > cols ? "longer" : "shorter");
    err(talker, "MPQS panicking");
  }
  return m;
}

/* compute the kernel of an mpqs_gauss_matrix over F_2
   uses the algorithm described by Knuth, Vol. 2 as modified by Henri Cohen
   and optimized by Christian Batut, Thomas Papanikolaou and Xavier Roblot.
   m = rows, n = cols */
static mpqs_gauss_matrix
mpqs_kernel(mpqs_gauss_matrix x, long m, long n, long *rank)
{
  long k, i, j, t, r;
  mpqs_gauss_matrix ker_x;
  mpqs_gauss_indices c, d;
  long words = n / MPQS_GAUSS_BITS;
  if (n % MPQS_GAUSS_BITS)
    words++;

  c = (long *) gpmalloc(m * sizeof(long));
  for (k = 0; k < m; k++) c[k] = -1;

  d = (long *) gpmalloc(n * sizeof(long));
  r = 0;

  for (k = 0; k < n; k++)
  {
    j = 0;
    while (j < m && (c[j] >= 0 || mpqs_gauss_get_bit(x, j, k) == 0))
      j++;

    if (j == m)
    {
      d[k] = -1; /* no pivot found in column k */
      r++;       /* column k is a vector of the kernel */
    }
    else
    {
      d[k] = j; /* the pivot in column k is at row j */
      c[j] = k; /* a pivot at position j was found in column k */
      for (t = 0; t < m; t++)
      {
	if (t != j)
	{
	  if (mpqs_gauss_get_bit(x, t, k))
	    mpqs_gauss_add_rows(x[j], x[t], k / MPQS_GAUSS_BITS, words);
        }
      }
    }
  }

  ker_x = mpqs_gauss_create_matrix(n, r);

  for (j = k = 0; j < r; j++, k++)
  {
    while (d[k] != -1) k++;
    for (i = 0; i < k; i++)
    {
      if (d[i] != -1)
      {
	if (mpqs_gauss_get_bit(x, d[i], k))
	  mpqs_gauss_set_bit(ker_x, i, j);
	else
	  mpqs_gauss_clear_bit(ker_x, i, j);
      }
      else
	mpqs_gauss_clear_bit(ker_x, i, j);
    }
    mpqs_gauss_set_bit(ker_x, k, j);
  }

  free(c);
  free(d);

  *rank = r;
  return ker_x;
}

/******************************/

static GEN
mpqs_add_relation(GEN Y_prod, GEN N_or_kN, long *ei, char *r1)
{
  GEN Y, res;
  char relation [MPQS_STRING_LENGTH];
  char *s;
  long e, p;
  pari_sp av = avma;

  strcpy(relation, r1);
  s = strchr(relation, ':') - 1;
  *s = '\0';
  Y = lisexpr(relation);
  res = modii(mulii(Y_prod, Y), N_or_kN);

  s = s + 3;
  s = strtok(s, " \n");
  while (s != NULL)
  {
    e = atol(s);
    if (e == 0)
      break;
    s = strtok(NULL, " \n");
    p = atol(s);
    ei[p] += e;
    s = strtok(NULL, " \n");
  }
  return gerepileupto(av,res);
}

static char*
mpqs_get_relation(long pos, FILE *FREL)
{
  static char buf [MPQS_STRING_LENGTH];
  if (fseek(FREL, pos, SEEK_SET))
    err(talker, "can\'t seek full relations file");
  if (fgets(buf, MPQS_STRING_LENGTH, FREL) == NULL)
    err(talker, "full relations file truncated?!");
  return buf;
}

/* the following two reside in src/basemath/ifactor1.c */
extern long is_odd_power(GEN x, GEN *pt, long *mask);
extern int miller(GEN n, long k);

#define isprobableprime(n) (miller((n),17))

static GEN
mpqs_solve_linear_system(GEN kN, GEN N, long rel, long *FB, long size_of_FB)
{
  pariFILE *pFREL;
  FILE *FREL;
  GEN X, Y_prod, N_or_kN, D1, base, res, new_res;
  pari_sp av=avma, av2, av3, lim, lim3, tetpil;
  long *fpos, *ei;
  long i, j, H_cols, H_rows;
  long res_last, res_next, res_size, res_max;
  mpqs_gauss_matrix m, ker_m;
  long done, flag, mask, rank;

#ifdef MPQS_DEBUG
  N_or_kN = kN;
#else
  N_or_kN = (DEBUGLEVEL >= 4 ? kN : N);
#endif /* --GN */
  pFREL = pari_fopen(FREL_str, READ);
  FREL = pFREL->file;
  fpos = (long *) gpmalloc(rel * sizeof(long));

  m = mpqs_gauss_read_matrix(FREL, size_of_FB+1, rel, fpos);
  if (DEBUGLEVEL >= 7)
  {
    fprintferr("\\\\ MATRIX READ BY MPQS\nFREL=");
    mpqs_gauss_print_matrix(m, size_of_FB+1, rel);
    fprintferr("\n");
  }

  ker_m = mpqs_kernel(m, size_of_FB+1, rel, &rank);
  if (DEBUGLEVEL >= 4)
  {
    if (DEBUGLEVEL >= 7)
    {
      fprintferr("\\\\ KERNEL COMPUTED BY MPQS\nKERNEL=");
      mpqs_gauss_print_matrix(ker_m, rel, rank);
      fprintferr("\n");
    }
    /* put this here where the poor user has a chance of seeing it: */
    fprintferr("MPQS: Gauss done: kernel has rank %ld, taking gcds...\n",
	       rank);
  }

  H_rows = rel;
  H_cols = rank;

  /* If the computed kernel turns out to be trivial, fail gracefully;
     main loop may try to find some more relations --GN */
  if (H_cols == 0)
  {
    if (DEBUGLEVEL >= 3)
      err(warner, "MPQS: no solutions found from linear system solver");
    /* ei has not yet been allocated */
    mpqs_gauss_destroy_matrix(m, size_of_FB+1, rel);
    mpqs_gauss_destroy_matrix(ker_m, rel, rank);
    free(fpos);
    pari_fclose(pFREL);
    avma = av;
    return NULL; /* no factors found */
  }

  /* If the rank is r, we can expect up to 2^r pairwise coprime factors,
     but it may well happen that a kernel basis vector contributes nothing
     new to the decomposition.  We will allocate room for up to eight factors
     initially  (certainly adequate when one or two basis vectors work),
     adjusting this down at the end to what we actually found, or up if
     we are very lucky and find more factors.  In the upper half of our
     vector, we store information about which factors we know to be composite
     (zero) or believe to be composite ((long)NULL which is just 0) or suspect
     to be prime (un), or an exponent (deux or some t_INT) if it is a proper
     power */
  av2 = avma; lim = stack_lim(av2,1);
  if (rank > (long)BITS_IN_LONG - 2)
    res_max = VERYBIGINT;	/* this, unfortunately, is the common case */
  else
    res_max = 1L<<rank;		/* max number of factors we can hope for */
  res_size = 8;			/* no. of factors we can store in this res */
  res = cgetg(2*res_size+1, t_VEC);
  for (i=2*res_size; i; i--) res[i] = 0;
  res_next = res_last = 1;

  ei = (long *) gpmalloc((size_of_FB + 2) * sizeof(long));

  for (i = 0; i < H_cols; i++)	/* loop over basis of kernel */
  {
    X = Y_prod = gun;
    memset(ei, 0, (size_of_FB + 2) * sizeof(long));

    av3 = avma; lim3 = stack_lim(av3,1);
    for (j = 0; j < H_rows; j++)
    {
      if (mpqs_gauss_get_bit(ker_m, j, i))
	Y_prod = mpqs_add_relation(Y_prod, N_or_kN, ei,
				   mpqs_get_relation(fpos[j], FREL));
      if (low_stack(lim3, stack_lim(av3,1)))
      {
	if(DEBUGMEM>1) err(warnmem,"[1]: mpqs_solve_linear_system");
	Y_prod = gerepileupto(av3, Y_prod);
      }
    }
    Y_prod = gerepileupto(av3, Y_prod);	/* unconditionally */

    av3 = avma; lim3 = stack_lim(av3,1);
    for (j = 2; j <= (size_of_FB + 1); j++)
    {
      if (ei[j] & 1)
      {				/* this cannot happen --GN */
	mpqs_gauss_destroy_matrix(m, size_of_FB+1, rel);
	mpqs_gauss_destroy_matrix(ker_m, rel, rank);
	free(ei); free(fpos);
	fprintferr("MPQS: the combination of the relations is a nonsquare\n");
	err(bugparier, "factoring (MPQS)");
      }
      if (ei[j])
      {
	X = modii(mulii(X, powmodulo(stoi(FB[j]), stoi(ei[j]>>1), N_or_kN)),
		  N_or_kN);
	if (low_stack(lim3, stack_lim(av3,1)))
	{
	  if(DEBUGMEM>1) err(warnmem,"[2]: mpqs_solve_linear_system");
	  X = gerepileupto(av3, X);
	}
      }
    }
    X = gerepileupto(av3, X);	/* unconditionally */
    if (
#ifdef MPQS_DEBUG
	1 ||
#endif
	DEBUGLEVEL >= 1)
    {				/* this shouldn't happen either --GN */
      if (signe(modii(subii(sqri(X), sqri(Y_prod)), N_or_kN)))
      {
	fprintferr("MPQS: X^2 - Y^2 != 0 mod %s\n",
		   (N_or_kN == kN ? "kN" : "N"));
	fprintferr("\tindex i = %ld\n", i);
	err(warner, "MPQS: wrong relation found after Gauss");
      }
    }
    /* if res_next < 3, we still haven't decomposed the original N, and
       will want both a gcd and its cofactor, overwriting N.  Note that
       gcd(X+Y_prod,N)==1 forces gcd(X-Y_prod,N)==N, so we can skip X-Y_prod
       in such cases */
    done = 0;			/* (re-)counts probably-prime factors
				   (or powers whose bases we don't want to
				   handle any further) */
    if (res_next < 3)
    {
      D1 = mppgcd(addii(X,Y_prod),N);
      if (!is_pm1(D1))
      {
	if ((flag = egalii(D1, N))) /* assignment */
				/* this one's useless, try the other one */
	  D1 = mppgcd(subii(X,Y_prod),N);
	if (!flag || (!is_pm1(D1) && !egalii(D1,N)))
	{			/* got something that works */
          if (DEBUGLEVEL >= 5)
            fprintferr("MPQS: splitting N after %ld kernel vector%s\n",
                       i+1, (i? "s" : ""));
	  (void)mpdivis(N, D1, N); /* divide N in place */
	  res[1] = (long)N;	/* we'll gcopy this anyway before exiting */
	  res[2] = (long)D1;
	  res_last = res_next = 3;
	  if (res_max == 2) break; /* two out of two possible factors seen */
	  mask = 7;
	  /* (actually, 5th/7th powers aren't really worth the trouble.  OTOH
	     once we have the hooks for dealing with cubes, higher powers can
	     be handled essentially for free) */
	  if (isprobableprime(N)) { done++; res[res_size+1] = un; }
	  else if (carrecomplet(N, &base))
	  {			/* squares could cost us a lot of time */
	    affii(base, N); done++; res[res_size+1] = deux;
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a square\n");
	  }
	  else if ((flag = is_odd_power(N, &base, &mask))) /* assignment */
	  {
	    affii(base, N); done++; res[res_size+1] = (long)(stoi(flag));
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a %s\n",
			 (flag == 3 ? "cube" :
			  (flag == 5 ? "5th power" : "7th power")));
	  }
	  else res[res_size+1] = zero; /* known composite */
	  mask = 7;
	  if (isprobableprime(D1)) { done++; res[res_size+2] = un; }
	  else if (carrecomplet(D1, &base))
	  {
	    res[2] = (long)base;
	    done++; res[res_size+2] = deux;
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a square\n");
	  }
	  else if ((flag = is_odd_power(D1, &base, &mask))) /* assignment */
	  {
	    res[2] = (long)base;
	    done++; res[res_size+2] = (long)(stoi(flag));
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a %s\n",
			 (flag == 3 ? "cube" :
			  (flag == 5 ? "5th power" : "7th power")));
	  }
	  else res[res_size+2] = zero; /* known composite */
	  if (done == 2) break;	/* both factors look prime or were powers */
	  if (DEBUGLEVEL >= 5)
	    fprintferr("MPQS: got two factors, looking for more...\n");
	  /* and loop (after collecting garbage if necessary) */
	} /* else loop to next kernel basis vector */
      } /* D1!=1, nothing to be done when ==1 */
    }
    else			/* we already have factors */
    {
      GEN X_plus_Y = addii(X, Y_prod);
      GEN X_minus_Y = NULL;	/* will only be computed when needed */
      for (j=1; j < res_next; j++)
      {				/* loop over known-composite factors */
	if (res[res_size+j] && res[res_size+j] != zero)
	{
	  done++; continue;	/* skip probable primes etc */
	}
	/* (actually, also skip square roots of squares etc.  They are
	   necessarily a lot smaller than the original N, and should
	   be easy to deal with later) */
	av3 = avma;
	D1 = mppgcd(X_plus_Y, (GEN)(res[j]));
	if (is_pm1(D1)) continue; /* this one doesn't help us */
	if ((flag = egalii(D1, (GEN)(res[j]))))
	{			/* bad one, try the other */
          avma = av3;
	  if (!X_minus_Y) X_minus_Y = subii(X, Y_prod);
          av3 = avma;
	  D1 = mppgcd(X_minus_Y, (GEN)(res[j]));
	}
	if (!flag || (!is_pm1(D1) && !egalii(D1, (GEN)(res[j]))))
	{			/* got one which splits this factor */
          if (DEBUGLEVEL >= 5)
            fprintferr("MPQS: resplitting a factor after %ld kernel vectors\n",
                       i+1);      /* always plural */
	  /* first make sure there's room for another factor */
	  if (res_next > res_size)
	  {			/* need to reallocate (_very_ rare case) */
	    long i1, new_size = 2*res_size;
	    GEN new_res;
	    if (new_size > res_max) new_size = res_max;
	    new_res = cgetg(2*new_size+1, t_VEC);
	    for (i1=2*new_size; i1>=res_next; i1--) new_res[i1] = 0;
	    for (i1=1; i1<res_next; i1++)
	    {
	      new_res[i1] = res[i1]; /* factors */
	      new_res[new_size+i1] = res[res_size+i1]; /* primality tags */
	    }
	    res = new_res; res_size = new_size;	/* res_next unchanged */
	  }
	  /* now there is room; divide into existing factor and store the
	     new gcd.  Remove the known-composite flag from the old entry */
	  (void)mpdivis((GEN)(res[j]), D1, (GEN)(res[j]));
	  res[res_next] = (long)D1; res[res_size+j] = 0;
	  if (++res_next > res_max) break; /* all possible factors seen */
	  mask = 7;		/* check for 3rd and 5th powers */
	  if (isprobableprime((GEN)(res[j])))
	  {
	    done++; res[res_size+j] = un;
	  }
	  else if (carrecomplet((GEN)(res[j]), &base))
	  {
	    /* we no longer bother preserving the cloned N or what is left
	       of it when we hit it here */
	    res[j] = (long)base;
	    done++; res[res_size+j] = deux;
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a square\n");
	  }
	  else if ((flag = is_odd_power((GEN)(res[j]), &base, &mask))) /* = */
	  {
	    res[j] = (long)base;
	    done++; res[res_size+j] = (long)stoi(flag);
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a %s\n",
			 (flag == 3 ? "cube" :
			  (flag == 5 ? "5th power" : "7th power")));
	  }
	  else res[res_size+j] = zero; /* known composite */
	  mask = 7;
	  if (isprobableprime(D1))
	  {
	    done++; res[res_size+res_last] = un;
	  }
	  else if (carrecomplet(D1, &base))
	  {
	    res[res_last] = (long)base;
	    done++; res[res_size+res_last] = deux;
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a square\n");
	  }
	  else if ((flag = is_odd_power(D1, &base, &mask))) /* assignment */
	  {
	    res[res_last] = (long)base;
	    done++; res[res_size+res_last] = (long)stoi(flag);
	    if (DEBUGLEVEL >= 5)
	      fprintferr("MPQS: decomposed a %s\n",
			 (flag == 3 ? "cube" :
			  (flag == 5 ? "5th power" : "7th power")));
	  }
	  else res[res_size+res_last] = zero; /* known composite */
	} /* else it didn't help on this factor, try the next one... */
	else avma = av3;	/* ...after destroying the gcds */
      }	/* loop over known composite factors */
      if (res_next > res_last)
      {
	if (DEBUGLEVEL >= 5 && done < res_last)
	  fprintferr("MPQS: got %ld factors%s\n",
		     res_last,
		     (done < res_last ? ", looking for more..." : ""));
	res_last = res_next;
      }
      /* we should break out of the outer loop when we have seen res_max
	 factors, and also when all current factors are probable primes */
      if (res_next > res_max || done == res_next - 1) break;
      /* else continue loop over kernel basis */
    } /* end case of further splitting of existing factors */
    /* garbage collection */
    if (low_stack(lim, stack_lim(av2,1)))
    {
      long i1;
      if(DEBUGMEM>1) err(warnmem,"[3]: mpqs_solve_linear_system");
      tetpil=avma;
      /* gcopy would have a problem with our NULL pointers... */
      new_res = cgetg(lg(res), t_VEC);
      for (i1=2*res_size; i1>=res_next; i1--) new_res[i1] = 0;
      for (i1=1; i1<res_next; i1++)
      {
	new_res[i1] =
	  (isonstack((GEN)(res[i1])) ? licopy((GEN)(res[i1])) : res[i1]);
	new_res[res_size+i1] = res[res_size+i1];
      }
      res = gerepile(av2, tetpil, new_res);
      /* discard X and Y_prod */
    }
  } /* for (loop over kernel basis) */

  if (res_next < 3)		/* still no factors seen */
  {
    pari_fclose(pFREL);
    mpqs_gauss_destroy_matrix(m, size_of_FB+1, rel);
    mpqs_gauss_destroy_matrix(ker_m, rel, rank);
    free(ei); free(fpos);
    avma = av;
    return NULL; /* no factors found */
  }
  /* normal case:  convert internal format to ifac format as described in
     src/basemath/ifactor1.c  (triples of components: value, exponent, class
     [unknown, known composite, known prime]),  clean up and return result */
  pari_fclose(pFREL);
  mpqs_gauss_destroy_matrix(m, size_of_FB+1, rel);
  mpqs_gauss_destroy_matrix(ker_m, rel, rank);
  free(ei); free(fpos);
  res_last = res_next - 1;	/* number of distinct factors found */
  new_res = cgetg(3*res_last + 1, t_VEC);
  if (DEBUGLEVEL >= 6)
    fprintferr("MPQS: wrapping up vector of %ld factors\n", res_last);
  for (i=1,j=1; i <= res_last; i++)
  {
    new_res[j++] =		/* value of factor */
      isonstack((GEN)(res[i])) ? licopy((GEN)(res[i])) : res[i];
    flag = res[res_size+i];
    new_res[j++] =		/* exponent */
      flag ?			/* flag was zero or un or ... */
	(flag == zero ? un :
	 (isonstack((GEN)flag) ? licopy((GEN)flag) : flag)
	 ) :
	   un;			/* flag was (long)NULL */
    new_res[j++] =		/* class */
      flag == zero ? zero :	/* known composite */		
	(long)NULL;		/* base of power or suspected prime --
				   mark as `unknown' */
    if (DEBUGLEVEL >= 6)
      fprintferr("\tpackaging %ld: %Z ^%ld (%s)\n", i, res[i],
		 itos((GEN)(new_res[j-2])),
		 (flag == zero ? "comp." : "unknown"));
  }
  return gerepileupto(av, new_res);
}

/******************************/

/* All percentages below are actually fixed-point quantities scaled by 10
   (value of 1 means 0.1%, 1000 means 100%). --GN */

#define max_percentage 1500	/* give up when nothing found after ~1.5
				   times the required number of relations has
				   been computed  (n might be a prime power
				   or the parameters might be exceptionally
				   unfortunate for it) --GN */

/**
 ** Factors N using the self-initializing multipolynomial quadratic sieve
 ** (SIMPQS).  Returns one of the two factors, or (usually) a vector of
 ** factors and exponents and information about which ones are definitely
 ** still composite, or NULL when something goes wrong or when we can't
 ** seem to make any headway.
 **/

/* TODO: this function to be renamed mpqs_main() with several extra para-
   meters, with mpqs() as a wrapper for the standard case, so we can do
   partial runs distributed across several machines etc.  (not necessarily
   from gp, but certainly from a small dedicated C program). --GN */

GEN
mpqs(GEN N)
{
  GEN fact;			/* will in the end hold our factor(s) */
  ulong decimal_digits;		/* number of decimals of N */
  long tc;			/* number of candidates found in one
				   iteration */
  long t;			/* number of full relations found in one
				   iteration */
  long tp;			/* number of full relations found in one
				   iteration after combining large prime
				   relations */
  long k;			/* the multiplier */
  GEN kN;			/* k * N */
  double sqrt_kN;		/* double approximation of sqrt(k*N) */
  long *FB;			/* the factor base */
  ulong size_of_FB;		/* the size of the factor base */
  ulong FB_overshoot;		/* the number of relations aimed for */
  double log_multiplier;	/* maps logarithms of FB elements to
				   unsigned chars */
  double tolerance;		/* used in sieving with logarithms */
  unsigned char *log_FB;	/* logarithms of FB elements mapped to
				   unsigned chars */
  unsigned char *sieve_array;	/* the sieve array */
  unsigned char *sieve_array_end; /* the end of the sieve array */
  ulong M;			/* the sieve interval size [-M, M] */
  ulong starting_sieving_index;	/* the first element in the FB used for
				   sieving */
  long last_prime_in_FB;	/* the biggest prime in FB */
  long *sqrt_mod_p_kN;		/* array containing sqrt(K*N) mod p_i,
				   where p_i are FB elements */
  GEN A, B, inv_A4;		/* coefficients of polynomials in (SI) */
  long *Q_prime_glob, *Q_prime;	/* used for self initialization (SI) */
  GEN *H_i;			/* will be used to compute the consecutive
				   B during (SI) */
  long start_index_FB_for_A;	/* the first index in the FB used for
				   computing A during (SI), minus 1 */
  ulong no_of_primes_in_A;	/* number of primes dividing A
				   during (SI) */
  ulong total_no_of_primes_for_A; /* number of primes used for finding A
				     during (SI) */
  long max_no_of_B;		/* how many B's to use before choosing
				   a new A during (SI) */
  long index_i;			/* denotes the current pair of coeffs
				   (A, B_i). If i == 0, a new A is
				   generated */
  ulong bin_index;		/* used for choosing the prime factors for
				   for the A coeffs in mpqs_self_init() */
  long i, p;			/* counters */

  /* Let (z0, z1) be the roots of Q(x) = A x^2 + Bx +C mod p_i;
     then we know that
     Q(z1 + i k) == 0 mod p_i and Q(z2 + i k) == 0 mod p_i */

  long *start_1;		/* stores the position where p_i
				   divides Q(x) for the first time,
				   using z1 */
  long *start_2;		/* same, but using z2 */
  long *inv_A2;			/* inv_A2[i] = 1/(2*A) mod p_i */
  long **inv_A_H_i;		/* inv_A_H_i[i][j] = 1/A H_i[i] mod p_j */
  long *candidates;		/* positions in the sieve_array which
				   probably factor over the FB */
  long lp_bound;		/* size limit for large primes */
  ulong sort_interval;		/* these determine when to sort and merge */
  ulong followup_sort_interval;	/* the temporary files (scaled percentages) */
  long total_full_relations = 0;
  long total_partial_relations = 0;
  pariFILE *pFREL;
  pariFILE *pFNEW;
  pariFILE *pLPREL;
  pariFILE *pLPNEW;
  pariFILE *pCOMB;
  FILE *FNEW;
  FILE *LPNEW;
  long percentage = 0;		/* scaled by 10, see comment above */
  long total_candidates_number = 0;
  long useless_candidates = 0;	/* another scaled percentage */
  long vain_iterations = 0;
  long good_iterations = 0;
  long iterations = 0;
  pari_sp av = avma;

  /* state flags for cleanup if we get interrupted --GN */
  static char all_clean = 1;	/* set to 0 while mpqs() is busy */

  if (DEBUGLEVEL >= 4)
  {
    if (!all_clean) { /* TODO: clean up... */ }
    (void) timer2();		/* clear timer */
    fprintferr("MPQS: number to factor N = %Z\n", N);
  }

  all_clean = 0;		/* activate clean-up trap */
  {
    char *s = GENtostr(N);
    decimal_digits = strlen(s);
    free(s);
  }

  if (decimal_digits >= 108)	/* changed to match Denny's parameters */
  {
    err(warner, "MPQS: number too big to be factored with MPQS, giving up");
    avma = av;
    all_clean = 1;
    return NULL;
  }

  if (DEBUGLEVEL >= 4)
    fprintferr("MPQS: factoring number of %ld decimal digits\n",
	       decimal_digits);

  if (decimal_digits >= 70)
    err(warner,
	"MPQS: the factorization of this number will take %s hours",
	decimal_digits >= 84 ? "many" : "several");

  k = mpqs_find_k(N, 5);
  if (DEBUGLEVEL >= 5)
    fprintferr("MPQS: found multiplier %ld for N\n", k);

  kN = mulis(N, k);
  {
    char *s = GENtostr(kN);
    decimal_digits = strlen(s);
    free(s);
  }

  if (DEBUGLEVEL >= 5)
  {
    fprintferr("MPQS: kN = %Z\n", kN);
    fprintferr("MPQS: kN has %ld decimal digits\n",
	       decimal_digits);
  }

  mpqs_read_parameters(decimal_digits, &tolerance, &M, &size_of_FB,
		       &FB_overshoot,
                       &no_of_primes_in_A, &total_no_of_primes_for_A,
                       &max_no_of_B, &starting_sieving_index,
		       &sort_interval, &followup_sort_interval);
  {
    double bytesize = (size_of_FB + 1)/(8.*1048576.);
    bytesize *= FB_overshoot;
    if (bytesize > 32.)
    {
      err(warner,
	  "MPQS: Gauss elimination will require more than 32MBy of memory");
      if (DEBUGLEVEL >= 1)
	fprintferr("\t(estimated memory needed: %4.1fMBy)\n", bytesize);
    }
  }

  if (DEBUGLEVEL >= 4)
  {
    fprintferr("MPQS: sieving interval = [%ld, %ld]\n",
	       -(long)M, M);
    fprintferr("MPQS: size of factor base = %ld\n",
	       size_of_FB);
    fprintferr("MPQS: striving for %ld relations\n",
	       FB_overshoot);
    fprintferr("MPQS: first sorting at %ld%%, then every %3.1f%% / %3.1f%%\n",
	       sort_interval/10, followup_sort_interval/10.,
	       followup_sort_interval/20.);
    fprintferr("MPQS: initial sieving index = %ld\n",
	       starting_sieving_index);
  }
  sieve_array =
    (unsigned char *) gpmalloc((M << 1) * sizeof(unsigned char));
  sieve_array_end = sieve_array + (M << 1) - 1;

  if (DEBUGLEVEL >= 5)
    fprintferr("MPQS: creating factor base FB of size = %ld\n",
	       size_of_FB);

  FB = mpqs_create_FB(size_of_FB, kN, k, &p);

  /* the following this way round to avoid overflow: --GN */
  lp_bound = FB[FB[0]+1];
  if (DEBUGLEVEL >= 4)
    fprintferr("MPQS: largest prime in FB = %ld\n",
	       lp_bound);
  if (lp_bound > MPQS_LP_BOUND)
    lp_bound = MPQS_LP_BOUND;
  lp_bound *= MPQS_LP_FACTOR;
  if (DEBUGLEVEL >= 4)
    fprintferr("MPQS: bound for `large primes\' = %ld\n",
	       lp_bound);

  if (p != 0)
  {
    free(FB);
    free(sieve_array);
    if (DEBUGLEVEL >= 4)
      fprintferr("\nMPQS: found factor = %ld whilst creating factor base\n",
		 p);
    if (mpqs_diffptr == diffptr) mpqs_diffptr = NULL;
    avma = av;
    /* TODO: free the FB etc!!! */
    all_clean = 1;
    return stoi(p);
  }

  if (DEBUGLEVEL >= 5)
  {
    fprintferr("MPQS: computing logarithm approximations for p_i in FB\n");
    fprintferr("MPQS: computing sqrt(k*N) mod p_i\n");
  }
  last_prime_in_FB = FB[FB[0] + 1];
  log_multiplier = (2 * (unsigned char) (0.5 * log2 (gtodouble(kN)) +
                           log2 ((double) M) - tolerance *
                           log2 ((double) last_prime_in_FB)));
  log_multiplier = 127.0 / log_multiplier;

  log_FB =
    (unsigned char *) gpmalloc((size_of_FB + 2) * sizeof(unsigned char));
  sqrt_mod_p_kN =
    (long *) gpmalloc((size_of_FB + 2) * sizeof(long));

  for (i = 2; (ulong)i < size_of_FB + 2; i++)
  {
    pari_sp av1 = avma;
    p = FB[i];

    /* compute the approximations of the logarithms of p_i */
    log_FB[i] =
      (unsigned char) (log_multiplier * log2 ((double) p) * 2);

    /* compute the x_i such that x_i^2 = (kN % p_i) mod p_i */
    sqrt_mod_p_kN[i] = itos(mpsqrtmod(modis(kN, p), stoi(p)));
    avma = av1;
  }

  if (DEBUGLEVEL >= 5)
    fprintferr("MPQS: allocating arrays for self-initialization\n");

  /* the size of coefficient A should be approximately */
  /* sqrt(kN)/M, so the size of the primes p dividing */
  /* A should be approximately (sqrt(kN/M))^(1/no_of_primes_in_A) */

  /* compute expected size of coefficients, which also defines the tolerance
     for the logarithmic sieve */
  sqrt_kN = sqrt(gtodouble(kN));
  tolerance = sqrt_kN / M;
  tolerance =  pow(2.0, log2(tolerance) / no_of_primes_in_A);
  if (tolerance > FB[size_of_FB - 1]) /* ??? */
    err(talker, "MPQS: number of prime factors in A is too small");

  /* choose primes in FB to use for building the A coefficient */
  start_index_FB_for_A = 2;
  while (FB[start_index_FB_for_A] < tolerance)
    start_index_FB_for_A++;

  if (start_index_FB_for_A > 7)
    start_index_FB_for_A -= (no_of_primes_in_A >> 1);

  /* ensure that the primes to be used for A do occur in the FB */
  if (start_index_FB_for_A + total_no_of_primes_for_A >= size_of_FB)
    start_index_FB_for_A = size_of_FB - total_no_of_primes_for_A - 1;

  /* ensure that the multiplier k is smaller than the prime divisors of A */
  if (k >= FB[start_index_FB_for_A])
  {
    do
      start_index_FB_for_A++;
    while (k >= FB[start_index_FB_for_A]);
    if (start_index_FB_for_A + total_no_of_primes_for_A >= size_of_FB)
      err(talker,
	  "MPQS: number of primes for A is too large, or FB too small");
    /* this shouldn't happen */
  }

  /* now a selection of total_no_of_primes_for_A consecutive primes
   * p = FB[start_index_FB_for_A+1], ... is chosen from the factor base */

  /* (no need to copy them around as long as they are consecutive entries
     in FB --GN) */
  Q_prime =
    (long *) gpmalloc(no_of_primes_in_A * sizeof(long));
#if 1
  Q_prime_glob = &(FB[start_index_FB_for_A + 1]);
#else
  Q_prime_glob =
    (long *) gpmalloc(total_no_of_primes_for_A * sizeof(long));
  for (i = 0; i < total_no_of_primes_for_A; i++)
    Q_prime_glob[i] = FB[start_index_FB_for_A + i + 1];
#endif

  /* used for choosing the correct A coeffs in mpqs_self_init() */
  bin_index = 0;

  /* will be used to compute the consecutive B during
     self-initialization */
  H_i = (GEN *) gpmalloc(no_of_primes_in_A * sizeof(GEN));
  for (i = 0; (ulong)i < no_of_primes_in_A; i++)
    H_i[i] = cgeti(2 * total_no_of_primes_for_A);

  inv_A_H_i =
    (long **) gpmalloc(total_no_of_primes_for_A * sizeof(long *));
  for (i = 0; (ulong)i < total_no_of_primes_for_A; i++)
    inv_A_H_i[i] = (long *) gpmalloc((size_of_FB + 2) * sizeof(long));

  start_1 = (long *) gpmalloc((size_of_FB + 2) * sizeof(long));
  start_2 = (long *) gpmalloc((size_of_FB + 2) * sizeof(long));

  /* the next will hold 1/(2*A) mod p_i, p_i in FB */
  inv_A2 = (long *) gpmalloc((size_of_FB + 2) * sizeof(long));

  candidates = (long *) gpmalloc(MPQS_CANDIDATE_ARRAY_SIZE * sizeof(long));

  if (DEBUGLEVEL >= 5)
  {
    fprintferr("MPQS: index range of primes for A: [%ld, %ld]\n",
	       start_index_FB_for_A + 1,
	       start_index_FB_for_A + total_no_of_primes_for_A);
    fprintferr("MPQS: coefficients A will be built from %ld primes each\n",
	       no_of_primes_in_A);
  }

/* CLEAN UP define */

#define CLEANUP() \
  free(FB); \
  free(sieve_array); \
  free(log_FB); \
  free(sqrt_mod_p_kN); \
  free(Q_prime); \
/*  free(Q_prime_glob); */ \
  free(H_i); \
  for (i = 0; (ulong)i < total_no_of_primes_for_A; i++) \
    free(inv_A_H_i[i]); \
  free(inv_A_H_i); \
  free(start_1); \
  free(start_2); \
  free(inv_A2); \
  free(candidates);

  /*
   * main loop which
   * - computes polynomials and their zeros (self initialization)
   * - does the sieving
   * - tests candidates of the sieve array
   */

  /* denotes the current pair of coeffs (A, B_i). If i == 0 a new A is
    generated */
  index_i = -1;

  /* the coefficients of the polynomial currently used for sieving */
  /* A will be at most as long as the product of
     no_of_primes_in_A word-sized primes (was total_..., GN) */
  /* B needs at most total_no_of_primes_for_A + 1 words [CHECK] --GN */
  /* Take the double is just for safety ... */
  A = cgeti(2 * no_of_primes_in_A);
  B = cgeti(2 * total_no_of_primes_for_A + 1);

  /* 1/4A mod kN */
  inv_A4 = cgeti(lg(kN));

  if (DEBUGLEVEL >= 5)
    fprintferr("MPQS: starting main loop\n");
  /* compute names for the temp files we'll need */
  FREL_str  = mpqs_get_filename("FREL");
  FNEW_str  = mpqs_get_filename("FNEW");
  LPREL_str = mpqs_get_filename("LPREL");
  LPNEW_str = mpqs_get_filename("LPNEW");
  COMB_str  = mpqs_get_filename("COMB");
  TMP_str = mpqs_get_filename("LPTMP");

  /* just to create the temp files */
  pFREL  = pari_safefopen(FREL_str,  WRITE); pari_fclose(pFREL);
  pLPREL = pari_safefopen(LPREL_str, WRITE); pari_fclose(pLPREL);

  pFNEW = pari_safefopen(FNEW_str,  WRITE);  FNEW = pFNEW->file;
  pLPNEW= pari_safefopen(LPNEW_str, WRITE); LPNEW = pLPNEW->file;
  for(;;)
  {
    /* at start of loop, FNEW and LPNEW are open for writing */
    iterations++;
    /* when all of the B's have already been used, choose new A ;
       this is indicated by setting index_i to 0 */
    if (index_i == (max_no_of_B - 1))
      index_i = 0;
    else
      index_i++;

    /* self initialization: compute polynomial and its zeros */

    mpqs_self_init(A, B, N, kN, FB, sqrt_mod_p_kN, start_1, start_2,
		   no_of_primes_in_A, total_no_of_primes_for_A,
		   M, inv_A_H_i, Q_prime, Q_prime_glob, H_i,
		   index_i, start_index_FB_for_A, inv_A2, inv_A4,
		   &bin_index, &fact);
    if (bin_index >= (1ul << total_no_of_primes_for_A)) /* wraparound */
    {
      /* TODO: increase some parameters.  For the moment, simply give up */
      CLEANUP();
      pari_fclose(pFNEW);
      pari_fclose(pLPNEW);
      /* FREL, LPREL are closed at this point */
      pari_unlink(FREL_str);
      pari_unlink(FNEW_str);
      pari_unlink(LPREL_str);
      pari_unlink(LPNEW_str);
      if (mpqs_diffptr == diffptr) mpqs_diffptr = NULL;
      all_clean = 1;
      avma=av; return NULL;
    }
    if (fact)			/* A4 not coprime to kN, fact divides N */
    {				/* (cannot actually happen) */
      if (is_pm1(fact) || egalii(fact,N))
	continue;		/* cannot use the current polynomial */
      CLEANUP();
      pari_fclose(pFNEW);
      pari_fclose(pLPNEW);
      pari_unlink(FREL_str);
      pari_unlink(FNEW_str);
      pari_unlink(LPREL_str);
      pari_unlink(LPNEW_str);
      if (mpqs_diffptr == diffptr) mpqs_diffptr = NULL;
      all_clean = 1;
      if (DEBUGLEVEL >= 4)
      {
	fprintferr("MPQS: whilst trying to invert A4 mod kN,\n");
	fprintferr("\tfound factor = %Z\n", fact);
	flusherr();
      }
      return gerepileupto(av, fact);
    }

    if (DEBUGLEVEL >= 6)
    {
      if (!index_i)
	fprintferr("MPQS: chose prime pattern 0x%lX for A\n",
		   bin_index);
      if (signe(B) < 0)
      {
	setsigne(B,1);
	fprintferr("MPQS: chose Q_%ld(x) = %Z x^2 - %Z x + C\n",
		   index_i, A, B);
	setsigne(B,-1);
      }
      else
      {
	fprintferr("MPQS: chose Q_%ld(x) = %Z x^2 + %Z x + C\n",
		   index_i, A, B);
      }
    }

    mpqs_sieve(FB, log_FB, start_1, start_2, sieve_array,
	       sieve_array_end, M, starting_sieving_index);

    tc = mpqs_eval_sieve(sieve_array, M, candidates);
    total_candidates_number += tc;
    if (DEBUGLEVEL >= 6)
      fprintferr("MPQS: found %lu candidate%s\n",
		 tc, (tc==1? "" : "s"));

    if (tc)
    {
      good_iterations++;
      t = mpqs_eval_candidates(A, inv_A4, B, kN, k, sqrt_kN, FB,
			       start_1, start_2,
			       M, bin_index, candidates, tc, lp_bound,
			       start_index_FB_for_A, FNEW, LPNEW);
    }
    else
      t = 0;

    total_full_relations += t;
    percentage =
      (long)((1000.0 * total_full_relations) / FB_overshoot);
    useless_candidates =
      (long)((1000.0 * (total_candidates_number - total_full_relations))
	     / (total_candidates_number ? total_candidates_number : 1));

    if ((ulong)percentage < sort_interval)
      continue;			/* most main loops end here... */

    /* Extra processing when we have completed a sort interval: */
    if (DEBUGLEVEL >= 3)
    {
      if (DEBUGLEVEL >= 4)
	fprintferr("\nMPQS: passing the %3.1f%% checkpoint, time = %ld ms\n",
		   sort_interval/10., timer2());
      else
	fprintferr("\nMPQS: passing the %3.1f%% checkpoint\n",
		   sort_interval/10.);
      flusherr();
    }
    /* sort LPNEW and merge it into LPREL, diverting combinables into COMB */
    pari_fclose(pLPNEW);
    (void)mpqs_sort_lp_file(LPNEW_str);
    tp = mpqs_mergesort_lp_file(LPREL_str, LPNEW_str, 0);
    pLPNEW = pari_fopen(LPNEW_str, WRITE); /* NOT safefopen */
    LPNEW = pLPNEW->file;

    /* combine whatever there is to be combined */
    if (tp > 0)
    {
      /* build full relations out of large prime relations */
      pCOMB = pari_fopen(COMB_str, READ);
      tp = mpqs_combine_large_primes(pCOMB->file, FNEW, size_of_FB, N, kN, &fact
#ifdef MPQS_DEBUG
				     , FB
#endif
      );
      pari_fclose(pCOMB);
      pari_unlink(COMB_str);
      /* now FREL, LPREL are closed and FNEW, LPNEW are still open */
      if (fact)			/* factor found during combining */
      {
	/* clean up */
	CLEANUP();
	pari_fclose(pLPNEW);
	pari_fclose(pFNEW);
	pari_unlink(FREL_str);
	pari_unlink(FNEW_str);
	pari_unlink(LPREL_str);
	pari_unlink(LPNEW_str);
	if (DEBUGLEVEL >= 4)
	{
	  fprintferr("\nMPQS: split N whilst combining, time = %ld ms\n",
		     timer2());
	  fprintferr("MPQS: found factor = %Z\n", fact);
	}
	if (mpqs_diffptr == diffptr) mpqs_diffptr = NULL;
	all_clean = 1;
	return gerepileupto(av, fact);
      }
    }

    /* sort FNEW and merge it into FREL */
    pari_fclose(pFNEW);
    (void)mpqs_sort_lp_file(FNEW_str);
    total_full_relations = mpqs_mergesort_lp_file(FREL_str, FNEW_str, 1);
    /* this being the definitive count (combinables combined, and
       duplicates removed) */
    /* FNEW stays closed until we know whether we need to reopen it for
       another iteration */

    total_partial_relations += tp;

    /* note that due to the removal of duplicates, percentage may actually
       decrease at this point.  This may look funny in the diagnostics but
       is nothing to worry about, since we _are_ making progress neverthe-
       less. --GN */
    percentage =
      (long)((1000.0 * total_full_relations) / FB_overshoot);
    vain_iterations =
      (long)((1000.0 * (iterations - good_iterations))
	     / iterations);

    /* TODO: the following could be improved (extrapolate from past
       experience how many combined full relations we can expect in
       addition to those we're finding directly) --GN */
    if (percentage >= 840)
    {
      if (percentage >= 980)
	sort_interval = percentage + 10;
      else
	sort_interval = percentage + (followup_sort_interval >> 1);
      if (sort_interval >= 1000 && percentage < 1000)
	sort_interval = 1000;
    }
    else
    {
      sort_interval = percentage + followup_sort_interval;
    }

    if (DEBUGLEVEL >= 4)
    {
      fprintferr("MPQS: done sorting%s, time = %ld ms\n",
		 tp > 0 ? " and combining" : "",
		 timer2());
      fprintferr("MPQS: found %3.1f%% of the required relations\n",
		 percentage/10.);
      if (DEBUGLEVEL >= 5)
      {
	/* total_full_relations are always plural */
	fprintferr("MPQS: found %ld full relations\n",
		   total_full_relations);
	fprintferr("MPQS:   (%ld of these from partial relations)\n",
		   total_partial_relations);
	fprintferr("MPQS: %4.1f%% useless candidates\n",
		   useless_candidates/10.);
	fprintferr("MPQS: %4.1f%% of the iterations yielded no candidates\n",
		   vain_iterations/10.);
	fprintferr("MPQS: next checkpoint at %3.1f%%\n",
		   sort_interval/10.);
      }
    }

    if (percentage < 1000)
    {
      pFNEW = pari_fopen(FNEW_str, WRITE); /* NOT safefopen */
      FNEW = pFNEW->file;
      /* at this point, LPNEW and FNEW are again open for writing */
      continue;			/* main loop */
    }

    /* percentage >= 1000, which implies total_full_relations > size_of_FB:
       try finishing it off */

    /* solve the system over F_2 */
    if (DEBUGLEVEL >= 4)
      fprintferr("\nMPQS: starting Gauss over F_2 on %ld distinct relations\n",
		 total_full_relations);
    fact = mpqs_solve_linear_system(kN, N,
				    total_full_relations,
				    FB, size_of_FB);

    /* if solution found, clean up and return */
    if (fact)
    {
      /* clean up */
      CLEANUP();
      pari_fclose(pLPNEW);
      pari_unlink(FREL_str);
      pari_unlink(FNEW_str);
      pari_unlink(LPREL_str);
      pari_unlink(LPNEW_str);
      if (DEBUGLEVEL >= 4)
      {
	fprintferr("\nMPQS: time in Gauss and gcds = %ld ms\n",
		   timer2());
	if (typ(fact) == t_INT)
	  fprintferr("MPQS: found factor = %Z\n", fact);
	else
	{
	  long j, nf=(lg(fact)-1)/3;
	  if (nf==2)
	    fprintferr("MPQS: found factors = %Z\n\tand %Z\n",
		        fact[4], fact[1]);
	  else
	  {
	    fprintferr("MPQS: found %ld factors =\n", nf);
	    for (j=nf; j; j--)
	      fprintferr("\t%Z%s\n", fact[3*j-2], (j>1? "," : ""));
	  }
	}
      }
      if (mpqs_diffptr == diffptr) mpqs_diffptr = NULL;
      all_clean = 1;
      /* nuisance: fact may not be safe for a gcopy(), and thus
	 gerepilecopy(av, fact) will usually segfault on
	 one of the NULL markers.  However, it is already a nice
	 connected object, and it resides already the top of the
	 stack, so... :^) --GN */
      return gerepileupto(av, fact);
    }
    else
    {
      if (DEBUGLEVEL >= 4)
      {
	fprintferr("\nMPQS: time in Gauss and gcds = %ld ms\n",
		   timer2());
	fprintferr("MPQS: no factors found.\n");
	if (percentage <= max_percentage)
	  fprintferr("\nMPQS: restarting sieving ...\n");
	else
	  fprintferr("\nMPQS: giving up.\n");
      }
      if (percentage > max_percentage)
      {
	/* clean up */
	CLEANUP();
	pari_fclose(pLPNEW);
	pari_unlink(FREL_str);
	pari_unlink(FNEW_str);
	pari_unlink(LPREL_str);
	pari_unlink(LPNEW_str);
	if (mpqs_diffptr == diffptr) mpqs_diffptr = NULL;
	all_clean = 1;
	avma=av; return NULL;
      }
      pFNEW = pari_fopen(FNEW_str, WRITE); /* NOT safefopen */
      FNEW = pFNEW->file;
    }
  } /* main loop */
}
