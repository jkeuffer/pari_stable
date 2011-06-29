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
/*********************************************************************/
/**                                                                 **/
/**                       BINARY DECOMPOSITION                      **/
/**                                                                 **/
/*********************************************************************/

INLINE GEN
inegate(GEN z) { return subsi(-1,z); }

GEN
binaire(GEN x)
{
  ulong m,u;
  long i,lx,ex,ly,tx=typ(x);
  GEN y,p1,p2;

  switch(tx)
  {
    case t_INT:
    {
      GEN xp=int_MSW(x);
      lx=lgefint(x);
      if (lx==2) return mkvec(gen_0);
      ly = BITS_IN_LONG+1; m=HIGHBIT; u=*xp;
      while (!(m & u)) { m>>=1; ly--; }
      y = cgetg(ly + bit_accuracy(lx-1), t_VEC); ly=1;
      do { gel(y,ly) = m & u ? gen_1 : gen_0; ly++; } while (m>>=1);
      for (i=3; i<lx; i++)
      {
        m=HIGHBIT; xp=int_precW(xp); u=*xp;
        do { gel(y,ly) = m & u ? gen_1 : gen_0; ly++; } while (m>>=1);
      }
      break;
    }
    case t_REAL:
      ex=expo(x);
      if (!signe(x)) return const_vec(maxss(-ex,0), gen_0);

      lx=lg(x); y=cgetg(3,t_VEC);
      if (ex > bit_prec(x)) pari_err(precer,"binary");
      p1 = cgetg(maxss(ex,0)+2,t_VEC);
      p2 = cgetg(bit_prec(x)-ex,t_VEC);
      gel(y,1) = p1;
      gel(y,2) = p2;
      ly = -ex; ex++; m = HIGHBIT;
      if (ex<=0)
      {
        gel(p1,1) = gen_0; for (i=1; i <= -ex; i++) gel(p2,i) = gen_0;
        i=2;
      }
      else
      {
        ly=1;
        for (i=2; i<lx && ly<=ex; i++)
        {
          m=HIGHBIT; u=x[i];
          do
            { gel(p1,ly) = (m & u) ? gen_1 : gen_0; ly++; }
          while ((m>>=1) && ly<=ex);
        }
        ly=1;
        if (m) i--; else m=HIGHBIT;
      }
      for (; i<lx; i++)
      {
        u=x[i];
        do { gel(p2,ly) = m & u ? gen_1 : gen_0; ly++; } while (m>>=1);
        m=HIGHBIT;
      }
      break;

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = binaire(gel(x,i));
      break;
    default: pari_err(typeer,"binary");
      return NULL; /* not reached */
  }
  return y;
}

/* return 1 if bit n of x is set, 0 otherwise */
long
bittest(GEN x, long n)
{
  long q, r;

  if (typ(x) != t_INT) pari_err(arither1);
  if (!signe(x) || n < 0) return 0;
  if (signe(x) < 0)
  {
    pari_sp ltop=avma;
    long b = !bittest(inegate(x),n);
    avma=ltop;
    return b;
  }
  q = dvmdsBIL(n, &r);
  if (q+3 > lgefint(x)) return 0;
  return (*int_W(x,q) >> r) & 1;
}

GEN
gbittest(GEN x, long n) { return map_proto_lGL(bittest,x,n); }

/***********************************************************************/
/**                                                                   **/
/**                          BITMAP OPS                               **/
/** x & y (and), x | y (or), x ^ y (xor), ~x (neg), x & ~y (negimply) **/
/**                                                                   **/
/***********************************************************************/
/* Truncate a non-negative integer to a number of bits.  */
static GEN
ibittrunc(GEN x, long bits)
{
  long lowbits, known_zero_words, xl = lgefint(x) - 2;
  long len_out = nbits2nlong(bits);

  if (xl < len_out)
    return x;
      /* Check whether mask is trivial */
  lowbits = bits & (BITS_IN_LONG-1);
  if (!lowbits) {
    if (xl == len_out)
      return x;
  } else if (len_out <= xl) {
    GEN xi = int_W(x, len_out-1);
    /* Non-trival mask is given by a formula, if x is not
       normalized, this works even in the exceptional case */
    *xi &= (1L << lowbits) - 1;
    if (*xi && xl == len_out) return x;
  }
  /* Normalize */
  known_zero_words = xl - len_out;
  if (known_zero_words < 0) known_zero_words = 0;
  return int_normalize(x, known_zero_words);
}

GEN
gbitneg(GEN x, long bits)
{
  const ulong uzero = 0;
  long lowbits, xl, len_out, i;

  if (typ(x) != t_INT)
    pari_err(typeer, "bitwise negation");
  if (bits < -1)
    pari_err(talker, "negative exponent in bitwise negation");
  if (bits == -1) return inegate(x);
  if (bits == 0) return gen_0;
  if (signe(x) < 0) { /* Consider as if mod big power of 2 */
    pari_sp ltop = avma;
    return gerepileuptoint(ltop, ibittrunc(inegate(x), bits));
  }
  xl = lgefint(x);
  len_out = nbits2lg(bits);
  lowbits = bits & (BITS_IN_LONG-1);
  if (len_out > xl) /* Need to grow */
  {
    GEN out, outp, xp = int_MSW(x);
    out = cgetipos(len_out);
    outp = int_MSW(out);
    if (!lowbits)
      *outp = ~uzero;
    else
      *outp = (1L << lowbits) - 1;
    for (i = 3; i < len_out - xl + 2; i++)
    {
      outp = int_precW(outp); *outp = ~uzero;
    }
    for (     ; i < len_out; i++)
    {
      outp = int_precW(outp); *outp = ~*xp;
      xp   = int_precW(xp);
    }
    return out;
  }
  x = icopy(x);
  for (i = 2; i < xl; i++) x[i] = ~x[i];
  return ibittrunc(int_normalize(x,0), bits);
}

/* bitwise 'and' of two positive integers (any integers, but we ignore sign).
 * Inputs are not necessary normalized. */
GEN
ibitand(GEN x, GEN y)
{
  long lx, ly, lout;
  long *xp, *yp, *outp;
  GEN out;
  long i;

  if (!signe(x) || !signe(y)) return gen_0;
  lx=lgefint(x); ly=lgefint(y);
  lout = minss(lx,ly); /* > 2 */
  xp = int_LSW(x);
  yp = int_LSW(y);
  out = cgetipos(lout);
  outp = int_LSW(out);
  for (i=2; i<lout; i++)
  {
    *outp = (*xp) & (*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

/* bitwise 'or' of absolute values of two integers */
GEN
ibitor(GEN x, GEN y)
{
  long lx, ly;
  long *xp, *yp, *outp;
  GEN  out;
  long i;
  if (!signe(x)) return absi(y);
  if (!signe(y)) return absi(x);

  lx = lgefint(x); xp = int_LSW(x);
  ly = lgefint(y); yp = int_LSW(y);
  if (lx < ly) swapspec(xp,yp,lx,ly);
  /* lx > 2 */
  out = cgetipos(lx);
  outp = int_LSW(out);
  for (i=2;i<ly;i++)
  {
    *outp = (*xp) | (*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  for (   ;i<lx;i++)
  {
    *outp = *xp;
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
  }
  /* If input is normalized, this is not needed */
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

/* bitwise 'xor' of absolute values of two integers */
GEN
ibitxor(GEN x, GEN y)
{
  long lx, ly;
  long *xp, *yp, *outp;
  GEN  out;
  long i;
  if (!signe(x)) return absi(y);
  if (!signe(y)) return absi(x);

  lx = lgefint(x); xp = int_LSW(x);
  ly = lgefint(y); yp = int_LSW(y);
  if (lx < ly) swapspec(xp,yp,lx,ly);
  /* lx > 2 */
  out = cgetipos(lx);
  outp = int_LSW(out);
  for (i=2;i<ly;i++)
  {
    *outp = (*xp) ^ (*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  for (   ;i<lx;i++)
  {
    *outp = *xp;
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
  }
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

/* bitwise 'negimply' of absolute values of two integers */
/* "negimply(x,y)" is ~(x => y) == ~(~x | y) == x & ~y   */
GEN
ibitnegimply(GEN x, GEN y)
{
  long lx, ly, lin;
  long *xp, *yp, *outp;
  GEN out;
  long i;
  if (!signe(x)) return gen_0;
  if (!signe(y)) return absi(x);

  lx = lgefint(x); xp = int_LSW(x);
  ly = lgefint(y); yp = int_LSW(y);
  lin = minss(lx,ly);
  out = cgetipos(lx);
  outp = int_LSW(out);
  for (i=2; i<lin; i++)
  {
    *outp = (*xp) & ~(*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  for (   ;i<lx;i++)
  {
    *outp = *xp;
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
  }
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

#define signs(x,y) (((signe(x) >= 0) << 1) | (signe(y) >= 0))

GEN
gbitor(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT) pari_err(typeer, "bitwise or");
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitor(x,y);
    case 2: /*1,-1*/
      z = ibitnegimply(inegate(y),x);
      break;
    case 1: /*-1,1*/
      z = ibitnegimply(inegate(x),y);
      break;
    case 0: /*-1,-1*/
      z = ibitand(inegate(x),inegate(y));
      break;
    default: return NULL;
  }
  return gerepileuptoint(ltop, inegate(z));
}

GEN
gbitand(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT) pari_err(typeer, "bitwise and");
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitand(x,y);
    case 2: /*1,-1*/
      z = ibitnegimply(x,inegate(y));
      break;
    case 1: /*-1,1*/
      z = ibitnegimply(y,inegate(x));
      break;
    case 0: /*-1,-1*/
      z = inegate(ibitor(inegate(x),inegate(y)));
      break;
    default: return NULL;
  }
  return gerepileuptoint(ltop, z);
}

GEN
gbitxor(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT) pari_err(typeer, "bitwise xor");
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitxor(x,y);
    case 2: /*1,-1*/
      z = inegate(ibitxor(x,inegate(y)));
      break;
    case 1: /*-1,1*/
      z = inegate(ibitxor(inegate(x),y));
      break;
    case 0: /*-1,-1*/
      z = ibitxor(inegate(x),inegate(y));
      break;
    default: return NULL;
  }
  return gerepileuptoint(ltop,z);
}

/* x & ~y */
GEN
gbitnegimply(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT)
    pari_err(typeer, "bitwise negated imply");
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitnegimply(x,y);
    case 2: /*1,-1*/
      z = ibitand(x,inegate(y));
      break;
    case 1: /*-1,1*/
      z = inegate(ibitor(y,inegate(x)));
      break;
    case 0: /*-1,-1*/
      z = ibitnegimply(inegate(y),inegate(x));
      break;
    default: return NULL;
  }
  return gerepileuptoint(ltop,z);
}
