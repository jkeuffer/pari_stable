#include "pari.h"
#include "anal.h"

GEN   gen_0, gen_1, gen_m1, gen_2;
pari_sp top, bot, avma;
size_t memused = 0;
ulong  DEBUGLEVEL,DEBUGMEM = 0;

void specinit()
{
  long size = 100000L;
  bot = (pari_sp)malloc(size);
  top = avma = bot + size;
  gen_0 = malloc(2);
  gen_0[0] = evaltyp(t_INT)|evallg(2);
  gen_0[1] = evallgefint(2);
  gen_1 = utoipos(1);
  gen_m1= utoineg(1);
  gen_2 = utoipos(2);
}

void gerepileall(pari_sp av, int n, ...){}
void pari_err(long x, ...) { exit (0); }
void pari_warn(long x, ...) { exit (0); }
GEN gmodulcp(GEN x, GEN y) { return NULL; }
GEN gerepileuptoint(pari_sp av, GEN q){ return q; }
void gerepilemanysp(pari_sp av, pari_sp tetpil, GEN* gptr[], int n){}
void gerepilemany(pari_sp av, GEN* gptr[], int n){}
/* used in addrr */
void stackdummy(GEN z, long l) { z[0] = evaltyp(t_VECSMALL) | evallg(l); }

void sorstring(long x)
{
#ifdef LONG_IS_64BIT
  printf("%08x%08x  ", (ulong)x>>32, x & MAXHALFULONG);
#else
  printf("%08lx  ", x);
#endif
}

void _voir(GEN x)
{
  long i, tx = typ(x), lx = (tx == t_INT)? lgefint(x): lg(x);
  sorstring(x[0]);
  for (i=1; i < lx; i++) sorstring(x[i]);
  printf("\n");
}

int main()
{
  GEN x,y,r,z, xr,yr;
  specinit();
  x = utoipos(187654321UL);
  y = utoineg(12345678UL);
  printf("INT: %ld\n", itos(x));
  printf("conv:"); _voir(x);
  printf("+:"); _voir(addii(x,y));
  printf("-:"); _voir(subii(x,y));
  printf("*:"); _voir(mulii(x,y));
  printf("/:"); _voir(dvmdii(x,y, &z));
  printf("rem:"); _voir(z);
  printf("pow:\n");
  z = mulii(x,x); _voir(z);
  z = mulii(z,z); _voir(z);
  z = mulii(z,z); _voir(z);
  z = mulii(z,z); _voir(z);
  z = mulii(z,z); _voir(z);
  printf("invmod:"); invmod(y,z,&r); _voir(r);
  xr = itor(x, DEFAULTPREC);
  yr = itor(y, DEFAULTPREC);
  printf("\nREAL: %f\n", rtodbl(xr));
  printf("conv1:"); _voir(xr);
  printf("conv2:"); _voir(dbltor(rtodbl(xr)));
  printf("+:"); _voir(addrr(xr,yr));
  printf("-:"); _voir(subrr(xr,yr));
  printf("*:"); _voir(mulrr(xr,yr));
  printf("/:"); _voir(divrr(xr,yr));
  printf("gcc bug?:"); _voir(divrs(dbltor(3.),2));
  return 0;
}
