#include <pari.h>
#include <anal.h>

GEN   gzero, gun, gdeux;
ulong top, bot, avma, memused = 0;
long  DEBUGLEVEL,DEBUGMEM = 0;

void specinit()
{
  long size = 100000L;
  bot = (long)malloc(size);
  top = avma = bot + size;
  gzero = malloc(2);
  gzero[0] = evaltyp(t_INT)|evallg(2);
  gzero[1] = evallgefint(2);
  gun   = stoi(1);
  gdeux = stoi(2);
}

void pari_err(long x, ...) { exit (0); }
GEN gerepileuptoint(long av, GEN q){ return q; }
void gerepilemanysp(long av, long tetpil, GEN* gptr[], long n){}
void gerepilemany(long av, GEN* gptr[], long n){}

void sorstring(char* b, long x)
{
#ifdef LONG_IS_64BIT
  printf(b,(ulong)x>>32,x & MAXHALFULONG);
#else
  printf(b,x);
#endif
}

void _voir(GEN x)
{
  long tx = typ(x), lx = lg(x),i;
  sorstring(VOIR_STRING2,x[0]);
  if (tx==t_INT) lx = lgefint(x);
  for (i=1; i < lx; i++) sorstring(VOIR_STRING2,x[i]);
  printf("\n");
}

int main()
{
  GEN x,y,r,z, xr,yr;
  specinit();
  x = stoi(187654321L);
  y = stoi(-12345678L);
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
  xr = cgetr(DEFAULTPREC); affir(x, xr);
  yr = cgetr(DEFAULTPREC); affir(y, yr);
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
