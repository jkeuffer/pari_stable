#include <pari/pari.h> /* Include PARI headers */

#include <omp.h>       /* Include OpenMP headers */

int
main(void)
{
  GEN M,N1,N2, F1,F2,D;
  struct pari_thread pth1, pth2, pth3;
  /* Initialise the main PARI stack and global objects (gen_0, etc.) */
  pari_init(4000000,500000);
  /* Compute in the main PARI stack */
  N1 = addis(int2n(256), 1); /* 2^256 + 1 */
  N2 = subis(int2n(193), 1); /* 2^193 - 1 */
  M = mathilbert(80);
  /*Allocate pari thread structures */
  pari_thread_alloc(&pth1,4000000,NULL);
  pari_thread_alloc(&pth2,4000000,NULL);
  pari_thread_alloc(&pth3,4000000,NULL);
#pragma omp parallel num_threads(4)
  {
    switch(omp_get_thread_num())
    {
      case 1:
        (void)pari_thread_start(&pth1);
        F1 = factor(N1);
        break; 
      case 2:
        (void)pari_thread_start(&pth2);
        F2 = factor(N2);
        break; 
      case 3:
        (void)pari_thread_start(&pth3);
        D = det(M);
        break; 
    }
  }
  pari_printf("F1=%Ps\nF2=%Ps\nlog(D)=%Ps\n", F1, F2, glog(D,3));
  pari_thread_free(&pth1);
  pari_thread_free(&pth2);
  pari_thread_free(&pth3);
  return 0;
}
