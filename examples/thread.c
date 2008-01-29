#include <pari/pari.h> /* Include PARI headers */

#include <pthread.h>   /* Include POSIX threads headers */

void *
mydet(void *arg)
{
  GEN F, M = (GEN)arg;

  pari_thread_init(8000000); /* This thread uses a local PARI stack of 8MB */
  /* Compute det(M) using local stack, then clone before freeing the stack */
  F = gclone( det(M) );
  pari_thread_close();     /* Free the local PARI stack */
  pthread_exit((void*)F);  /* End the thread and return F */
  return NULL;             /* Not reached */
}

void *
myfactor(void *arg)  /* same principles */
{
  GEN F, N = (GEN)arg;

  pari_thread_init(4000000);
  F = gclone( factor(N) );
  pari_thread_close();
  pthread_exit((void*)F);
  return NULL;
}

int
main(void)
{
  GEN M,N1,N2, F1,F2,D;
  pthread_t th1, th2, th3; /* Allocate POSIX-thread variables */

  /* Initialise the main PARI stack and global objects (gen_0, etc.) */
  pari_init(4000000,500000);
  /* Compute in the main PARI stack */
  N1 = addis(int2n(256), 1); /* 2^256 + 1 */
  N2 = subis(int2n(193), 1); /* 2^193 - 1 */
  M = mathilbert(80);
  /* pthread_create and pthread_join are standard POSIX-thread functions
   * to start and get the result of threads. */
  pthread_create(&th1,NULL, &myfactor, (void*)N1); /* Start threads */
  pthread_create(&th2,NULL, &myfactor, (void*)N2);
  pthread_create(&th3,NULL, &mydet,    (void*)M);
  pthread_join(th1,(void*)&F1); /* Wait for termination, get the results */
  pthread_join(th2,(void*)&F2);
  pthread_join(th3,(void*)&D);
  pariprintf("F1=%Zs\nF2=%Zs\nlog(D)=%Zs\n", F1, F2, glog(D,3));
  return 0;
}
