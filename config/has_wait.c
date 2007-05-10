#include <stdio.h>
#include <sys/wait.h>
main(){
#ifdef WNOHANG
  while (wait3(NULL, WNOHANG, NULL) > 0);
#else
  wait(NULL);
#endif
}
