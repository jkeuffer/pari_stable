#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
main(){ waitpid(-1,NULL,0); }
