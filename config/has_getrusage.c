#define _INCLUDE_POSIX_SOURCE
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
main(){ struct rusage a; printf("%d",getrusage(0,&a));}
