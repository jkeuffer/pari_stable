#include <stdio.h>
#include <sys/times.h>
main(){ struct tms t; printf("%d", times(&t)); }

