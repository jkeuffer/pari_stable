#include <stdio.h>
#include <gmp.h>
f() { mpn_gcdext(NULL,NULL, NULL, NULL, 0, NULL, 0); }
main(){ printf("%s", gmp_version); }
