#include <stdio.h>
#   ifdef READLINE_LIBRARY
#     include <readline.h>
#   else
#     include <readline/readline.h>
#   endif
main(){ printf(rl_library_version); }
