#include <sys/stat.h>
#if (!defined(_MSC_VER) && !defined(_WIN32))
#  include <sys/types.h>
#  include <unistd.h>
#endif
main() { struct stat buf; 
  if (stat (".", &buf) || !(buf.st_mode & S_IFDIR)) exit(1);
}
