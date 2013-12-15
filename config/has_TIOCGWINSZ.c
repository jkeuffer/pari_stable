#include <unistd.h>
#include <sys/types.h>
#ifdef __sun
#  include <sys/termios.h>
#endif
#include <sys/ioctl.h>
int main() { int x = TIOCGWINSZ; return x; }
