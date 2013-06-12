#include <unistd.h>
#include <sys/types.h>
#include <sys/termios.h>
#include <sys/ioctl.h>
int main() { int x = TIOCGWINSZ; return x; }
