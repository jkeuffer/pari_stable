#include <unistd.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <termios.h>
int main() { int x = TIOCGWINSZ; return x; }
