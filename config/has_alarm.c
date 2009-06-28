#include <unistd.h>

char (*f)() = alarm;
int main(){ return f != alarm; }
