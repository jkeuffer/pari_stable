# For SunOS
#   If __GNUC__, most level0 functions are "asm inline"
#   If not, they are "asm extern"
#   The object kernel.o (resp. kernel2.o) contains entries for the functions
#   that can (resp. cannot) be inline.
#   Problem: "divll" uses "overflow", so kernel2.o is not the same when
#   compiled with gcc or with cc. We should try to find a workaround.
# For NextStep or Linux
#   We don't accept "asm inline" since it does not work (Ptitboul)

if test -z "$__gnuc__" -o "$osname" = "nextstep" -o "$osname" = "linux"; then
  kernel="$kernel kernel2"
  if test "$gnuas" = "yes"; then do_cpp=yes; fi
fi

ker=$src/kernel/sparcv8
kernel1=$ker/level0_$asmarch.S
kernel2=$ker/level0.S
level0=$ker/level0.h
if test "$osname" = "nextstep" -o "$osname" = "linux" -o "$do_cpp" = "yes"
then
cat >> $file << EOT
kernel1.s: $kernel1
	\$(CPP) $KERNELCPPFLAGS $kernel1 > \$@
kernel2.s: $kernel2
	\$(CPP) $KERNELCPPFLAGS $kernel2 > \$@
EOT
kernel1=kernel1.s
kernel2=kernel2.s
level0=$src/kernel/none/asm0.h
fi
level1=$src/kernel/none/level1.h

cat >> $file << EOT
pariinl.h: $level0 $level1
	cat $level0 $level1 > \$@
kernel.o:  $kernel1
	\$(AS) \$(ASFLAGS) -o \$@ $kernel1
kernel2.o: $kernel2
	\$(AS) \$(ASFLAGS) -o \$@ $kernel2
# Level 1 kernel is the generic one
mp.o: .headers $src/kernel/none/mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o \$@ $src/kernel/none/mp.c
mpinl.o: .headers $level1
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o \$@ $src/kernel/none/level1.c

EOT
