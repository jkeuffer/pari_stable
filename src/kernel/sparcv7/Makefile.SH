# Level 0 kernel is "asm extern"
# Level 1 kernel is the C generic one
level0=$src/kernel/none/asm0.h
level1=$src/kernel/none/level1.h
kernel1=$src/kernel/$asmarch/level0.S
if test "$osname" = "nextstep" -o "$osname" = "linux" -o "$gnuas" = "yes";
then
cat >> $file << EOT
kernel1.s: $kernel1
	\$(CPP) $KERNELCPPFLAGS $kernel1 > \$@
EOT
kernel1=kernel1.s
fi

cat >> $file << EOT
pariinl.h: $level0 $level1
	cat $level0 $level1 > \$@
kernel.o:  $kernel1
	\$(AS) \$(ASFLAGS) -o \$@ $kernel1
mp.o: .headers $src/kernel/none/mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o \$@ $src/kernel/none/mp.c
mpinl.o: .headers $level1 
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o \$@ $src/kernel/none/level1.c

EOT
