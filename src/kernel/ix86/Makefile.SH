# Level 0 kernel is "asm inline" if gcc and "asm extern" if not
# Level 1 kernel is the C generic one

cat >> $file << EOT
pariinl.h: $src/kernel/ix86/level0.h $src/kernel/none/level1.h
	cat $src/kernel/ix86/level0.h $src/kernel/none/level1.h > \$@
level0.s: ../src/kernel/ix86/l0asm.c ../src/kernel/ix86/l0asm.h
	\$(CPP) ../src/kernel/ix86/l0asm.c | sed -e '/^#/d' -e '/^ *#line/d' -e 's/%  */%/g' > level0.s
kernel.o:  level0.s
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o kernel.o level0.s
mp.o: .headers $src/kernel/none/mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mp.o $src/kernel/none/mp.c
mpinl.o: .headers $src/kernel/none/level1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl.o $src/kernel/none/level1.c

EOT
