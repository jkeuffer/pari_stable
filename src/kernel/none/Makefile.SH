# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c

cat >> $file << EOT
pariinl.h: $src/kernel/none/level0.h $src/kernel/none/level1.h
	cat $src/kernel/none/level0.h $src/kernel/none/level1.h > \$@
kernel.o: .headers $src/kernel/none/level0.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o kernel.o $src/kernel/none/level0.c
mp.o: .headers $src/kernel/none/mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mp.o $src/kernel/none/mp.c
mpinl.o: .headers $src/kernel/none/level1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl.o $src/kernel/none/level1.c

EOT
