# Level 0 kernel is the C generic one.

# Level 1 kernel is in assembly (mp.s), except the new functions that
# were only written in C (karatsuba and others).
# The assembly file is compiled in mpasm.o

kernel="$kernel mpasm"

cat >> $file << EOT
pariinl.h: $src/kernel/none/level0.h $src/kernel/none/level1.h
	cat $src/kernel/none/level0.h $src/kernel/none/level1.h > \$@
kernel.o: .headers $src/kernel/none/level0.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o kernel.o $src/kernel/none/level0.c
mpasm.o: $src/kernel/m68k/mp.s
	\$(AS) \$(ASFLAGS) -o mpasm.o $src/kernel/m68k/mp.s
mp.o: .headers $src/kernel/none/mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mp.o $src/kernel/none/mp.c
mpinl.o: .headers $src/kernel/none/level1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl.o $src/kernel/none/level1.c

EOT
