# Level 0 kernel is "asm extern"
# Level 1 kernel is the C generic one

kern=$src/kernel/$asmarch
kerngen=$src/kernel/none

cat >> $file << EOT
pariinl.h: $kern/asm0.h $kerngen/level1.h
	cat $kern/asm0.h $kern/asm1.h $kerngen/level1.h > \$@
kernel.o: $kern/level0.s
	\$(AS) \$(ASFLAGS) -o kernel.o $kern/level0.s
invert_word.o: $kern/invert_word.s
	\$(AS) \$(ASFLAGS) -o invert_word.o $kern/invert_word.s
mp.o: .headers $kerngen/mp.c 
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mp.o $kerngen/mp.c
mpinl.o: .headers $kerngen/level1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl.o $kerngen/level1.c
EOT
