# Level 0 kernel is "asm inline" if gcc and "asm extern" if not

level0=$src/kernel/$kernlvl0
none=$src/kernel/none

cat >> $file << EOT
parilvl0.h: $level0/asm0.h 
	cat $level0/asm0.h > parilvl0.h
kernel\$(_O): $none/level0.h pariinl.h
	\$(CC) -c \$(CFLAGS) \$(DLCFLAGS) \$(CPPFLAGS) -o kernel\$(_O) $none/level0.c
EOT

