# Level 0 kernel is "asm extern"
kern=$src/kernel/$kernlvl0
knone=$src/kernel/none

cat >> $file << EOT
parilvl0.h: $kern/level0.h $knone/bfffo.h $knone/divll.h
	cat $kern/level0.h $knone/bfffo.h $knone/divll.h > parilvl0.h
kernel\$(_O): .headers $knone/level0.h
	\$(CC) -c \$(CFLAGS) \$(DLCFLAGS) \$(CPPFLAGS) -o kernel\$(_O) $knone/level0.c

EOT
