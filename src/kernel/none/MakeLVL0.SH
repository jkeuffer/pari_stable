# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c

kern=$src/kernel/$kernlvl0

cat >> $file << EOT
parilvl0.h: $kern/level0.h 
	cat $kern/level0.h > parilvl0.h
kernel\$(_O): .headers $kern/level0.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o kernel\$(_O) $kern/level0.c
EOT
