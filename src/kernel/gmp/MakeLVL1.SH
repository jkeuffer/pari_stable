# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c

kern=$src/kernel/$kernlvl1
knone=$src/kernel/none

cat >> $file << EOT
parilvl1.h: $kern/int.h $knone/level1.h
	cat $kern/int.h $knone/level1.h > parilvl1.h
mp\$(_O): .headers $kern/mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mp\$(_O) $kern/mp.c
mpinl\$(_O): .headers $knone/level1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl\$(_O) $knone/level1.c
EOT
