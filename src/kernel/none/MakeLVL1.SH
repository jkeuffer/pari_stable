# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c

kern=$src/kernel/$kernlvl1

cat >> $file << EOT
parilvl1.h: $kern/int.h $kern/level1.h
	cat $kern/int.h $kern/level1.h > parilvl1.h
mp.c: $kern/mp.c $kern/gcdll.c $kern/ratlift.c $kern/gcd.c
	cat $kern/mp.c $kern/gcdll.c $kern/ratlift.c $kern/gcd.c > mp.c
mp\$(_O): .headers mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mp\$(_O) mp.c
mpinl\$(_O): .headers parilvl1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl\$(_O) $kern/level1.c
EOT
