# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c

kern=$src/kernel/$kernlvl1
knone=$src/kernel/none

cat >> $file << EOT
parilvl1.h: $kern/int.h $knone/level1.h
	cat $kern/int.h $knone/level1.h > parilvl1.h
MP_C= $kern/mp.c $knone/gcdll.c $knone/ratlift.c $knone/invmod.c $kern/gcd.c $knone/mp_indep.c $knone/add.c
mp.c: \$(MP_C)
	cat \$(MP_C) > mp.c
mp\$(_O): .headers mp.c
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) \$(GMPINCLUDE) -o mp\$(_O) mp.c
mpinl\$(_O): .headers parilvl1.h
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o mpinl\$(_O) $knone/level1.c
EOT
