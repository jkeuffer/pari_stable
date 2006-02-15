# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c
cat >> $file << EOT
L1OBJS=$kern1/tune.h $kern1/int.h $kern1/level1.h
parilvl1.h: \$(L1OBJS) $src/headers/paritune.h
	cat \$(L1OBJS) > parilvl1.h
MP_C=$kern1/mp.c $kern1/cmp.c $kern1/gcdll.c $kern1/ratlift.c $kern1/gcd.c $kern1/invmod.c $kern1/mp_indep.c $kern1/add.c
mp.c: \$(MP_C)
	cat \$(MP_C) > mp.c
mp\$(_O): .headers mp.c
	\$(CC) -c \$(CFLAGS) \$(DLCFLAGS) \$(CPPFLAGS) -o mp\$(_O) mp.c
mpinl\$(_O): .headers parilvl0.h parilvl1.h $kern/level1.c
	\$(CC) -c \$(CFLAGS) \$(DLCFLAGS) \$(CPPFLAGS) -o mpinl\$(_O) $kern/level1.c
EOT
