cat >> $file << EOT
L1OBJS=$kern1/int.h $knone/level1.h
parilvl1.h: \$(L1OBJS) $src/headers/paritune.h
	if test -r ./tune.h; then d=.; else d=$kern1; fi;\
          cat \$\$d/tune.h \$(L1OBJS) > parilvl1.h
MP_C=$kern1/mp.c $knone/cmp.c $knone/gcdll.c $knone/ratlift.c\
  $knone/invmod.c $kern1/gcd.c $kern1/gcdext.c $knone/mp_indep.c $knone/add.c
mp.c: \$(MP_C)
	cat \$(MP_C) > mp.c
mp\$(_O): .headers mp.c
	\$(CC) -c \$(CFLAGS) \$(KERNELCFLAGS) \$(DLCFLAGS) \$(CPPFLAGS) -o mp\$(_O) mp.c
EOT
