# Level 0 kernel is "asm inline" if gcc and "asm extern" if not

level0=$src/kernel/$kernlvl0

cat >> $file << EOT
parilvl0.h: $level0/level0.h 
	cat $level0/level0.h > parilvl0.h
level0.s: $level0/l0asm.c $level0/l0asm.h
	\$(CPP) $level0/l0asm.c |\
	  sed -e '/^#/d' -e '/^ *#line/d' -e 's/%  */%/g' \
	      -e 's/\. /./g' -e 's/ :/:/g' > level0.s
kernel\$(_O):  level0.s
	\$(CC) -c \$(CFLAGS) \$(CPPFLAGS) -o kernel\$(_O) level0.s

EOT
