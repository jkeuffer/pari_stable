kern=$src/kernel/$kernlvl0

cat >> $file << EOT
parilvl0.h: $kern/asm0.h $kern/asm1.h  
	cat $kern/asm0.h $kern/asm1.h > parilvl0.h
kernel\$(_O): $kern/level0.s
	\$(AS) \$(ASFLAGS) -o kernel\$(_O) $kern/level0.s

EOT
