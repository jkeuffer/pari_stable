# Level 0 kernel is "asm extern"

$kern=$src/kernel/$kernlvl0

cat >> $file << EOT
parilvl0.h: $src/kernel/none/asm0.h 
	cat $src/kernel/none/asm0.h > parilvl0.h
kernel\$(_O):  $kern/level0.s
	\$(AS) \$(ASFLAGS) -o kernel\$(_O) $kern/level0.s

EOT
