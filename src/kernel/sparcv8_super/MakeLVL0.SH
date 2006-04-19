cat >> $file << EOT
parilvl0.h: $src/kernel/sparcv8_micro/level0_common.h $knone/divll.h
	$cfg/genkernel $src/kernel/sparcv8_micro/level0_common.h $kern0/asm0.h > parilvl0.h
EOT
