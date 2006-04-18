cat >> $file << EOT
parilvl0.h: $src/kernel/sparcv8_micro/level0_common.h $knone/divll.h
	$cfg/genkernel sparcv8_micro/level0_common.h asm0.h > parilvl0.h
EOT
