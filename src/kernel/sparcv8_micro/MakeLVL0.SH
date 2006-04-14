cat >> $file << EOT
parilvl0.h: $src/kernel/sparcv8_micro/level0_common.h $kern0/level0.h
	($cfg/genkernel sparcv8_micro/level0_common.h;\
	 $cfg/genkernel $kernlvl0/level0.h) > parilvl0.h
EOT
