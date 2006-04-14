kercom=$src/kernel/sparcv8_micro
cat >> $file << EOT
parilvl0.h: $kercom/level0_common.h $kern0/level0.h
	($cfg/genkernel $kercom/level0_common.h; cat $kern0/level0.h) > parilvl0.h
EOT
