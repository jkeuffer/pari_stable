kercom=$src/kernel/sparcv8_micro
cat >> $file << EOT
parilvl0.h: $kercom/level0_common.h $knone/divll.h
	($cfg/genkernel $kercom/level0_common.h; cat $knone/divll.h) > parilvl0.h
EOT
