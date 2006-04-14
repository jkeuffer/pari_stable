cat >> $file << EOT
parilvl0.h: $src/kernel/sparcv8_micro/level0_common.h $knone/divll.h
	($cfg/genkernel sparcv8_micro/level0_common.h; cat $knone/divll.h) > parilvl0.h
EOT
