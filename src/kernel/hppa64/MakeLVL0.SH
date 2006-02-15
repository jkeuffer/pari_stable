# Level 0 kernel is "asm extern"
cat >> $file << EOT
parilvl0.h: $kern0/level0.h $knone/bfffo.h $knone/divll.h
	cat $kern0/level0.h $knone/bfffo.h $knone/divll.h > parilvl0.h
EOT
