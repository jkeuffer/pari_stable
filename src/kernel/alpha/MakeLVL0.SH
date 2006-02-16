cat >> $file << EOT
parilvl0.h: $kern0/asm0.h $knone/bfffo.h $knone/divll.h  
	cat $kern0/asm0.h $knone/bfffo.h $knone/divll.h > parilvl0.h
EOT
