cat >> $file << EOT
parilvl0.h: $knone/addll.h $kern0/asm0.h $knone/divll.h  
	cat $knone/addll.h $kern0/asm0.h $knone/divll.h > parilvl0.h
EOT
