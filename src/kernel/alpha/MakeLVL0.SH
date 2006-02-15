cat >> $file << EOT
parilvl0.h: $kern0/asm0.h $kern0/asm1.h  
	cat $kern0/asm0.h $kern0/asm1.h > parilvl0.h
EOT
