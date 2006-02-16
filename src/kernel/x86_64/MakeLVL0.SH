# Level 0 kernel is "asm inline" if gcc and "asm extern" if not
cat >> $file << EOT
parilvl0.h: $kern0/asm0.h 
	cat $kern0/asm0.h > parilvl0.h
EOT

