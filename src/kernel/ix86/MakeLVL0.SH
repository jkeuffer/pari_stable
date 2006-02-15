# Level 0 kernel is "asm inline" if gcc and "asm extern" if not

level0=$src/kernel/$kernlvl0

cat >> $file << EOT
parilvl0.h: $level0/level0.h 
	cat $level0/level0.h > parilvl0.h
EOT
