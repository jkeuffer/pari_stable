# Functions that can be inlined are externally defined too
# This is done with level0.c and level1.c
cat >> $file << EOT
parilvl0.h: $kern0/level0.h $kern0/bfffo.h $kern0/divll.h
	cat $kern0/level0.h $kern0/bfffo.h $kern0/divll.h > parilvl0.h
EOT
