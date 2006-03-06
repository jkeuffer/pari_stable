cat >> $file << EOT

KERN0_H=$kern0/addll.h $kern0/mulll.h $kern0/bfffo.h $kern0/divll.h

parilvl0.h: \$(KERN0_H)
	cat \$(KERN0_H) > parilvl0.h
EOT
