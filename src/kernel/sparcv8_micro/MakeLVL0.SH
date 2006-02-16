kercom=$src/kernel/sparcv8_micro

if test "$osname" = "nextstep" 
then
# don't accept "asm inline" since it does not work (Ptitboul, around 1996)
# FIXME: is that still true ?
  level0=$knone/asm0.h
else
  level0="$kercom/level0_common.h $kern0/level0.h"
fi
level0="$knone/bfffo.h $level0"

cat >> $file << EOT
parilvl0.h: $level0
	cat $level0 > parilvl0.h
EOT
