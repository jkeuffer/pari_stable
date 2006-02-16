# For SunOS
#   If __GNUC__, most level0 functions are "asm inline"
#   If not, they are "asm extern"
# For NextStep
#   We don't accept "asm inline" since it does not work (Ptitboul)
kercom=$src/kernel/sparcv8_micro

if test "$osname" = "nextstep" 
then
  level0=$src/kernel/none/asm0.h
else
  level0="$kercom/level0_common.h $knone/divll.h"
fi
level0="$knone/bfffo.h $level0"

cat >> $file << EOT
parilvl0.h: $level0
	cat $level0 > parilvl0.h
EOT
