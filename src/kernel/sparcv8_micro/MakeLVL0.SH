# For NextStep
#   We don't accept "asm inline" since it does not work (Ptitboul)
if test "$osname" = "nextstep" 
then
  level0=$src/kernel/none/asm0.h
else
  level0="$src/kernel/sparcv8_micro/level0_common.h $src/kernel/$kernlvl0/level0.h"
fi
level0="$src/kernel/none/bfffo.h $level0"

cat >> $file << EOT
parilvl0.h: $level0
	cat $level0 > parilvl0.h
EOT
