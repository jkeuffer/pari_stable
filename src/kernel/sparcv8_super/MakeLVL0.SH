# For SunOS
#   If __GNUC__, most level0 functions are "asm inline"
#   If not, they are "asm extern"
# For NextStep or Linux
#   We don't accept "asm inline" since it does not work (Ptitboul)
kercom=$src/kernel/sparcv8_micro
ker=$src/kernel/$kernlvl0

if test "$osname" = "nextstep" -o "$osname" = "linux"
then
  level0=$src/kernel/none/asm0.h
else
  level0="$kercom/level0_common.h $ker/level0.h"
fi

cat >> $file << EOT
kernel0.s: $kercom/level0_common.S $ker/level0.S
	cat $kercom/level0_common.S $ker/level0.S > level0.S
	\$(CPP) $KERNELCPPFLAGS level0.S |\
	   sed -e '/^#/d' -e '/^ *#line/d' -e 's/%  */%/g' > \$@

parilvl0.h: $level0
	cat $level0 > parilvl0.h

kernel\$(_O): kernel0.s
	\$(AS) \$(ASFLAGS) -o \$@ \$<

EOT
