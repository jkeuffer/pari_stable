# For SunOS
#   If __GNUC__, most level0 functions are "asm inline"
#   If not, they are "asm extern"
#   The object kernel.o (resp. kernel2.o) contains entries for the functions
#   that can (resp. cannot) be inline.
#   Problem: 'divll' uses 'hiremainder', so kernel2.o is not the same when
#   compiled with gcc or with cc. We should try to find a workaround.
# For NextStep or Linux
#   We don't accept "asm inline" since it does not work (Ptitboul)
ker=$src/kernel/sparcv8
kernel1=$ker/level0_$kernlvl0.S
kernel2=$ker/level0.S

if test "$osname" = "nextstep" -o "$osname" = "linux"
then
  level0=$src/kernel/none/asm0.h
else
  level0=$ker/level0.h
fi

if test "$osname" = "nextstep" -o "$osname" = "linux" -o "$gnuas" = "yes"
then
  cat >> $file << EOT
kernel1.s: $kernel1
	\$(CPP) $KERNELCPPFLAGS $kernel1 > \$@
kernel2.s: $kernel2
	\$(CPP) $KERNELCPPFLAGS $kernel2 > \$@
EOT
  kernel1=kernel1.s
  kernel2=kernel2.s
fi

cat >> $file << EOT
parilvl0.h: $level0 
	cat $level0 > parilvl0.h
kernel\$(_O):  $kernel1
	\$(AS) \$(ASFLAGS) -o \$@ $kernel1
kernel2\$(_O): $kernel2
	\$(AS) \$(ASFLAGS) -o \$@ $kernel2

EOT
