# Level 0 kernel is "asm extern"
# Level 1 kernel is the C generic one
level0=$src/kernel/none/asm0.h
kernel1=$src/kernel/$kernlvl0/level0.S
if test "$osname" = "nextstep" -o "$osname" = "linux" -o "$gnuas" = "yes";
then
cat >> $file << EOT
kernel1.s: $kernel1
	\$(CPP) $KERNELCPPFLAGS $kernel1 > \$@
EOT
kernel1=kernel1.s
fi

cat >> $file << EOT
parilvl0.h: $level0 
	cat $level0 > parilvl0.h
kernel\$(_O):  $kernel1
	\$(AS) \$(ASFLAGS) -o \$@ $kernel1

EOT
