file=Makefile
echo "Extracting $file"
rm -f $file

case "$status" in
  alpha|beta|kernel) suf_status=".$status";;
  *) suf_status=;;
esac

filename=pari-$version.$patch$suf_status
tarfile=$filename.tar
ztarfile=$filename.tgz

dbgobjdir=`echo "$objdir" | sed -e 's/\.[dbgprf]*$//'`
dbgobjdir=$dbgobjdir.dbg

dosversion=`echo $version|sed -e 's/\.//g'`
dosversion="_$dosversion$patch"

# MAINTAINER ONLY: for automated tests in Bordeaux
bxmachine=megrez.math.u-bordeaux.fr
bxgzip=/usr/local/bin/gzip

cat > $file << EOT
# This file was created by Configure. All changes made will be lost
# next time Configure is run.
#
SHELL = $make_sh
RM = /bin/rm -f

dft target::
	@echo "Possible targets are:"
	@echo "	gp			 Compilation"
	@echo "	bench, test-compat       Compilation and test"
	@echo "	dobench                	 Test only"
	@echo "	doc			 Documentation"
	@echo "	install			 Installation"
	@echo "	clean, cleantest         Cleaning up"
	@echo "For pari maintainers..."
	@echo "	all			Compile gp-[sta|dyn] and lib-[sta|dyn]"
	@echo "	gp.dbg	                Compile gp binary suitable for debugging"
	@echo "	distrib			Create a new distribution"
	@echo "	ctags			Generate VI/VIM tags file in ./src"
	@echo "	etags			Generate Emacs  tags file in ./src"
	@echo "	tune	                Generate tuning utility"

gp all bench test-kernel test-compat test-graphic install cleanobj cleantest install-bin install-doc install-lib-sta install-bin-sta dobench tune::
	cd \`$config_dir/objdir\`; \$(MAKE) \$@

dbg gp.dbg::
	cd \`$config_dir/objdir\`.dbg; \$(MAKE) gp

prf gp.prf::
	cd \`$config_dir/objdir\`.prf; \$(MAKE) gp

doc docps docpdf gpman cleandoc::
	cd doc; \$(MAKE) \$@

clean:: cleandoc cleanobj

setdir::
	@dir=pari-$version.$patch$suf_status; if test -d \$\$dir; then \\
	   echo "Remove \$\$dir before building a new release"; exit 1;\\
	fi;\\
	mkdir \$\$dir; mv $tarfile \$\$dir; \\
	cd \$\$dir; tar xf $tarfile; \$(RM) $tarfile; cd ..; \\
	tar cf $tarfile \$\$dir; \\
	\$(RM) -r \$\$dir

tar:
	\$(RM) $ztarfile
	tar cf $tarfile \`$config_dir/tar_distrib\` $config_dir/MANIFEST

distrib: tar setdir
	gzip $tarfile
	mv $tarfile.gz $ztarfile

dosdistrib: gpman
	-zip -kr GPB${dosversion}.ZIP GP.EXE README README.DOS ../EMX/README.DOC ../RSX/README.TXT
	-zip -k GPD${dosversion}.ZIP doc/*.tex doc/gphelp doc/gp.man examples misc/gprc* misc/gpalias

etags:
	cd src; sh make_emacs_tags

ctags:
	src/make_vi_tags $TOP/src

EOT
