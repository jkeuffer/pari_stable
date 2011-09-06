file=Makefile
echo "Extracting $file"
rm -f $file

dbgobjdir=`echo "$objdir" | sed -e 's/\.[dbgprf]*$//'`
dbgobjdir=$dbgobjdir.dbg

dosversion=`echo $version|sed -e 's/\.//g'`
dosversion="_$dosversion$patch"
__status__=$status
case "$status" in
  development*) __status__='snapshot';;
esac

cat > $file << EOT
# This file was created by Configure. All changes made will be lost
# next time Configure is run.
#
SHELL = $make_sh
VERS = pari-$version.$patch $__status__
TAG=release-$VersionMajor-$VersionMinor-$patch

dft target::
	@echo "Possible targets are:"
	@echo "	all             	 Compilation + Documentation"
	@echo "	gp			 Compilation"
	@echo "	bench                    Compilation + quick test"
	@echo "	dobench                	 Test only"
	@echo "	doc			 Documentation"
	@echo "	install			 Installation"
	@echo "	clean, cleantest         Clean up"
	@echo "For pari maintainers..."
	@echo "	dbg	                Compile gp binary suitable for debugging"
	@echo "	prf	                Compile gp binary suitable for profiling"
	@echo "	distrib,alpha,beta,release  Create a new distribution"
	@echo "	snapshot                Create a snapshot"
	@echo "	ctags			Generate VI/VIM tags file in ./src"
	@echo "	etags			Generate Emacs  tags file in ./src"
	@echo "	tune	                Generate tuning utility"
	@echo "	test-all	        Thorough regression tests (slow)"

all::
	@\$(MAKE) gp
	@-cd doc && \$(MAKE) doc

gp bench test-kernel test-all $top_test_extra $top_dotest_extra install cleanall cleanobj cleantest install-bin install-doc install-docpdf install-data install-lib-sta install-bin-sta dobench dyntest-all statest-all tune::
	@dir=\`config/objdir\`; echo "Making \$@ in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) \$@

dbg gp.dbg::
	@dir=\`config/objdir\`.dbg; echo "Making gp in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -g first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) gp

prf gp.prf::
	@dir=\`config/objdir\`.prf; echo "Making gp in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -pg first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) gp

doc docps docpdf gpman cleandoc::
	cd doc && \$(MAKE) \$@

clean:: cleandoc cleanall

distrib:
	$config_dir/settar \$(VERS) $__status__

alpha:
	$config_dir/settar \$(VERS) alpha
beta:
	$config_dir/settar \$(VERS) beta
release:
	$config_dir/settar \$(VERS) released
snapshot:
	$config_dir/settar \$(VERS) snapshot

dosdistrib: gpman
	-zip -kr GPB${dosversion}.ZIP GP.EXE README README.DOS ../EMX/README.DOC ../RSX/README.TXT
	-zip -k GPD${dosversion}.ZIP doc/*.tex doc/gphelp doc/gp.man examples misc/gprc* misc/gpalias

etags:
	cd src; sh ../config/make_emacs_tags

ctags:
	config/make_vi_tags "$TOP/src"

checkspaces:
	config/checkspaces

EOT
