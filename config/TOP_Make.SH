file=Makefile
echo "Extracting $file"
rm -f $file

file=Makefile.$objdir
rm -f $file

case "$status" in
  alpha|beta|kernel) suf_status=".$status";;
  *) suf_status=;;
esac

tar="/bin/tar"
filename=pari-$version.$patch$suf_status
tarfile=$filename.tar
ztarfile=$filename.tgz
case "`$tar 2>&1`" in
  *"--help"*) inc="-T";; # GNU
           *) inc="-I";; # Solaris
esac
tarinc="$inc $TOP/MANIFEST"

dosversion=`echo $version|sed -e 's/\.//g'`
dosversion="_$dosversion$patch"

# MAINTAINER ONLY: for automated tests in Bordeaux
bxmachine=megrez.math.u-bordeaux.fr
gzip=/usr/local/bin/gzip

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
	@echo "	distrib			Create a new distribution"
	@echo "	ctags			Generate VI/VIM tags file in ./src"
	@echo "	etags			Generate Emacs  tags file in ./src"

gp all bench test-compat test-graphic install clean cleantest install-bin install-doc install-lib-sta install-bin-sta dobench::
	cd $objdir; \$(MAKE) \$@

doc docps gpman::
	cd doc; \$(MAKE) \$@

RCS::
	ci -f -l -r\$\${REVISION:-$rcsrevision} -m"." \`find src -name \\*.[chs] -type f -print\`

setdir::
	@dir=pari-$version.$patch$suf_status; if test -d \$\$dir; then \\
	   echo "Remove \$\$dir before building a new release"; exit 1;\\
	fi;\\
	mkdir \$\$dir; mv $tarfile \$\$dir; \\
	cd \$\$dir; tar xf $tarfile; \$(RM) $tarfile; cd ..; \\
	tar cf $tarfile \$\$dir; \\
	rm -r \$\$dir

tar:
	rm -f $tarfile.gz
	$tar cf $tarfile $tarinc

distrib: tar setdir
	gzip $tarfile
	mv $tarfile.gz $ztarfile

uu: distrib
	uuencode $tarfile.gz $tarfile.gz > pari.uu

dosdistrib: docps gpman
	-zip -kr GPB${dosversion}.ZIP GP.EXE README README.DOS examples ../EMX/README.DOC ../RSX/README.TXT
	-zip -k GPD${dosversion}.ZIP doc/users.ps doc/refcard.ps doc/tutorial.ps
	-zip -k GPM${dosversion}.ZIP doc/*.tex doc/gphelp doc/gp.man

etags:
	cd src; sh make_emacs_tags

ctags:
	src/make_vi_tags $TOP/src

benchbx: $ztarfile
	rcp $ztarfile pari@$bxmachine:PARINEW
	rsh $bxmachine -l pari "cd PARINEW; $gzip -dc $ztarfile|tar xf -; ./makeall $filename"
EOT

$ln_s $file Makefile
