# Path to directories
cfg=../$config_dir
data=../$data_dir
doc=../$doc_dir
desc=../$desc_dir
ex=../$examples_dir
misc=../$misc_dir
src=../$src_dir

cat > doc/Makefile << EOT
#  This file was created by Configure. Any change made to it will be lost
#  next time configure is run.
#
SHELL = $make_sh
PERL  = $perl

DESC          = pari.desc
MACROS= paricfg.tex parimacro.tex
USERS_TEX=\$(MACROS) appa.tex users.tex usersch1.tex usersch2.tex usersch3.tex
PARI_TEX=\$(MACROS) libpari.tex appb.tex appd.tex usersch4.tex usersch5.tex usersch6.tex usersch7.tex

doc all: develop.dvi libpari.dvi users.dvi refcard.ps tutorial.dvi
docps: develop.ps libpari.ps refcard.ps tutorial.ps users.ps INSTALL.ps
docpdf: develop.pdf libpari.pdf users.pdf tutorial.pdf refcard.pdf INSTALL.pdf

.SUFFIXES: .tex .ipf .pod .inf .dumbpod .3 .html

paricfg.tex: paricfg.tex.in
	sed -e 's/@version@/$version.$patch/'\\
	    -e 's!@includedir@!$includedir!'\\
	    -e 's!@libdir@!$libdir!'\\
	    -e 's!@datadir@!$datadir!' paricfg.tex.in > \$@

%.pdf: %.tex \$(MACROS)
	pdftex \$<

%.dvi: %.tex \$(MACROS)
	tex \$<

libpari.pdf: \$(PARI_TEX) \$(MACROS)
	-rm -f libpari.std
	pdftex libpari
	pdftex libpari
	make libpari.std; pdftex libpari; rm -f libpari.std
libpari.dvi: \$(PARI_TEX) \$(MACROS)
	-rm -f libpari.std
	tex libpari
	tex libpari
	make libpari.std; tex libpari; rm -f libpari.std

develop.pdf: develop.tex \$(MACROS)
	-rm -f develop.std
	pdftex develop
	pdftex develop
	make develop.std; pdftex develop; rm -f develop.std
develop.dvi: develop.tex \$(MACROS)
	-rm -f develop.std
	tex develop
	tex develop
	make develop.std; tex develop; rm -f develop.std

tutorial.pdf: tutorial.tex \$(MACROS)
	-rm -f tutorial.std
	pdftex tutorial
	pdftex tutorial
tutorial.dvi: tutorial.tex \$(MACROS)
	-rm -f tutorial.std
	tex tutorial
	tex tutorial

%.ps: %.dvi
	dvips \$< -o \$@

refcard.ps: refcard.dvi
	dvips refcard.dvi -o \$@

%.std: %.idx
	sed -e 's/!\([1-9]\)!/!00\1!/'\\
	    -e 's/!\([1-9][0-9]\)!/!0\1!/'\\
	    -e 's/\\\\EFF {}/f/g'\\
	  \$< | env LANG=C sort -f |\\
	sed -e 's/!00*\([0-9]*\)!/!\1!/' > \$@;

users.dvi: \$(USERS_TEX)
	-rm -f users.std
	tex users
	tex users
	make users.std; tex users; rm -f users.std

users.pdf: \$(USERS_TEX)
	-rm -f users.std
	pdftex users
	pdftex users
	make users.std; pdftex users; rm -f users.std

gpman: gp.1
	nroff -man gp.1 | unix2dos -ascii > gp.man

clean:
	rm -f *.log *.dvi *.idx *.ps *.pdf *.aux *.toc *.std *.dumbpod *.3 *.tmp *.html

cleandoc: clean

veryclean: clean
	rm -f paricfg.tex gp.man

.tex.pod:
	perl gphelp -to_pod \$*.tex > tmp_pod && mv tmp_pod \$*.pod

.tex.dumbpod:
	perl gphelp -to_dumb_pod \$*.tex > tmp_pod && mv tmp_pod \$*.dumbpod

.ipf.inf:
	ipfc /INF \$*.ipf

# This is for testing:
.pod.ipf:
	pod2ipf \$*.pod > tmp_ipf && mv tmp_ipf \$*.ipf

pari.ipf:  refcard.pod tutorial.pod usersch1.pod usersch1.pod usersch2.pod usersch3.pod appa.pod
	pod2ipf --title="PARI/GP Manual" --by-files --section-name="Getting started" --file=refcard.pod --file=tutorial.pod --section-name="User guide" --file=usersch1.pod --file=usersch2.pod --file=usersch3.pod --section-name=Appendices --file=appa.pod > tmp_ipf && mv tmp_ipf pari.ipf

dumbpod: appa.dumbpod usersch1.dumbpod usersch2.dumbpod usersch3.dumbpod

.dumbpod.html:
	pod2html --title="PARI/GP Manual, part \$*" --infile=\$*.dumbpod --outfile=tmp_html && mv tmp_html \$*.html

manpages: dumbpod appa.3 usersch1.3 usersch2.3 usersch3.3

html: dumbpod appa.html appb.html appd.html usersch1.html usersch2.html usersch3.html usersch4.html usersch5.html usersch6.html usersch7.html

.dumbpod.3:
	pod2man --section=3 --center="PARI/GP Manual, part \$*" --release=$version.$patch --lax \$*.dumbpod > tmp_man && mv tmp_man \$*.3
EOT

if test -n "$add_funclist"; then
  cat >> doc/Makefile << EOT

$src/funclist::
	@-$cfg/genfunclist $desc

$desc/\$(DESC): $src/funclist $desc/merge_822 $desc/PARI/822.pm
	cd $desc && \$(PERL) merge_822 ../funclist > def\$(TMPSUF)
	mv $desc/def\$(TMPSUF) \$@

usersch3.tex: $desc/\$(DESC) ../src/desc/doc_make usersFUNCS.tex
	cd ../src/desc && \$(PERL) doc_make > ../../doc/usersch3.tex
EOT
fi
