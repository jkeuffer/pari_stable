pdf=wantpdfoutput
cat > doc/Makefile << EOT
#  This file was created by Configure. Any change made to it will be lost
#  next time configure is run.
#
SHELL = $make_sh

doc all: manual refcard tutorial
docps: refcard.ps tutorial.ps users.ps ../INSTALL.ps
docpdf: users.pdf tutorial.pdf refcard.pdf ../INSTALL.pdf
manual: users.dvi
tutorial: tutorial.dvi
refcard: refcard.ps

.SUFFIXES: .tex .ipf .pod .inf .dumbpod

paricfg.tex: paricfg.tex.in
	sed -e 's/@version@/$version.$patch/'\\
	    -e 's!@includedir@!$includedir!'\\
	    -e 's!@libdir@!$libdir!'\\
	    -e 's!@miscdir@!$miscdir!' paricfg.tex.in > \$@

tutorial.pdf: tutorial.tex paricfg.tex
	-touch $pdf
	pdftex tutorial.tex
	-rm -f $pdf

refcard.pdf: refcard.tex paricfg.tex
	-touch $pdf
	pdftex refcard.tex
	-rm -f $pdf

../INSTALL.pdf: ../INSTALL.tex
	-cd ..; touch $pdf; pdftex INSTALL.tex; rm -f $pdf

tutorial.dvi: tutorial.tex paricfg.tex
	-rm -f $pdf
	tex tutorial.tex

refcard.dvi: refcard.tex paricfg.tex
	-rm -f $pdf
	tex refcard.tex

../INSTALL.dvi: ../INSTALL.tex
	-cd ..; rm -f $pdf; tex INSTALL.tex

refcard.ps: refcard.dvi
	dvips -t landscape -t a4 refcard.dvi -o \$@

users.ps: users.dvi
	dvips users.dvi -o \$@

tutorial.ps: tutorial.dvi
	dvips tutorial.dvi -o \$@

../INSTALL.ps: ../INSTALL.dvi
	dvips ../INSTALL.dvi -o \$@

users.dvi: users.tex appa.tex appb.tex appc.tex\\
 usersch1.tex usersch2.tex usersch3.tex usersch4.tex usersch5.tex\\
 paricfg.tex parimacro.tex
	-rm -f $pdf
	rm -f users.std; tex users;
	sed -e 's/!\([1-9]\)!/!00\1!/'\\
	    -e 's/!\([1-9][0-9]\)!/!0\1!/'\\
	    -e 's/\\\\EFF {}/f/g'\\
	  users.idx | env LANG=C sort -f |\\
	sed -e 's/!00*\([0-9]*\)!/!\1!/' > users.std;
	tex users; rm -f users.idx

users.pdf: users.tex appa.tex appb.tex appc.tex\\
 usersch1.tex usersch2.tex usersch3.tex usersch4.tex usersch5.tex\\
 paricfg.tex parimacro.tex
	rm -f users.std; touch $pdf; pdftex users;
	sed -e 's/!\([1-9]\)!/!00\1!/'\\
	    -e 's/!\([1-9][0-9]\)!/!0\1!/'\\
	    -e 's/\\\\EFF {}/f/g'\\
	  users.idx | env LANG=C sort -f |\\
	sed -e 's/!00*\([0-9]*\)!/!\1!/' > users.std;
	pdftex users; rm -f users.idx $pdf

gpman: gp.1
	nroff -man gp.1 | unix2dos -ascii > gp.man

clean:	
	rm -f *.log *.dvi *.idx *.ps *.pdf *.aux *.toc users.std $pdf\\
	../INSTALL.log ../INSTALL.dvi ../INSTALL.idx ../INSTALL.pdf\\
	../INSTALL.aux ../INSTALL.toc ../INSTALL.ps ../$pdf

cleandoc: clean

veryclean: clean
	rm -f paricfg.tex gp.man

.tex.pod:
	perl gphelp -to_pod \$*.tex > tmp_pod && mv tmp_pod \$*.pod

.tex.dumbpod:
	perl gphelp -to_dumb_pod $*.tex > tmp_pod && mv tmp_pod $*.dumbpod

.ipf.inf:
	ipfc /INF \$*.ipf

# This is for testing:

.pod.ipf:
	pod2ipf \$*.pod > tmp_ipf && mv tmp_ipf \$*.ipf

pari.ipf:  refcard.pod tutorial.pod usersch1.pod usersch1.pod usersch2.pod usersch3.pod usersch4.pod usersch5.pod appa.pod appb.pod appc.pod
	pod2ipf --title="PARI/GP Manual" --by-files --section-name="Getting started" --file=refcard.pod --file=tutorial.pod --section-name="User guide" --file=usersch1.pod --file=usersch1.pod --file=usersch2.pod --file=usersch3.pod --file=usersch4.pod --file=usersch5.pod --section-name=Appendices --file=appa.pod --file=appb.pod --file=appc.pod > tmp_ipf && mv tmp_ipf pari.ipf

# Wrong syntax...  How to convert a group of files?
#pari.html:  refcard.dumbpod tutorial.dumbpod usersch1.dumbpod usersch1.dumbpod usersch2.dumbpod usersch3.dumbpod usersch4.dumbpod usersch5.dumbpod appa.dumbpod appb.dumbpod appc.dumbpod
#	pod2html --title="PARI/GP Manual" --by-files --section-name="Getting started" --file=refcard.dumbpod --file=tutorial.dumbpod --section-name="User guide" --file=usersch1.dumbpod --file=usersch1.dumbpod --file=usersch2.dumbpod --file=usersch3.dumbpod --file=usersch4.dumbpod --file=usersch5.dumbpod --section-name=Appendices --file=appa.dumbpod --file=appb.dumbpod --file=appc.dumbpod > tmp_ipf && mv tmp_ipf pari.html

.dumbpod.html:
	pod2html --title="PARI/GP Manual $* Getting started" --file=$*.dumbpod > tmp_html && mv tmp_html $*.html


EOT
