pdf=wantpdfoutput
cat > doc/Makefile << EOT
#  This file was created by Configure. Any change made to it will be lost
#  next time configure is run.
#
SHELL = $make_sh

doc all: manual refcard tutorial
docps: refcard.ps tutorial.ps users.ps
docpdf: users.pdf tutorial.pdf refcard.pdf
manual: users.dvi
tutorial: tutorial.dvi

.SUFFIXES: .tex .ipf .pod .inf

paricfg.tex: paricfg.tex.in
	sed -e 's/@version@/$version.$patch/'\\
	    -e 's!@includedir@!/usr/local/include/pari!'\\
	    -e 's!@libdir@!/usr/local/lib!'\\
	    -e 's!@miscdir@!/usr/local/lib/pari!' paricfg.tex.in > \$@

tutorial.dvi: tutorial.tex paricfg.tex
	-rm -f $pdf
	tex tutorial.tex

tutorial.pdf: tutorial.tex paricfg.tex
	-touch $pdf
	pdftex tutorial.tex
	-rm -f $pdf

refcard: refcard.ps

refcard.pdf: refcard.tex paricfg.tex
	-touch $pdf
	pdftex refcard.tex
	-rm -f $pdf

refcard.dvi: refcard.tex paricfg.tex
	-rm -f $pdf
	tex refcard.tex

refcard.ps: refcard.dvi
	dvips -t landscape -t a4 refcard.dvi -o \$@

users.ps: users.dvi
	dvips users.dvi -o \$@

tutorial.ps: tutorial.dvi
	dvips tutorial.dvi -o \$@

users.dvi: users.tex appa.tex appb.tex appc.tex\\
 usersch1.tex usersch2.tex usersch3.tex usersch4.tex usersch5.tex\\
 paricfg.tex parimacro.tex
	-rm -f $pdf
	rm -f users.std; tex users;
	sed -e 's/!\([1-9]\)!/!00\1!/'\\
	    -e 's/!\([1-9][0-9]\)!/!0\1!/'\\
	    -e 's/\\\\EFF {}/f/g'\\
	  users.idx | sort -f |\\
	sed -e 's/!00*\([0-9]*\)!/!\1!/' > users.std;
	tex users; rm -f users.idx

users.pdf: users.tex appa.tex appb.tex appc.tex\\
 usersch1.tex usersch2.tex usersch3.tex usersch4.tex usersch5.tex\\
 paricfg.tex parimacro.tex
	rm -f users.std; touch $pdf; pdftex users;
	sed -e 's/!\([1-9]\)!/!00\1!/'\\
	    -e 's/!\([1-9][0-9]\)!/!0\1!/'\\
	    -e 's/\\\\EFF {}/f/g'\\
	  users.idx | sort -f |\\
	sed -e 's/!00*\([0-9]*\)!/!\1!/' > users.std;
	pdftex users; rm -f users.idx $pdf

gpman: gp.1
	nroff -man gp.1 | unix2dos -ascii > gp.man

halfclean:	
	rm -f *.log *.dvi *.idx *.ps *.pdf tutorial.aux $pdf

clean: halfclean	
	rm -f users.aux users.std users.toc

veryclean: clean
	rm -f paricfg.tex gp.man

.tex.pod:
	perl gphelp -to_pod \$*.tex > tmp_pod && mv tmp_pod \$*.pod

.ipf.inf:
	ipfc /INF \$*.ipf

# This is for testing:

.pod.ipf:
	pod2ipf \$*.pod > tmp_ipf && mv tmp_ipf \$*.ipf

pari.ipf:  refcard.pod tutorial.pod usersch1.pod usersch1.pod usersch2.pod usersch3.pod usersch4.pod usersch5.pod appa.pod appb.pod appc.pod
	pod2ipf --title="PARI/GP Manual" --by-files --section-name="Getting started" --file=refcard.pod --file=tutorial.pod --section-name="User guide" --file=usersch1.pod --file=usersch1.pod --file=usersch2.pod --file=usersch3.pod --file=usersch4.pod --file=usersch5.pod --section-name=Appendices --file=appa.pod --file=appb.pod --file=appc.pod > tmp_ipf && mv tmp_ipf pari.ipf
EOT
