# Path to pari.cfg file
PARI_CFG=/usr/local/lib/pari/pari.cfg

# Where to install ourselves ?
INSTALL=/usr/local/share/emacs/site-list/pari

# Path to 'emacs' binary
EMACS=emacs

install: pari-conf.el elc
	mkdir -p $(INSTALL)
	cp *.elc *.el pariemacs.txt $(INSTALL)

pari-conf.el: pari-conf.el.in
	. $(PARI_CFG); sed -e "s/@version@/$$pari_release/" \
	    -e "s!@emacsdir@!$(INSTALL)!" \
	    -e "s!@bindir@!$$bindir!" pari-conf.el.in > $@

elc:
	@echo "Byte-Compiling elisp files..."
	-$(EMACS) -batch \
	   --eval '(setq load-path (append (list ".") load-path))' \
	   -f batch-byte-compile *.el

clean:
	rm -f *.elc
