#===========================================================================
# You may need to modify one of the following three variables

# Path to pari.cfg file
PARI_CFG=/usr/local/lib/pari/pari.cfg

# Where to install ourselves ?
INSTALL=/usr/local/share/emacs/site-list/pari

# Path to 'emacs' binary
EMACS=emacs

#===========================================================================
# Maintainer only.

# version number (How do we call ourselves?)
DIR=pariemacs-2.55
FILES=Makefile pari-completion.el pari-conf.el.in pari-fontification.el pari-help.el pari-messages.el pari.el pariemacs.txt sli-tools.el
TARFILE=$(DIR).tar

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

distrib: 
	@if test -d $(DIR); then \
	  echo "Remove $(DIR) before building a new release"; exit 1; \
	fi
	@tar cf $(TARFILE) $(FILES)
	@mkdir $(DIR) && mv $(TARFILE) $(DIR)
	@cd $(DIR) && tar xf $(TARFILE) && rm -f $(TARFILE)
	@tar cf $(TARFILE) $(DIR)
	@rm -rf $(DIR)
	@rm -f $(TARFILE).gz
	@gzip  $(TARFILE)

clean:
	rm -f *.elc pari-conf.el
