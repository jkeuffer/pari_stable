PERL=perl
all: ../language/init.h ../gp/gp_init.h ../gp/highlvl.h

Def::
	$(PERL) merge_822 ../functions/*/* > Def

../language/init.h: Def
	$(PERL) gen_proto basic Def > $@ && $(PERL) gen_help  basic Def >> $@

../gp/gp_init.h: Def
	$(PERL) gen_proto gp Def > $@ && $(PERL) gen_help  gp Def >> $@

../gp/highlvl.h: Def
	$(PERL) gen_proto highlevel Def > $@ && $(PERL) gen_help  highlevel Def >> $@

veryclean:
	rm -f Def ../language/init.h ../gp/gp_init.h ../gp/highlvl.h
