PERL=perl

HEADERS=../language/init.h ../gp/gp_init.h ../gp/highlvl.h
HE_DEPS=gen_proto gen_help PARI/822.pm

all: $(HEADERS)

Def: ../funclist merge_822 PARI/822.pm
	$(PERL) merge_822 ../functions/*/* > Def

../language/init.h: Def $(HE_DEPS)
	$(PERL) gen_proto basic Def > $@ && $(PERL) gen_help  basic Def >> $@

../gp/gp_init.h: Def $(HE_DEPS)
	$(PERL) gen_proto gp Def > $@ && $(PERL) gen_help  gp Def >> $@

../gp/highlvl.h: Def $(HE_DEPS)
	$(PERL) gen_proto highlevel Def > $@ && $(PERL) gen_help  highlevel Def >> $@

veryclean:
	rm -f Def $(HEADERS)
