PERL=perl

HEADERS=../language/init.h ../gp/gp_init.h ../gp/highlvl.h ../language/members.h
HE_DEPS=gen_proto gen_help PARI/822.pm
DEF=pari.desc

all: $(HEADERS)

$(DEF): ../funclist merge_822 PARI/822.pm
	$(PERL) merge_822 ../functions/*/* > $(DEF)

../language/members.h: $(DEF) gen_member
	$(PERL) gen_member $(DEF) > $@ 

../language/init.h: $(DEF) $(HE_DEPS)
	$(PERL) gen_proto basic $(DEF) > $@ && $(PERL) gen_help  basic $(DEF) >> $@

../gp/gp_init.h: $(DEF) $(HE_DEPS)
	$(PERL) gen_proto gp $(DEF) > $@ && $(PERL) gen_help  gp $(DEF) >> $@

../gp/highlvl.h: $(DEF) $(HE_DEPS)
	$(PERL) gen_proto highlevel $(DEF) > $@ && $(PERL) gen_help  highlevel $(DEF) >> $@

veryclean:
	rm -f $(DEF) $(HEADERS)
