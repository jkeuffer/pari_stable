PERL=perl

HEADERS=../language/init.h ../gp/gp_init.h ../gp/highlvl.h ../language/members.h
HE_DEPS=gen_proto gen_help PARI/822.pm
DEF=pari.desc

all: $(HEADERS)

$(DEF): ../funclist merge_822 PARI/822.pm
	$(PERL) merge_822 ../functions/*/* > $(DEF).new && mv $(DEF).new $(DEF)

../language/members.h: $(DEF) gen_member
	$(PERL) gen_member $(DEF) > $@.new && mv $@.new $@

../language/init.h: $(DEF) $(HE_DEPS)
	$(PERL) gen_proto basic $(DEF) > $@.new && $(PERL) gen_help basic $(DEF) >> $@.new && mv $@.new $@

../gp/gp_init.h: $(DEF) $(HE_DEPS)
	$(PERL) gen_proto gp $(DEF) > $@.new && $(PERL) gen_help gp $(DEF) >> $@.new && mv $@.new $@

../gp/highlvl.h: $(DEF) $(HE_DEPS)
	$(PERL) gen_proto highlevel $(DEF) > $@.new && $(PERL) gen_help  highlevel $(DEF) >> $@.new && mv $@.new $@

veryclean:
	rm -f $(DEF) $(HEADERS)
