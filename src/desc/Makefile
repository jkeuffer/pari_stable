PERL=perl
all: ../language/init.h ../gp/gp_init.h ../gp/highlvl.h

Def: 
	$(PERL) merge_822 ../functions/*/* > Def

../language/init.h: Def
	$(PERL) gen_proto basic Def > ../language/init.h
	$(PERL) gen_help basic Def >> ../language/init.h

../gp/gp_init.h: Def
	$(PERL) gen_proto gp Def >  ../gp/gp_init.h
	$(PERL) gen_help  gp Def >> ../gp/gp_init.h

../gp/highlvl.h: Def
	$(PERL) gen_proto highlevel Def >  ../gp/highlvl.h
	$(PERL) gen_help  highlevel Def >> ../gp/highlvl.h

veryclean:
	rm -f Def ../language/init.h ../gp/gp_init.h ../gp/highlvl.h
