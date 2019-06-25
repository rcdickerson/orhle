.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f $^ $@

%: Makefile.coq
	$(MAKE) -f $^ $@

Makefile.coq:
	coq_makefile -f _CoqProject -o $@

clean: Makefile.coq
	$(MAKE) -f $^ cleanall
	rm Makefile.coq Makefile.coq.conf
