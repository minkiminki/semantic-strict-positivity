COQMODULE    := ssp
COQTHEORIES  := lib/paco/src/*.v src/*.v

.PHONY: all theories clean

all: quick

build: paco Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: paco-quick Makefile.coq
	$(MAKE) -f Makefile.coq quick

paco: lib/paco/src
	$(MAKE) -C lib/paco/src

paco-quick: lib/paco/src
	$(MAKE) -C lib/paco/src quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib/paco/src Paco"; \
	echo "-R src $(COQMODULE)"; \
	\
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq
