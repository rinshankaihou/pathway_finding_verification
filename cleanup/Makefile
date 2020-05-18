all: Makefile.coq
	+make -f Makefile.coq all
	ocamlbuild extraction/coq_print.native -use-ocamlfind -package io-system

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f .*.aux
	rm -f *.glob
	rm -rf _build
	rm -f extraction/coq_print.ml
	rm -f extraction/coq_print.mli
	rm -f extraction/path_finding_algorithm.ml
	rm -f extraction/path_finding_algorithm.mli
	rm -f coq_print.native

Makefile.coq: Make
	$(COQBIN)coq_makefile -f Make -o Makefile.coq

Make: ;

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean
