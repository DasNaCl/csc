EXTRA_DIR:=extra
COQDOCFLAGS:= \
	--toc --toc-depth 2 --html --interpolate \
	--index indexpage --no-lib-name --parse-comments \
	--with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

#%: Makefile.coq phony
#	+make -f Makefile.coq $@

all: coq ocaml

coq: Makefile.coq Ltms/Parser.v
	+make -f Makefile.coq all

ocaml: coq Ltms/Parser.ml
	ocamlc -g -I Ltms Ltms/Parser.mli
	ocamlc -g -o a.out -I Ltms Ltms/Parser.ml Driver.ml

Ltms/Parser.v: Ltms/Parser.vy
	menhir --coq --coq-no-complete Ltms/Parser.vy

Ltms/Parser.ml: coq

clean-coq: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Ltms/Parser.v Ltms/Parser.vo Ltms/Parser.vok Ltms/Parser.vos Ltms/Parser.glob Ltms/Parser.ml

clean-ocaml:
	rm -f a.out Driver.cmi Driver.cmo Driver.o Driver.cmx \
		    Ltms/Parser.o Ltms/Parser.cmi Ltms/Parser.cmo Ltms/Parser.cmx Ltms/Parser.mli

clean: Makefile.coq clean-coq clean-ocaml

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;

html: Makefile.coq
	rm -fr html
	@$(MAKE) -f Makefile.coq $@
	cp $(EXTRA_DIR)/resources/* html

phony: ;

.PHONY: all clean phony
