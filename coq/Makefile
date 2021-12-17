EXTRA_DIR:=extra
COQDOCFLAGS:= \
	--toc --toc-depth 2 --html --interpolate \
	--index indexpage --no-lib-name --parse-comments \
	--with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

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

