# Coq sources
COQDIR = coq
COQLIBDIR = lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Graph) -R $(EXTRACTDIR) Extract
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILESINTERP := Permutations Graphs STLC PHOAS Toposort

COQFILESOPT    := 

OLLVMFILES :=

VFILES  := $(COQFILESINTERP:%=coq/%.v) $(COQFILESOPT:%=coq/%.v)
VOFILES := $(COQFILESINTERP:%=coq/%.vo) $(COQFILESOPT:%=coq/%.vo)

.PHONEY: all
all: .depend
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq

coq: $(VOFILES)

coqinterp: $(COQFILESINTERP:%=coq/%.vo)

update-trees:
	git submodule update -- $(ITREEDIR)

.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP $(VOFILES)

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	touch $(EXTRACTDIR)/STAMP

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

.depend: $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend


.PHONY: clean test

print-includes:
	@echo $(COQINCLUDES)

clean: clean-graph
clean-graph:
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
	find $(COQLIBDIR) -name "*.vo" -delete
	find $(COQLIBDIR) -name "*.vio" -delete
	find $(COQLIBDIR) -name "*.vok" -delete
	find $(COQLIBDIR) -name "*.vos" -delete
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o

.PHONY: clean-graph


-include .depend
