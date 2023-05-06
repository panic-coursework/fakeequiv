-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep
COQFLAGS=-R . ''

FILES = $(shell find -name '*.v')

all: $(FILES:%.v=%.vo)

$(FILES:%.v=%.vo): %.vo: %.v
	$(COQC) $(COQFLAGS) $<

_CoqProject:
	echo $(COQFLAGS) > _CoqProject

depend: .depend
.depend: $(FILES)
	$(COQDEP) $(COQFLAGS) $(FILES) > .depend

clean:
	rm -f **/*.glob **/*.vo **/*.vok **/*.vos **/.*.aux .depend

.PHONY: clean depend

-include .depend
