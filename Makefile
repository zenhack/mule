

tests := $(wildcard tests/*.mule)
checks := $(tests:.mule=.check)

all:
	dune build main.exe
repl: all
	rlwrap ./_build/default/main.exe
check: $(checks)
%.check: all %.mule %.expected
	@echo CHECK $*
	@./_build/default/main.exe test $*.mule > $*.actual || true
	@diff -u $*.expected $*.actual
	@touch $@
clean:
	rm -rf _build tests/*.check tests/*.actual

.PHONY: all repl check
