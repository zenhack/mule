

tests := $(wildcard tests/*.in)
checks := $(tests:.in=.check)

all:
	dune build main.exe
repl: all
	rlwrap ./_build/default/main.exe
check: $(checks)
%.check: all %.in %.expected
	./_build/default/main.exe < $*.in > $*.actual
	diff -u $*.expected $*.actual
	touch $@
clean:
	rm -rf _build tests/*.check tests/*.actual

.PHONY: all repl check
