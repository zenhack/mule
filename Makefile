

tests := $(wildcard tests/*.mule)
checks := $(tests:.mule=.check)

main_exe := src/mule/mule.exe
utop_bc := src/mule-utop/mule_utop.bc

all:
	dune build $(main_exe)
	dune build $(utop_bc)
utop: all
	./_build/default/$(utop_bc)
repl: all
	rlwrap ./_build/default/$(main_exe)
check: $(checks)
%.check: all %.mule %.expected
	@echo CHECK $*
	@./_build/default/$(main_exe) test $*.mule > $*.actual || true
	@diff -u $*.expected $*.actual
	@touch $@
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;

.PHONY: all repl check format
