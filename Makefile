

tests := $(wildcard tests/*.mule)
checks := $(tests:.mule=.check)

main_exe := src/mule/mule.exe

all:
	dune build $(main_exe)
install: all
	dune build @install
	dune install libmule
check: runtest $(checks)
%.check: all %.mule %.expected
	@echo CHECK $*
	@./_build/default/$(main_exe) eval --debug-steps $*.mule > $*.actual || true
	@diff -u $*.expected $*.actual
	@touch $@
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;
runtest:
	dune runtest

.PHONY: all repl check format runtest
