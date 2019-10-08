

tests := $(wildcard tests/*.mule)
checks := $(tests:.mule=.check)

main_exe := ./_build/default/src/main.exe

all:
	dune build src/main.exe
repl: all
	rlwrap $(main_exe)
check: $(checks)
%.check: all %.mule %.expected
	@echo CHECK $*
	@$(main_exe) test $*.mule > $*.actual || true
	@diff -u $*.expected $*.actual
	@touch $@
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;

.PHONY: all repl check format
