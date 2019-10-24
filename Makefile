

tests := $(wildcard tests/*.mule)
checks := $(tests:.mule=.check)

main_exe := src/mule/mule.exe

all:
	dune build $(main_exe)
install: all
	dune build @install
	dune install libmule
check: $(checks)
%.check: all %.mule %.expected
	@echo CHECK $*
	@DEBUG_STEPS=1 ./_build/default/$(main_exe) eval $*.mule > $*.actual || true
	@diff -u $*.expected $*.actual
	@touch $@
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;

.PHONY: all repl check format
