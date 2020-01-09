

tests := $(wildcard tests/*.mule)

main_exe := src/mule/mule.exe

all:
	dune build $(main_exe)
install: all
	dune build @install
	dune install mule
	dune install mule-stdlib
check: all
	MULE_ROOT=$(PWD)/stdlib dune runtest
	find stdlib/ -type f -name '*.mule' | xargs -n 1 ./mule eval
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;

.PHONY: all repl check format runtest
