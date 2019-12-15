

tests := $(wildcard tests/*.mule)

main_exe := src/mule/mule.exe

all:
	dune build $(main_exe)
install: all
	dune build @install
	dune install mule
check: all
	dune runtest
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;

.PHONY: all repl check format runtest
