

tests := $(wildcard tests/*.mule)

main_exe_tgt := src/mule/mule.exe
main_exe_path := $(PWD)/_build/default/$(main_exe_tgt)

all:
	dune build $(main_exe_tgt)
install: all
	dune build @install
	dune install mule
	dune install mule-stdlib
check: check_expect check_stdlib check_dunetest

check_dunetest:
	MULE_ROOT=$(PWD)/stdlib dune runtest

check_expect:
	@find tests/ -type f -name '*.mule' \
		| xargs -n 1 \
		./scripts/expect-test.sh $(main_exe_path)

check_stdlib:
	@find stdlib/ -type f -name '*.mule' \
		| xargs -n 1 \
		./scripts/check-stdlib.sh $(main_exe_path)
clean:
	rm -rf _build tests/*.check tests/*.actual
format:
	find src/ -type f -name '*.ml*' -exec ocp-indent -i \{} \;

.PHONY: all repl check format check_dunetest check_stdlib
