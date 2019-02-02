

all:
	dune build main.exe
repl: all
	rlwrap ./_build/default/main.exe

.PHONY: all repl
