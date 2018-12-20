UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  FORMAT=aout
  PIE=
else
ifeq ($(UNAME), Darwin)
  FORMAT=macho
  PIE=
endif
endif

PKGS=oUnit,extlib,unix,batteries
BUILD=ocamlbuild -r -use-ocamlfind

_build/util.o: util.c util.h
	clang -m32 -c -g -o _build/util.o util.c

_build/gc.o: gc.c gc.h util.h
	clang -m32 -c -g -o _build/gc.o gc.c

main: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS) main.native
	mv main.native main

test: *.ml parser.mly lexer.mll
	$(BUILD) -no-hygiene -package $(PKGS),str test.native
	mv test.native test

output/%.run: output/%.o _build/gc.o _build/util.o main.c
	clang $(PIE) -mstackrealign -g -m32 -o $@ $^

output/%.o: output/%.s
	nasm -f $(FORMAT) -o $@ $<

.PRECIOUS: output/%.s
output/%.s: input/%.snake main
	./main $< > $@

clean:
	rm -rf output/*.o output/*.s output/*.dSYM output/*.run *.log
	rm -rf _build/
	rm -f main test
