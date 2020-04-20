default: build
	utop

build:
	ocamlbuild -use-ocamlfind main.byte type_checker.byte

test:
	ocamlbuild -use-ocamlfind test.byte && ./test.byte

clean:
	ocamlbuild -clean
