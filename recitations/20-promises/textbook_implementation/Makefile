default: build
	utop

build:
	ocamlbuild -use-ocamlfind promise.byte 
	ocamlbuild -use-ocamlfind -tag thread async_write_demo.byte

clean:
	ocamlbuild -clean