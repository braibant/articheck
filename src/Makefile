.PHONY all:
	ocamlbuild -I example silist.native rbt.native avl.native

# arti: arti.ml
# 	ocamlfind ocamlopt -g -annot -bin-annot -w @1..3@8..12@14..21@23..40-41@43 $< -o $@

clean:
	ocamlbuild -clean

test: all
	./silist.native
	./rbt.native

doc: arti
	mkdir -p ../doc/
	ocamldoc -I _build -d ../doc/ -html *.ml

