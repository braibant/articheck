all: arti

arti: arti.ml
	ocamlfind ocamlopt -g -annot -bin-annot $< -o $@
	
clean:
	rm -f *.cm* arti *.o *.annot

test: arti
	./arti
