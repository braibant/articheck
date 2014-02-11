all: arti

arti: arti.ml
	ocamlfind ocamlopt -g -annot -bin-annot -w @1..3@8..12@14..21@23..40-41@43 $< -o $@

clean:
	rm -f *.cm* arti *.o *.annot

test: arti
	./arti

doc: arti
	mkdir -p ../doc/
	ocamldoc -d ../doc/ -html *.ml
