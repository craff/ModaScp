all: test.native solver.native doc/scp_model.pdf

test.native: $(wildcard *.ml)
	ocamlbuild -package bindlib,unix -use-ocamlfind test.native

solver.native: $(wildcard *.ml)
	ocamlbuild -package bindlib,unix -use-ocamlfind solver.native

doc/scp_model.pdf: doc/scp_model.tex
	cd doc; rubber --pdf scp_model.tex

.PHONY: test
test: test.native
	./$^

clean:
	rm -f *~ doc/*~ \#*\#
	ocamlbuild -clean
	cd doc; rubber --clean scp_model.tex

distclean: clean
	rm -f doc/scp_model.pdf
