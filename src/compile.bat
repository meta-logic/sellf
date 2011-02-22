ocamlc -c term.ml 
ocamlc -c structs.ml
ocamlc -c typeChecker.ml
ocamlc -c norm.ml
ocamlc -c unify.ml
ocamlc -c interpreter.ml
ocamlyacc parser.mly
ocamlc -c parser.mli
ocamlc -c parser.ml
ocamllex lexer.mll
ocamllex lexer_top.mll
ocamlc -c lexer.ml
ocamlc -c lexer_top.ml
ocamlc -o sellf.exe *.cmo sellf.ml
del parser.mli
del parser.ml
