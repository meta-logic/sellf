# DEFINITIONS

cmo = cmo
cma = cma
cmx = cmx
OCAMLC = ocamlc -g
OCAMLRUN = ocamlrun -b
OCAMLL = ocamlopt
OCAMLDEP = /usr/bin/ocamldep -native -I ndcore
OCAMLDOC = ocamldoc
OCAMLYACC = /usr/bin/ocamlyacc
OCAMLLEX = /usr/bin/ocamllex

# SOURCE FILES
SELLF_ML = sellf.ml
CORE_ML = term.ml structs.ml typeChecker.ml norm.ml unify.ml interpreter.ml
TEST_ML    = oUnit.ml test.ml
PARSER_ML = parser.ml lexer.ml lexer_top.ml
PARSER_CMO = $(PARSER_ML:.ml=.$(cmo)) 
CORE_CMO = $(CORE_ML:.ml=.$(cmo)) 
TEST_CMO = $(TEST_ML:.ml=.$(cmo)) 
PARSER_CMX = $(PARSER_ML:.ml=.$(cmx)) 
CORE_CMX = $(CORE_ML:.ml=.$(cmx)) 
TEST_CMX = $(TEST_ML:.ml=.$(cmx)) 


# COMMANDS

normal : $(CORE_CMO) $(PARSER_CMO)  $(SELLF_ML) 
	$(OCAMLC) -o sellf $(CORE_CMO) $(PARSER_CMO)  $(SELLF_ML) 

# native : $(CORE_CMX) $(PARSER_CMX)  $(SELLF_ML) 
# 	$(OCAMLL) -o sellf $(CORE_CMX) $(PARSER_CMX)  $(SELLF_ML) 
# 
# %.cmx:  %.ml
# 	$(OCAMLL) -c $< 

run : $(CORE_CMO) $(PARSER_CMO)  $(SELLF_ML) 
	env OCAMLRUNPARAM=l=10M $(OCAMLRUN) sellf 


%.cmo:  %.ml
	$(OCAMLC) -c $< 

%.cmi: %.mli %.ml
	$(OCAMLC) -c $<

%.ml: %.mli
	$(OCAMLC) -c $<

%.ml: %.mll 
	$(OCAMLLEX) $<

%.mli: %.mly
	$(OCAMLYACC) $<
	echo "Creating ml and mli files"

clean: 
	rm *.cmi
	rm *.cmo
	rm *.cmx
	rm *.o
	rm sellf
	rm parser.mli
	rm parser.ml

test:  $(TEST_CMO)
	$(OCAMLC) unix.$(cma) $(CORE_CMO)  $(TEST_CMO) -o test


