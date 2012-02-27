# DEFINITIONS

cmo = cmo
cma = cma
cmx = cmx
OCAMLC = ocamlc -g -annot
OCAMLRUN = ocamlrun -b
OCAMLDEBUG = ocamldebug
OCAMLL = ocamlopt
OCAMLDEP = ocamldep -native -I ndcore
OCAMLDOC = ocamldoc
OCAMLYACC = ocamlyacc
OCAMLLEX = ocamllex

# SOURCE FILES
SELLF_ML = sellf.ml
#CORE_ML = lib.ml solverStr.ml term.ml prints.ml basic.ml structs.ml Constraints.ml ProofTree.ml typeChecker.ml norm.ml unify.ml common.ml boundedproofsearch.ml interpreter.ml macro.ml permutation.ml coherence.ml
# Using only what is needed for bounded proof search and coherence proof
CORE_ML = term.ml prints.ml basic.ml Subexponentials.ml staticpermutationcheck.ml Context.ml Sequent.ml ProofTree.ml typeChecker.ml norm.ml unify.ml boundedproofsearch.ml coherence.ml
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
	$(OCAMLC) unix.cma -o sellf $(CORE_CMO) $(PARSER_CMO)  $(SELLF_ML) 

# native : $(CORE_CMX) $(PARSER_CMX)  $(SELLF_ML) 
# 	$(OCAMLL) -o sellf $(CORE_CMX) $(PARSER_CMX)  $(SELLF_ML) 
# 
# %.cmx:  %.ml
# 	$(OCAMLL) -c $< 

run : $(CORE_CMO) $(PARSER_CMO)  $(SELLF_ML) 
	env OCAMLRUNPARAM=l=10M $(OCAMLRUN) sellf 

debug : $(CORE_CMO) $(PARSER_CMO)  $(SELLF_ML) 
	env OCAMLRUNPARAM=l=10M $(OCAMLDEBUG) sellf 

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
	rm -f *.cmi
	rm -f *.cmo
	rm -f *.cmx
	rm -f *.o
	rm -f *.annot
	rm -f sellf
	rm -f parser.mli
	rm -f parser.ml

test:  $(TEST_CMO)
	$(OCAMLC) unix.$(cma) $(CORE_CMO)  $(TEST_CMO) -o test


