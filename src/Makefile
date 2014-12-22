#*********************************************************************#
#                                                                     #
#                           Objective Caml                            #
#                                                                     #
#            Pierre Weis, projet Cristal, INRIA Rocquencourt          #
#                                                                     #
#  Copyright 1998 Institut National de Recherche en Informatique et   #
#  en Automatique.  Distributed only by permission.                   #
#                                                                     #
#*********************************************************************#
# 
# Modified by Didier Remy
# 

#                   Generic Makefile for Objective Caml Programs

############################ Documentation ######################
#
# To use this Makefile:
# -- You must fix the value of the variable SOURCES below.
# (The variable SOURCES is the list of your Caml source files.)
# -- You must create a file .depend, using
# $touch .depend
# (This file will contain the dependancies between your Caml modules,
#  automatically computed by this Makefile.)

# Usage of this Makefile:
# To incrementally recompile the system, type
#     make
# To recompute dependencies between modules, type
#     make depend
# To remove the executable and all the compiled files, type
#     make clean
# To compile using the native code compiler
#     make opt
#
##################################################################


##################################################################
#
# Advanced usage:
# ---------------

# If you want to fix the name of the executable, set the variable
# EXEC, for instance, if you want to obtain a program named my_prog:
# EXEC = my_prog

# If you need special libraries provided with the Caml system,
# (graphics, arbitrary precision numbers, regular expression on strings, ...),
# you must set the variable LIBS to the proper set of libraries. For
# instance, to use the graphics library set LIBS to $(WITHGRAPHICS):
# LIBS=$(WITHGRAPHICS)

# You may use any of the following predefined variable
# WITHGRAPHICS : provides the graphics library
# WITHUNIX : provides the Unix interface library
# WITHSTR : provides the regular expression string manipulation library
# WITHNUMS : provides the arbitrary precision arithmetic package
# WITHTHREADS : provides the byte-code threads library
# WITHDBM : provides the Data Base Manager library
#
#
########################## End of Documentation ####################



########################## User's variables #####################
#
# The Caml sources (including camlyacc and camllex source files)

SOURCES = types.mli term.ml prints.ml basic.ml llrules.ml subexponentials.ml specification.ml typeChecker.ml context.ml contextSchema.ml constraints.ml constraints.mli sequent.ml norm.ml proofTree.ml proofTreeSchema.ml parser_models.mly lexer_models.mll dlv.ml bipole.ml olRule.ml permutation.ml unify.ml staticpermutationcheck.ml boundedproofsearch.ml coherence.ml parser.mly lexer.mll lexer_top.mll sellf.ml 

QUATI = types.mli subexponentials.ml specification.ml contextSchema.ml constraints.ml constraints.mli sequent.ml proofTreeSchema.ml dlv.ml bipole.ml ol.ml permutation.ml sellf.ml 

# The executable file to generate
EXEC = sellf

# The documentation file
DOC = sellfdoc.tex
DOT = dependencies.gv


########################## Advanced user's variables #####################
#
# The Caml compilers.
# You may fix here the path to access the Caml compiler on your machine
# You may also have to add various -I options.
CAMLC = ocamlc -g -annot -I +ocamlgraph
CAMLOPT = ocamlopt -I +ocamlgraph
CAMLDEP = ocamldep
CAMLLEX = ocamllex
CAMLYACC = ocamlyacc
CAMLDOC = ocamldoc -latex
CAMLDOT = ocamldoc -dot

# The list of Caml libraries needed by the program
# For instance:
# LIBS=$(WITHGRAPHICS) $(WITHUNIX) $(WITHSTR) $(WITHNUMS) $(WITHTHREADS)\
# $(WITHDBM)

LIBS=$(WITHUNIX) $(WITHGRAPH)

# Should be set to -custom if you use any of the libraries above
# or if any C code have to be linked with your program
# (irrelevant for ocamlopt)

# G: Removing the -custom option so that the generated file works with the
# debugger.
#CUSTOM=-custom
CUSTOM=

# Default setting of the WITH* variables. Should be changed if your
# local libraries are not found by the compiler.
WITHGRAPHICS =graphics.cma -cclib -lgraphics -cclib -L/usr/X11R6/lib -cclib -lX11

WITHUNIX =unix.cma -cclib -lunix

WITHSTR =str.cma -cclib -lstr

WITHNUMS =nums.cma -cclib -lnums

WITHTHREADS =threads.cma -cclib -lthreads

WITHDBM =dbm.cma -cclib -lmldbm -cclib -lndbm

WITHGRAPH =graph.cma

################ End of user's variables #####################


##############################################################
################ This part should be generic
################ Nothing to set up or fix here
##############################################################

all:: .depend.input .depend $(EXEC)

opt:: $(EXEC)-opt

doc:: $(EXEC)-doc

dot:: $(EXEC)-dot

#ocamlc -custom other options graphics.cma other files -cclib -lgraphics -cclib -lX11
#ocamlc -thread -custom other options threads.cma other files -cclib -lthreads
#ocamlc -custom other options str.cma other files -cclib -lstr
#ocamlc -custom other options nums.cma other files -cclib -lnums
#ocamlc -custom other options unix.cma other files -cclib -lunix
#ocamlc -custom other options dbm.cma other files -cclib -lmldbm -cclib -lndbm

SMLIY = $(SOURCES:.mly=.ml)
SMLIYL = $(SMLIY:.mll=.ml)
SMLYL = $(filter %.ml,$(SMLIYL))
OBJS = $(SMLYL:.ml=.cmo)
OPTOBJS = $(SMLYL:.ml=.cmx)

SMLIYDOC = $(QUATI:.mly=.ml)
SMLIYLDOC = $(SMLIYDOC:.mll=.ml)
SMLYLDOC = $(filter %.ml,$(SMLIYLDOC))

$(EXEC): $(OBJS) 
	$(CAMLC) $(CUSTOM) -o $(EXEC) $(LIBS) $(OBJS)

$(EXEC)-opt: $(OPTOBJS)
	$(CAMLOPT) -o $(EXEC) $(LIBS:.cma=.cmxa) $(OPTOBJS)

$(EXEC)-doc: 
	$(CAMLDOC) -o ../doc/$(DOC) $(SMLIYLDOC)

$(EXEC)-dot: 
	$(CAMLDOT) -o ../doc/$(DOT) $(SMLIYLDOC)

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly 

.ml.cmo:
	$(CAMLC) -c $<

.mli.cmi:
	$(CAMLC) -c $<

.ml.cmx:
	$(CAMLOPT) -c $<

.mll.cmo:
	$(CAMLLEX) $<
	$(CAMLC) -c $*.ml

.mll.cmx:
	$(CAMLLEX) $<
	$(CAMLOPT) -c $*.ml

.mly.cmo:
	$(CAMLYACC) $<
	$(CAMLC) -c $*.mli
	$(CAMLC) -c $*.ml

.mly.cmx:
	$(CAMLYACC) $<
	$(CAMLOPT) -c $*.mli
	$(CAMLOPT) -c $*.ml

.mly.cmi:
	$(CAMLYACC) $<
	$(CAMLC) -c $*.mli

.mll.ml:
	$(CAMLLEX) $<

.mly.ml:
	$(CAMLYACC) $<

clean::
	rm -f *.cm[iox] *~ .*~ #*#
	rm -f $(EXEC)
	rm -f $(EXEC).opt
	rm -f *.annot
	rm -f *.o
	rm -f parser.mli
	rm -f parser.ml
	rm -f parser_models.mli
	rm -f parser_models.ml
	rm -f lexer_top.ml
	rm -f lexer.ml
	rm -f lexer_models.ml

.depend.input: Makefile
	@echo -n '--Checking Ocaml input files: '
	@(ls $(SMLIY) $(SMLIY:.ml=.mli) 2>/dev/null || true) \
	     >  .depend.new
	@diff .depend.new .depend.input 2>/dev/null 1>/dev/null && \
	    (echo 'unchanged'; rm -f .depend.new) || \
	    (echo 'changed'; mv .depend.new .depend.input)

depend: .depend

.depend:: $(SMLIY) .depend.input
	@echo '--Re-building dependencies'
	$(CAMLDEP) $(SMLIY) $(SMLIY:.ml=.mli) > .depend

include .depend
