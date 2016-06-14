
Thank you for your interest in SELLF :)

### Introduction

Linear logic frameworks have been successfully used to specify many systems,
such as multiset rewrite systems, programming languages, proof systems, and
concurrent systems. However, previous frameworks still fall short whenever one
needs to separate different resources, namely linear logic formulas, in
different locations, namely linear contexts. Locations can have many
interpretations, for instance, space, time, ownership, etc. Thereby, locations
can be naturally used, for example, in the specification of algorithms, in the
encoding of proof systems, and in the specification of access control policies.
Linear logic with subexponentials, on the other hand,  is a refinement of linear
logic that allows one to place resources in different locations, create new
locations, and check whether a location is empty. These operations have been
shown to be enough to capture in a purely linear fashion a wide range of
algorithms, proof systems as well as access control policies that were not
possible before. Moreover, besides linear contexts, one is also able to specify
contexts which only contain either affine, relevant, or unbounded formulas.
SELLF is an OCaml implementation of a fragment of linear logic with
subexponentials.

A part of SELLF, called TATU, consists of a tool that takes specifications of
sequent calculus systems in linear logic with subexponentials and checks:

  * if the cut rule can be permuted such that it is a principal cut;
  * if the principal cut can be reduced to the atomic case;
  * if atomic cuts can be eliminated.

Basically, the system checks the admissibility of the cut rule(s). This
implementation can be tested online at:
[TATU](http://www.logic.at/people/giselle/tatu).

Another part of SELLF, called QUATI, is a tool that can check permutation lemmas
and print the rules of the object logic similar to a way they would appear in a
text book. This is very useful for checking whether the specification actually
corresponds to the intended sequent calculus rule. The implementation has a
web-interface with some examples at:
[QUATI](http://www.logic.at/staff/giselle/quati).

### Requirements

These tools must be installed for 'sellf' to work.

  * ocaml, ocamldoc (http://caml.inria.fr/)
  * ocamlgraph (http://ocamlgraph.lri.fr/index.en.html)
  * dlv (http://www.dlvsystem.com/dlv/)

NOTE: The system is implemented and tested in Linux/Fedora and MacOS, and
explicitly makes use of the Unix OCaml module. 

### Installation

Execute the installation script:

```
$ ./install.sh
```

It will create a binary called 'sellf' in the current directory. To start the
program, execute this binary. It also creates a documentation of the main
modules implemented. This is a pdf file in the folder 'doc'.

### Syntax

The operators of linear logic with subexponentials and its syntax are:

| Operator name | Syntax |
| ------------- |:------:|
| tensor        |  `*`   |
| plus          |  `+`   |
| with          |  `&`   |
| par           |  `|`   |
| !l            |  `![l]` |
| ?l            |  `?[l]`    |
| one           |  `one` |
| zero          |  `zero`|
| top           |  `top` |
| bottom        |  `bot` |

Binary operators associate on the right.

To comment some line in your file, start it with the symbol '%'.
Signature files have sufix '.sig' and the program file has sufix '.pl' (both
must have the same name).

### Running

After compilation, an executable file called 'sellf' will be created in the
current folder. To execute it, just type:

```
$ ./sellf
```

and press enter. A command line prompt will appear with the symbol ':>'. For a
list of commands available, you can type '#help'. 

Some example specifications can be found inside the 'examples/proofsystems'
folder. If you open the file 'mall.pl' you can see the specification of
multiplicative additive linear logic (MALL). A specification rule has the
following form:

```
not (rght (tensor A B)) * ?[lr] (rght A) * ?[lr] (rght B).
```

Some buit-in elements for the specification of systems are:

  * 'form' as the type of formulas of the object logic
  * 'term' as the type of terms of the object logic
  * atomic predicates 'rght' and 'lft' of type form -> o

A specification can be built of formulas using these operators and the
predicates 'rght' or 'lft' that atomizes formulas of the object logic. They are
also divided in four sections which are identified by the keywords: 'rules
introduction', 'rules axiom', 'rules cut' and 'rules structural'.

To load the file 'mall.pl' of the examples folder, run 'sellf' as expalined above
and type:

```
:> #load examples/proofsystems/mall
```

Then, the system will display a 'mall >' symbol indicating that the file is loaded.
The commands available at this point can be seen using the command '#help'. 

Alternatively, a file can be loaded directly from the command line:

```
$ ./sellf -i examples/proofsystems/mall
```

