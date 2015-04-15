Linear logic frameworks have been successfully used to specify many systems, such as multiset rewrite systems, programming languages, proof systems, and concurrent systems. However, previous frameworks still fall short whenever one needs to
separate different resources, namely linear logic formulas,
in different locations, namely linear contexts. Locations can have many interpretations, for instance, space, time, ownership, etc. Thereby, locations can be naturally used, for example, in the specification of algorithms, in the encoding of proof systems, and in the specification of access control policies.
Linear logic with subexponentials, on the other hand,  is a
refinement of linear logic that allows one to place resources in different locations, create new locations, and check whether a location is empty. These operations have been shown to be enough to capture in a purely linear fashion a wide range of algorithms,
proof systems as well as access control policies that were not possible before. Moreover, besides linear contexts, one is also able to specify contexts which only contain either affine, relevant, or unbounded formulas.
SELLF is an OCaml implementation of a fragment of linear logic with subexponentials.

A part of SELLF, called TATU, consists of a tool that takes specifications of sequent calculus systems in linear logic with subexponentials and checks:

  * if the cut rule can be permuted such that it is a principal cut;
  * if the principal cut can be reduced to the atomic case;
  * if atomic cuts can be eliminated.

Basically, the system checks the admissibility of the cut rule(s). This implementation can be tested online at: [TATU](http://www.logic.at/people/giselle/tatu).

Another part of SELLF, called QUATI, is a tool that can check permutation lemmas and print the rules of the object logic similar to a way they would appear in a text book. This is very useful for checking whether the specification actually corresponds to the intended sequent calculus rule. The implementation has a web-interface with some examples at: [QUATI](http://www.logic.at/staff/giselle/quati).

