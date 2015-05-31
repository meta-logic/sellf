%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                             %
% SELLF specification for Lax %
%                             %
% Giselle Machado Reis - 2012 %
%                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l  unb.
subexp r  lin.
subexp cr lin.

subexprel r < cr.
subexprel cr < l.

subexpctx l many lft.
subexpctx r single rght.
subexpctx cr single rght.

rules introduction.
% Conjunction
(not (lft (and A B))) * ([l]? (lft A)) | ([l]? (lft B)).
(not (rght (and A B))) * (([l]bang ([r]? (rght A))) * ([l]bang ([r]? (rght B)))).

% Disjunction
(not (lft (or A B))) * ([l]? (lft A)) & ([l]? (lft B)).
(not (rght (or A B))) * ([l]bang ([r]? (rght A))) + ([l]bang ([r]? (rght B))).

% Implication
(not (lft (imp A B))) * (([l]bang (([r]? (rght A)))) * ([l]? (lft B))).
(not (rght (imp A B))) * [l]bang (([l]? (lft A)) | (([r]? (rght B)))).

% Circ
(not (lft (circ A))) * [cr]bang ([l]? (lft A)).
(not (rght (circ A))) * [l]bang ([r]? (rght A)).

rules axiom.
% Initial
((not (lft A)) * (not (rght A))).

rules cut.
% Cut
(([l]? (lft A)) * ([l]bang ([r]? (rght A)))).

rules structural.
% Structural rule for circ
((not (rght (circ A))) * ([cr]? (rght (circ A)))).

