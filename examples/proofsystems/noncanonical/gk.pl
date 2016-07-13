%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for GK                %
% (for Paraconsistent Logics)               %
%                                           %
% Giselle Reis - 2012                       %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l unb.
subexp r unb.

rules introduction.

% Conjunction
(not (lft (and A B))) * ((?[l] (lft A)) | (?[l] (lft B))).
(not (rght (and A B))) * ((?[r] (rght A)) * (?[r] (rght B))).

% Disjunction
(not (lft (or A B))) * ((?[l] (lft A)) * (?[l] (lft B))).
(not (rght (or A B))) * ((?[r] (rght A)) | (?[r] (rght B))).

% Implication
(not (lft (imp A B))) * ((?[r] (rght A)) * (?[l] (lft B))).
(not (rght (imp A B))) *  ((?[l] (lft A)) | (?[r] (rght B))).

% Negation
(not (lft (gkneg A))) * (?[l] (lft A)).

% Consistent
(not (lft (cons A))) * ((?[r] (rght A)) * (?[r] (rght (gkneg A)))).
(not (rght (cons A))) * ((?[l] (lft A)) | (?[l] (lft (gkneg A)))).

% (c)
%(not (lft (gkneg (gkneg A)))) * (?[l] (lft A)).

% (e)
%(not (rght (gkneg (gkneg A)))) * (?[r] (rght A)).

% (i1)
%(not (lft (gkneg (cons A)))) * (?[l] (lft A)).

% (i2)
%(not (lft (gkneg (cons A)))) * (?[l] (lft (gkneg A))).

% (a_conj)
%(not (lft (gkneg (and A B)))) * ((?[l] (lft (gkneg A))) * (?[l] (lft (gkneg B)))).

% (a_disj1)
%(not (lft (gkneg (or A B)))) * ((?[l] (lft (gkneg A))) * ((?[l] (lft (gkneg B))) | (?[l] (lft B)))).

% (a_disj2)
%(not (lft (gkneg (or A B)))) * ((?[l] (lft (gkneg B))) * ((?[l] (lft (gkneg A))) | (?[l] (lft A)))).

% (a_impl1)
%(not (lft (gkneg (imp A B)))) * ((?[l] (lft A)) * ((?[l] (lft (gkneg B))) | (?[l] (lft B)))).

% (a_impl2)
%(not (lft (gkneg (imp A B)))) * (((?[l] (lft (gkneg A))) | (?[l] (lft A))) * (?[l] (lft (gkneg B)))).

% (o_conj1)
%(not (lft (gkneg (and A B)))) * ((?[l] (lft (gkneg A))) * (?[l] (lft B))).

% (o_conj2)
%(not (lft (gkneg (and A B)))) * ((?[l] (lft (gkneg B))) * (?[l] (lft A))).

% (o_disj11)
%(not (lft (gkneg (or A B)))) * (?[l] (lft (gkneg A))).

% (o_disj12)
%(not (lft (gkneg (or A B)))) * ((?[l] (lft A)) * (?[r] (rght B))).

% (o_disj21)
%(not (lft (gkneg (or A B)))) * (?[l] (lft (gkneg B))).

% (o_disj22)
%(not (lft (gkneg (or A B)))) * ((?[l] (lft B)) * (?[r] (rght A))).

% (o_impl11)
%(not (lft (gkneg (imp A B)))) * ((?[l] (lft (gkneg A))) * (?[r] (rght B))).

% (o_impl12)
%(not (lft (gkneg (imp A B)))) * (?[l] (lft A)).

% (o_impl21)
%(not (lft (gkneg (imp A B)))) * (?[l] (lft (gkneg B))).

% (o_impl22)
%(not (lft (gkneg (imp A B)))) * ((?[l] (lft A)) * (?[l] (lft B))).

rules axiom.
((not (lft A)) * (not (rght A))).

rules cut.
%((?[r] (rght A)) * (?[l] (lft A))).
