%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% Minimal specification for testing         %
% automatic generation of Coq code.         %
%                                           %
% Giselle Reis  -  2017                     %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp r lin.
subexp l unb.

subexpctx l many ant.
subexpctx r single suc.

%subexprel r < l.

rules introduction.

% Conjunction
(not (lft (conj A B))) * ((?[l] (lft A)) | (?[l] (lft B))).
(not (rght (conj A B))) * ((?[r] (rght A)) & (?[r] (rght B))).

% False
(not (lft bottom)) * top.

rules axiom.
((not (lft A)) * (not (rght A))).

