% Tonk connective (thanks to Dale Miller and Chuck Liang)

% SPECIFICATION
rules introduction.
% tonk

not (lft  (tonk A B)) * (lft  B).
% With this specification the conective is not dual
not (rght (tonk A B)) * (rght A).
% With this specification the connective is dual.
%not (rght (tonk A B)) * (rght B).

rules axiom.
% Axiom
not (lft A) * not (rght A).

rules cut.
% Cut rule
(lft A) * (rght A).
