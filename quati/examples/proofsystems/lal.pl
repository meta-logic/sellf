%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                      %
% SELLF specification for LAL                          %
% (Linear Authorization Logics)                        %
% Vivek Nigam - 2012                                   %
%                                                      %
% Based on the paper:                                  %
% On the complexity of linear authorization logics     %
%                  in LiCS 2012                        %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subexp l lin.
subexp r lin.
subexp ll lin.
subexp gl unb.
subexp k1 unb.
subexp k2 unb.
subexp h1 lin.
subexp h2 lin.
subexp s1L lin.
subexp s1R lin.
subexp s2L lin.
subexp s2R lin.

subexprel r < l.
subexprel l < s1L.
subexprel l < s2L.
subexprel s1R < s1L.
subexprel s1R < s2L.
subexprel s2R < s1L.
subexprel s2R < s2L.
subexprel s1L < ll.
subexprel s2L < ll.
subexprel ll < h1.
subexprel ll < h2.
subexprel h1 < k1.
subexprel h2 < k2.
subexprel k1 < gl.
subexprel k2 < gl.

subexpctx l many ant.
subexpctx ll many ant.
subexpctx gl many ant.
subexpctx k1 many ant.
subexpctx k2 many ant.
subexpctx h1 many ant.
subexpctx h2 many ant.
subexpctx s1L many ant.
subexpctx s2L many ant.

subexpctx r single suc.
subexpctx s1R single suc.
subexpctx s2R single suc.

rules introduction.
% Tensor
not (lft (ten A B)) * ?[l] (lft A) | ?[l] (lft B).
not (rght (ten A B)) * ![l] ?[r] (rght A) * ![l] ?[r] (rght B).

% Implication
not (lft (lol A B)) * ![l] ?[r] (rght A) * ?[l] (lft B).
not (rght (lol A B)) * ![l] (?[l] (lft A) | ?[r] (rght B)).

% Says
not (lft (says p1 A)) * ![s1R] ?[l] (lft A).
not (rght (says p1 A)) * ![l] ?[r] (rght A).

not (lft (says p2 A)) * ![s2R] ?[l] (lft A).
not (rght (says p2 A)) * ![l] ?[r] (rght A).

% Has
not (lft (has p1 A)) * ?[l] (lft A).
not (rght (has p1 A)) * ![h1] ?[r] (rght A).

not (lft (has p2 A)) * ?[l] (lft A).
not (rght (has p2 A)) * ![h2] ?[r] (rght A).

% Knows

not (lft (knows p1 A)) * ?[l] (lft A).
not (rght (knows p1 A)) * ![k1] ?[r] (rght A).

not (lft (knows p2 A)) * ?[l] (lft A).
not (rght (knows p2 A)) * ![k2] ?[r] (rght A).

rules axiom.
% Init
not (lft A) * not (rght A).

rules cut.
% Cut
?[l] (lft A) * ![l] ?[r] (rght A).

rules structural.
% Structural rules for modals
not (lft (ten A B)) * ?[ll] (lft (ten A B)).
not (lft (lol A B)) * ?[ll] (lft (lol A B)).

not (lft (says p1 A)) * ?[s1L] (lft (says p1 A)).
not (lft (says p2 A)) * ?[s2L] (lft (says p2 A)).

not (rght (says p1 A)) * ?[s1R] (rght (says p1 A)).
not (rght (says p2 A)) * ?[s2R] (rght (says p2 A)).

not (lft (has p1 A)) * ?[h1] (lft (has p1 A)).
not (lft (has p2 A)) * ?[h2] (lft (has p2 A)).

not (lft (knows p1 A)) * ?[k1] (lft (knows p1 A)).
not (lft (knows p2 A)) * ?[k2] (lft (knows p2 A)).


