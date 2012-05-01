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

rules introduction.
% Tensor
(not (lft (ten A B))) * ([l]? (lft A)) | ([l]? (lft B)).
(not (rght (ten A B))) * ( ([l]bang ([r]? (rght A))) * ( [l]bang ([r]? (rght B)))).

% Implication
(not (lft (lol A B))) * (([l]bang ([r]? (rght A))) * ([l]? (lft B))).
(not (rght (lol A B))) * ([l]bang (([l]? (lft A)) | ([r]? (rght B)))).

% Says
(not (lft (says p1 A))) * [s1R]bang ([l]? (lft A)).
(not (rght (says p1 A))) * [l]bang ([r]? (rght A)).

(not (lft (says p2 A))) * [s2R]bang ([l]? (lft A)).
(not (rght (says p2 A))) * [l]bang ([r]? (rght A)).

% Has
(not (lft (has p1 A))) * ([l]? (lft A)).
(not (rght (has p1 A))) * [h1]bang ([r]? (rght A)).

(not (lft (has p2 A))) * ([l]? (lft A)).
(not (rght (has p2 A))) * [h2]bang ([r]? (rght A)).

% Knows

(not (lft (knows p1 A))) * ([l]? (lft A)).
(not (rght (knows p1 A))) * [k1]bang ([r]? (rght A)).

(not (lft (knows p2 A))) * ([l]? (lft A)).
(not (rght (knows p2 A))) * [k2]bang ([r]? (rght A)).

rules axiom.
% Init
sigma \A ((not (lft A)) * (not (rght A))).

rules cut.
% Cut
sigma \A (([l]? (lft A)) * ([l]bang ([r]? (rght A)))).

rules structural.
% Structural rules for modals
sigma \A ((not (lft (ten A B))) * ([ll]? (lft (ten A B)))).
sigma \A ((not (lft (lol A B))) * ([ll]? (lft (lol A B)))).

sigma \A ((not (lft (says p1 A))) * ([s1L]? (lft (says p1 A)))).
sigma \A ((not (lft (says p2 A))) * ([s2L]? (lft (says p2 A)))).

sigma \A ((not (rght (says p1 A))) * ([s1R]? (rght (says p1 A)))).
sigma \A ((not (rght (says p2 A))) * ([s2R]? (rght (says p2 A)))).

sigma \A ((not (lft (has p1 A))) * ([h1]? (lft (has p1 A)))).
sigma \A ((not (lft (has p2 A))) * ([h2]? (lft (has p2 A)))).

sigma \A ((not (lft (knows p1 A))) * ([k1]? (lft (knows p1 A)))).
sigma \A ((not (lft (knows p2 A))) * ([k2]? (lft (knows p2 A)))).


