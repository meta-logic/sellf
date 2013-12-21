% ICL

rules introduction.
subexp r lin.

%VN: Not sure which system is this and therefore did not add the subexpctx relations.

% Implication
(not (lft  (imp A B))) * ((bang ([r]? (rght A))) *  (? (lft B))).
(not (rght (imp A B))) * (bang ((? (lft A)) | ([r]? (rght B)))).

% Conjunction
(not (lft  (and A B))) * ((? (lft A))  | (? (lft  B))).
(not (rght (and A B))) * ((bang ([r]? (rght A))) * bang(([r]? (rght B)))).

% Disjunction
(not (lft  (or A B))) * ((? (lft  A)) & (? (lft  B))).
(not (rght (or A B))) * ((bang ([r]? (rght A))) + (bang ([r]? (rght B)))).

% True
(not (rght tt)) * top.
(not (lft  tt)) * zero.

% False : zz (zero)
(not (lft  zz)) * top.
(not (rght zz)) * zero.

% False : bttm (bottom)
(not (lft  bttm)) * one.
(not (rght bttm)) * bot.

rules axiom.
% Init
((not (lft A)) * (not (rght A))).

rules cut.
% Cut
((? (lft A))   * (bang  ([r]? (rght A)))).
((bang  (? (lft A))) *  ([r]? (rght A))).
