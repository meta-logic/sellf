%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                           %
% SELLF specification for Linear Logic      %
%                                           %
% Giselle Machado Reis - 2011               %
%                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% THIS IS NOT CORRECT NOR COMPLETE

subexp slin lin. % holds linear formulas
subexp sunb unb. % holds unbounded formulas

%% Specification of Linear Logic (one-sided version)

rght (tensor a b) := ([slin]? (rght a)) , ([slin]? (rght b)).
rght (plus c d) := ([slin]? (rght c)) ; ([slin]? (rght d)).
%rght (with e f) := ([slin]? (rght e)) & ([slin]? (rght f)).
%rght (par g h) := ([slin]? (rght g)) | ([slin]? (rght h)).
%rght (quest i) := ([sunb]? (rght i)).
%rght (bng j) := ([sunb]bang ([slin]? (rght j))).
%rght (lone) := one.
%rght (ltop) := top.
%rght (bottom) := bot.

