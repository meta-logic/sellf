% Object logic connectives' type

kind label type.

type and  form -> form -> form.
type or   form -> form -> form.
type imp  form -> form -> form.
type nec  form -> form. % Box
type poss form -> form. % Diamond

type rel label -> label -> o.
type pair label -> form -> form.

