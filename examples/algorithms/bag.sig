kind cond type.

type load1 int -> tsub -> o -> o.
type load2 int -> int -> tsub -> o -> o.
type unload1 int -> tsub -> (int -> o) -> o.
type unload2 int -> int -> tsub -> (int -> int -> o) -> o.
type while cond -> (o -> o) -> o -> o.
type loop1 tsub -> (int -> o -> o) -> o -> o.
type loop2 tsub -> (int -> int -> o -> o) -> o -> o.
type paral o -> o -> o.
type if cond -> o -> o.
type new (tsub -> o) -> o.

type tup1 int -> tsub -> o.
type tup2 int -> int -> tsub -> o.
type eq int -> int -> cond.
type neq int -> int -> cond.
type less int -> int -> cond.
type grt int -> int -> cond.
type leq int -> int -> cond.
type geq int -> int -> cond.
type isEmpty tsub -> cond.