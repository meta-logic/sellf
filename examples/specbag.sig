kind prog type.

%% Commands

type load           T -> tsub -> prog -> prog.
type unload         tsub -> (T -> prog) -> prog.
type unload2        tsub -> (T -> T -> prog) -> prog.
type while          o -> (prog -> prog) -> prog -> prog.
type loop           tsub -> (T -> prog -> prog) -> prog -> prog.
type loop2          tsub -> (T -> T -> prog -> prog) -> prog -> prog.
type alt            prog -> prog -> prog.
type if             o -> (prog -> prog) -> (prog -> prog) -> prog -> prog.
type if_is_empty    tsub -> (prog -> prog) -> (prog -> prog) -> prog -> prog.
type new            tsub -> prog -> prog.
type done           prog.

