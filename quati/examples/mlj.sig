% Object logic connectives' type

type imp form -> form -> form.
type and form -> form -> form.
type or  form -> form -> form.

type forall (term -> form) -> form.
type exists (term -> form) -> form.

type bottom form.

