% Object logic connectives' types

type imp form -> form -> form.
type and form -> form -> form.
type or  form -> form -> form.
type myNot form -> form.

type forall (term -> form) -> form.
type exists (term -> form) -> form.
