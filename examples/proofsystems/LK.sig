% Object logic connectives' types

type imp form -> form -> form.
type and form -> form -> form.
type or  form -> form -> form.
type false  form.
type true form.

type forall (term -> form) -> form.
type exists (term -> form) -> form.
