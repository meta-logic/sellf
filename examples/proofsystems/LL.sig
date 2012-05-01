% Object logic connectives' types

type lolli form -> form -> form.
type with form -> form -> form.
type tensor  form -> form -> form.
type oplus form -> form -> form.
type par  form -> form -> form.
type lbang form -> form -> form.
type lquest  form -> form -> form.
type lbot  form.
type lone form.
type lzero form.
type ltop form.

type forall (term -> form) -> form.
type exists (term -> form) -> form.
