# axeyum-property

Typed prove-or-counterexample SDK over the Axeyum IR and evidence APIs.

This crate is intentionally thin: it owns no solver logic. It gives frontends a
typed `Bool` / `Bv<W>` / `Int` builder, records declared scalar symbols in a
deterministic counterexample-objective order, and delegates proof attempts to
`axeyum-solver`'s replay-checked evidence functions.

The `Symbolic` trait gives macro-free typed declaration/lifting for scalar
inputs and small tuples today; a derive macro for named structs is a later layer.

Disproving models can be extracted as deterministic `Counterexample` bindings
and rendered as native Rust scalar `let` bindings or a `#[test]` skeleton with
caller-provided replay code.
