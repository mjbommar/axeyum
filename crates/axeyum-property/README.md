# axeyum-property

Typed prove-or-counterexample SDK over the Axeyum IR and evidence APIs.

This crate is intentionally thin: it owns no solver logic. It gives frontends a
typed `Bool` / `Bv<W>` / `Int` builder, records declared scalar symbols in a
deterministic counterexample-objective order, and delegates proof attempts to
`axeyum-solver`'s replay-checked evidence functions.

The `Symbolic` trait gives typed declaration/lifting for scalar inputs, small
tuples, and derived structs. `Property::symbolic_struct` is the macro-free
named-field builder underneath `#[derive(axeyum_property::Symbolic)]`, so
frontends can choose either explicit builder code or a derive when their input
shape is a Rust struct.

Disproving models can be extracted as deterministic `Counterexample` bindings
and rendered as native Rust scalar `let` bindings or a `#[test]` skeleton with
caller-provided replay code.
