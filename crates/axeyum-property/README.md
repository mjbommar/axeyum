# axeyum-property

Typed prove-or-counterexample SDK over the Axeyum IR and evidence APIs.

This crate is intentionally thin: it owns no solver logic. It gives frontends a
typed `Bool` / `Bv<W>` / `Int` builder, records declared scalar symbols in a
deterministic counterexample-objective order, and delegates proof attempts to
`axeyum-solver`'s replay-checked evidence functions.

The `Symbolic` trait gives typed declaration/lifting for scalar inputs, small
tuples, and derived structs. Unsigned fixed-width Rust integers map to BV terms;
signed fixed-width Rust integers (`i8`/`i16`/`i32`/`i64`) map to two's-complement
BV terms and signed-order minimized counterexamples; `i128` maps to mathematical
Int. `Property::symbolic_struct` is the macro-free named-field builder
underneath `#[derive(axeyum_property::Symbolic)]`, so frontends can choose
either explicit builder code or a derive when their input shape is a Rust struct.

Disproving models can be extracted as deterministic `Counterexample` bindings
and rendered as native Rust scalar `let` bindings or a `#[test]` skeleton with
caller-provided replay code. Direct named and tuple symbolic bundles can also
render Rust aggregate initializer statements over those scalar bindings; nested
or domain-specific replay remains caller-owned.
