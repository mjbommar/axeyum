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

Expression construction stays fallible and arena-backed: typed handles expose
explicit builder methods such as `add`, `ule`, and `equals`, while
`Property::all` / `Property::any` fold Boolean conditions without hiding
construction errors.

Proof calls can also be packaged as `ProofCertificate`: the ordinary
`ProofOutcome` still carries the checked Axeyum `EvidenceReport`, and proved
queries get a best-effort standalone Lean module when the refutation fragment is
covered by reconstruction. `ProofCertificate::summary()` turns that raw evidence
into stable frontend-facing route, trust-ledger, and Lean reconstruction fields.

Disproving models can be extracted as deterministic `Counterexample` bindings
and rendered as native Rust scalar `let` bindings or a `#[test]` skeleton with
caller-provided setup and replay code. Direct named and tuple symbolic bundles
can also render Rust aggregate initializer statements over those scalar
bindings. Nested or domain-specific replay remains caller-owned, but frontends
can explicitly compose nested aggregate initializers by rendering the inner value
first, passing a field expression such as `("limits", "transfer_limits")` to
`render_rust_named_struct_let_with_fields`, and inserting those setup snippets
before the replay assertion with `render_rust_test_with_setup`.
