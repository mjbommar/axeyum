# Notes: 227-nat-bitwise-general

Detail moved out of [`../status/227-nat-bitwise-general.md`](../status/227-nat-bitwise-general.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What was NOT attempted:** a universal `forall m n, bitwise and m n =
land m n` equivalence proof. `bitwiseAux`'s per-bit step and `landAux`'s
differ as FORMULAS (`bool_select_nat (f (beq a 1) (beq b 1)) 1 0` vs `mul a
b`) — they agree at every concrete `{0,1}` pair but are not definitionally
equal at symbolic `a, b`. Closing that needs an induction relating two
independently-built `Nat.rec` instances plus a `Nat.mod _ 2 in {0,1}`
case-split lemma this prelude does not yet carry. Real proof engineering,
correctly sized past one lane — the concrete specialization checks are the
strongest available substitute.

Full derivation: `bitwise.rs`'s module doc (front-loaded, not scattered).

Five new facts: `F:nat-bitwise-zero-left`, `F:nat-bitwise-zero-right`,
`F:nat-bitwise-and-eq-land-three-five`, `F:nat-bitwise-or-eq-lor-three-five`,
`F:nat-bitwise-xor-three-five`. Did not touch any `F:ml430-nat-bitwise-*`
mirror/held-out fact.

Measured: `nat_prelude::` test count 111 after this lane's one new test
function (all green, incl. `every_nat_declaration_is_checked_and_axiom_free`
and `every_promised_name_is_admitted_with_the_expected_kind`); declaration
count (`the_build_is_deterministic`'s pin, read off its own panic message,
never hand-counted) 83+421=504 before this lane, 85+426=511 after (+2
definitions `bitwiseAux`/`bitwise`, +5 theorems); `axiom_footprint` for every
new declaration is `[]`; `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`
unchanged. `cargo fmt --edition 2024` (per-file,
not workspace-wide) and `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings` both clean.

Kernel rejected one thing during construction: a borrow-checker error, not a
kernel rejection (`d.zero()` called while `d` was already mutably borrowed
inside a nested `bitwise(d, ..., d.zero())` call) — flattened into a
sequential `let`, exactly the "flatten nested `d.foo(..., d.bar())`" gotcha.
No `add_declaration` rejection occurred; every construction was accepted on
the first attempt once it type-checked in Rust.
