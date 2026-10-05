# Lane: nat-bitwise-general — land `Nat.bitwise`, the general form `land`/`lor`/`ldiff` specialize

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-bitwise-general, 2026-08-28).** `Nat.bitwise`
landed: `crates/axeyum-lean-kernel/src/nat_prelude/bitwise.rs` (new file),
wired into `nat_prelude.rs` (mod/use/fields/initializers/call site) and
`nat_prelude/nat_prelude_tests.rs`.

**The two earlier declines do NOT hold anymore, and here is the precise
reading of what "mismatched-length base cases" costs.** Both prior lanes
declined citing "a `Bool -> Bool -> Bool` function threaded through
mismatched-length base cases" as too big for one lane. That threading turns
out to be small and mechanical once `land`/`lor`/`ldiff` exist: the general
base case answers "does the fuel operand carry this operator's absorbing
zero?" — a question with no fixed answer for a general `f` — by evaluating
`f` at the two boundary `Bool` literals (`f false true`, `f true false`) and
gating with the SAME `bool_select_nat` combinator `land`/`lor`/`ldiff` already
build for their own zero-guards. No new primitive, no new height dependency.
The per-bit step needs one genuinely new piece (`Nat.beq _ 1` to get a `Bool`
out of each `{0,1}` bit, apply `f`, `bool_select_nat` back to `{0,1}`), also
mechanical.

**Outcome 1 landed** (of the brief's three ranked outcomes): `Nat.bitwise`
+ `Nat.bitwiseAux` (fuel-recursive, `f` threaded through every closure), two
`f`-general boundary theorems (`bitwise_zero_left` refl, `bitwise_zero_right`
induction — the ONE genuinely new proof-content wrinkle: the base case needs
a small `Bool`-case-split helper, `bool_select_same`, that the three
specializations' own zero-right theorems never needed, because their base
cases were syntactically identical for a fixed `f`), and three concrete
specialization checks (`bitwise and_fn 3 5 = land 3 5`, `bitwise or_fn 3 5 =
lor 3 5`, both refl against the ACTUAL sibling declaration; `bitwise xor_fn
3 5 = 6` against a hand-computed numeral, no XOR sibling exists).

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

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bitwise-general | landed `Nat.bitwise`, the general form `land`/`lor`/`ldiff` specialize; 5 new facts |
