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

Detail moved to [`../notes/227-nat-bitwise-general.md`](../notes/227-nat-bitwise-general.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-bitwise-general | landed `Nat.bitwise`, the general form `land`/`lor`/`ldiff` specialize; 5 new facts |
