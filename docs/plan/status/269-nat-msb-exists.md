# Lane: nat-msb-exists -- `Nat.exists_most_significant_bit` (piece 2 of 4)

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL (cheap half landed as F:nat-testbit-eq-zero-of-lt; hard half NOT built, precise diagnosis below)`, nat-msb-exists, 2026-08-29).**

## What landed

**`Nat.testBit_eq_zero_of_lt : forall n j, Lt n (pow 2 j) -> Eq (testBit n
j) zero`** (`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`) --
admitted, axiom-free, on the FIRST real kernel-check attempt (only a
`clippy::doc_markdown` nested-backticks nit needed fixing afterward).
Registered as `F:nat-testbit-eq-zero-of-lt`. This is exactly the "cheap
half" `docs/plan/status/265-nat-msb-order.md` diagnosed but did not build:
above a value's own magnitude bound, every bit reads zero.

Route: `value_eq_sum_range` (already in `bit_order.rs`, private) at
`bound := j` gives `sumRange f_n j = n` directly from the hypothesis (via
`mod_eq_self_of_lt`); the same helper at `bound := succ j` needs
`n < pow 2 (succ j)`, obtained via `pow_j <= pow_j + pow_j = mul pow_j 2`
(`= pow 2 (succ j)` by `pow_succ`/`refl`), bridged with `le_add_right` +
`double_eq` (the exact same bridge `Nat.self_lt_two_pow_add`'s induction
step already uses) composed with `lt_of_lt_of_le`. `sum_range_succ` then
forces `n = add n (f_n j)` (substituting the first equation), so
`add_left_cancel` against `n = add n 0` collapses `f_n j` to `0`; since
`f_n j` is literally `mul (testBit n j) (pow 2 j)` up to beta,
`mul_eq_zero` splits into `testBit n j = 0` or `pow 2 j = 0`, and
`pow_pos` + `lt_irrefl` + `Or.resolve_right` rule out the second
disjunct. No new general arithmetic lemma was needed beyond what
`self_lt_two_pow_add`'s own proof already established the technique for.

## Codomain verdict for the Mathlib mirror

Detail moved to [`../notes/269-nat-msb-exists.md`](../notes/269-nat-msb-exists.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-msb-exists | Landed `Nat.testBit_eq_zero_of_lt` (the "cheap half" of `exists_most_significant_bit`, piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`) as the new local fact `F:nat-testbit-eq-zero-of-lt` (Mathlib's `Nat.testBit_eq_false_of_lt` is Bool-valued; ours stays Nat-valued), admitted axiom-free on the first real kernel-check attempt via `value_eq_sum_range` at `bound := j` and `bound := succ j` plus `sum_range_succ`/`add_left_cancel`/`mul_eq_zero`; the "highest bit is set" hard half remains open and is re-confirmed (not newly discovered) to need either a new `size`-recursion lemma relating `size n` to `size (n/2)` or an independent ~150-line bottom-up `msbAux`-fuel construction |
