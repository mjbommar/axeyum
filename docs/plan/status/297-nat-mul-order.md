# Lane: nat-mul-order — `Nat` ordering under multiplication and division

<!-- plan-section: lane-status -->

**Closed all five targets** (`DONE`, nat-mul-order, 2026-08-29): `2f9162c98`.
New file `crates/axeyum-lean-kernel/src/nat_prelude/mul_order_lemmas.rs`
declares `Nat.mul_lt_mul_left`, `Nat.mul_lt_mul_right`,
`Nat.lt_of_mul_lt_mul_left`, `Nat.lt_of_mul_lt_mul_right`,
`Nat.div_lt_of_lt_mul`, dispatched last in `nat_prelude.rs`'s build order.

Step 0 (`nat_theorem_inventory --release`) confirmed all five absent under any
rendered type before writing any proof — no duplicate work.

The two `lt_of_mul_lt_mul_*` cancellation lemmas carry **no** positivity
hypothesis, matching the pinned Mathlib v4.30 source exactly (`a*b < a*c` at
`a = 0` is vacuous, so requiring `0 < a` would only be a weaker true
statement). Proved by contradiction via `lt_or_ge` + `mul_le_mul_left`/
`le_trans`/`lt_irrefl`, no `Nat.rec` case split. `mul_lt_mul_left`/`right` are
the matching `Iff` (`mp` = the cancellation lemma, `mpr` = a positive-monotone
core). `div_lt_of_lt_mul` is the one real case split, on the divisor
(`cases_zero_succ`): `n = 0` is absurd via `zero_mul`/`not_lt_zero`; `n = succ
n'` is `div_mod_lt_mul_iff`'s forward direction fed the `div_mod_exec`
witness.

**One real bug, found by bisection.** A first draft of
`mul_lt_mul_pos_right_core` assumed `mul(succ b, a) = add(mul b a, a)` held BY
REFL — copying the pattern that genuinely does hold in the *left* core
(`mul_succ`, a refl-provable defining equation, since `Nat.mul` recurses on
its right argument). The left-successor form (`succ_mul`) is instead a real
theorem under "multiplicative theorems", proved by induction. This poisoned
the whole prelude build (`TypeMismatch` across all 169 `nat_prelude::` tests);
bisected by toggling the three new `declare_*` dispatch calls one at a time
against `nat_theorem_inventory`, then further by disabling the second
`d.theorem` call inside `declare_mul_lt_mul_iff`. Fixed with an explicit
`transport` along `succ_mul`.

`theorem_names`/`the_build_is_deterministic` pin: `93 + 538` → `93 + 543`
(new value taken from the panic's own mismatch, not hand-incremented). New
test `mul_order_lemmas_apply_at_concrete_and_boundary_instances` applies all
five at concrete numerals, including the boundary `a = 1` (smallest value
satisfying `0 < a`) and `n = 1` (smallest divisor taking the `succ`
case-split branch), plus `7 < 2*4` at the `div_lt_of_lt_mul` boundary.
Confirmed "1 passed", never "0 filtered out".

Detail moved to [`../notes/297-nat-mul-order.md`](../notes/297-nat-mul-order.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `2f9162c98` | Five `Nat` mul/div order mirrors (`mul_lt_mul_left`/`right`, `lt_of_mul_lt_mul_left`/`right`, `div_lt_of_lt_mul`) in a new `nat_prelude/mul_order_lemmas.rs`; five facts flipped to `proved`. |
