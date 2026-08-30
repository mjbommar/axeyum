# Lane: choose-backlog — close the Nat.choose import backlog (5 facts)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, choose-backlog, 2026-08-28).** All five targeted
facts landed as axiom-free kernel-lean proofs in
`crates/axeyum-lean-kernel/src/nat_prelude/choose.rs`:
`Nat.choose_one_right`, `Nat.choose_eq_zero_of_lt`, `Nat.choose_ne_zero`,
`Nat.choose_le_succ`, `Nat.choose_symm_of_eq_add`. `nat_prelude::` --lib went
94 -> 95 passed, 0 failed.

One real bug found and fixed along the way: `choose_le_succ`'s `c = 0` base
case assumed `choose(a, 0)` reduces to `1` by defeq for a SYMBOLIC `a` — it
does not (the outer recursor is stuck on a non-constructor first argument;
only `choose(succ a, 0)` reduces regardless of `a`). Caught by the full
`nat_prelude::` sweep (a single-test run against only that one theorem's own
test passed, then the full sweep failed with `TypeMismatch` across 95 tests
because the shared prelude build itself fails). Fixed by routing through
`choose_zero_right(a)` + `le_refl` instead of assuming defeq. Bisected by
toggling each of the five `declare_choose_*` calls in `declare_choose_all`
one at a time against the single fast test
`choose_computes_and_symm_holds_at_a_concrete_point`.

Also updated (both environment-derived, not hand-maintained lists per the
project's "every X must derive from the authority" rule):
`every_nat_declaration_is_checked_and_axiom_free`'s `theorem_names` list, and
`the_build_is_deterministic`'s rendered-declaration count pin
(`65+322` -> `65+327`, re-derived from the test's own failure message, not
guessed).

Fact ledger: all five `F:ml430-nat-choose-*` facts flipped `open` -> `proved`,
evidence mirrors `F:nat-choose-symm`'s pattern (`nat_theorem_inventory`
grep-count + `nat_axiom_inventory --require-axiom-free nat`), both checker
commands verified to discriminate (positive control passes, a fabricated
theorem name fails). `python3 scripts/validate-facts.py`: 1867 facts, 0
errors.

Nothing found already existing that the brief implied was missing — the
`choose.rs`/`binomial.rs` family cited in the brief (`declare_choose`,
`declare_choose_equations`, `declare_choose_self`, `declare_choose_symm`,
`sum_choose_row`, `choose_le_two_pow`, `succ_mul_choose_eq`) was exactly as
described, and none of the five target names existed anywhere in the tree
before this lane (grepped both spellings).

Detail moved to [`../notes/183-choose-backlog.md`](../notes/183-choose-backlog.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | choose-backlog | 5 Nat.choose theorems (one_right, eq_zero_of_lt, ne_zero, le_succ, symm_of_eq_add) + 5 facts flipped to proved; fixed a false defeq assumption in choose_le_succ's base case |
