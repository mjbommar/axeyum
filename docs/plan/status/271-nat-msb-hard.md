# Lane: nat-msb-hard -- `Nat.exists_most_significant_bit`, the hard half

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (F:nat-exists-most-significant-bit landed, admitted axiom-free on the first attempt)`, nat-msb-hard, 2026-08-29).**

## What landed

**`Nat.msb_exists_of_le_fuel : ∀ fuel n, Le n fuel → Not (Eq n zero) →
∃ i, And (Eq (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j) zero)`**
(fuel-generalized) and **`Nat.exists_most_significant_bit`** (the `fuel :=
n` specialization via `le_refl`), both in
`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`. Both admitted,
axiom-free, on the FIRST real kernel-check attempt -- the entire
construction (~450 lines) compiled and kernel-checked without a single
`TypeMismatch` iteration. Registered as `F:nat-exists-most-significant-bit`.

This is the "hard half" both `docs/plan/status/265-nat-msb-order.md` and
`docs/plan/status/269-nat-msb-exists.md` diagnosed but did not build: the
highest bit really IS set, not just that no higher bit is needed.

## Does `Nat.size` shortcut this? No -- re-confirmed, not newly discovered

Re-read `binary.rs`'s `size` addendum before writing anything, per the
brief. `Nat.size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux
fuel n))` is proved by induction on `fuel` generalized over `n`, and it is
an UPPER bound only. It has no lemma relating `size n` to `size (n/2)` when
`n != 0` -- deliberately, since generalizing over ANY sufficient fuel is
exactly what let that proof avoid needing that relation. The route below
does not touch `size` at all; it is an independent fuel-recursion.

## Route taken: (b), an independent fuel-recursion -- NOT a `size`-recursion lemma

Detail moved to [`../notes/271-nat-msb-hard.md`](../notes/271-nat-msb-hard.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-msb-hard | Landed `Nat.msb_exists_of_le_fuel` (fuel-generalized) and `Nat.exists_most_significant_bit` (the hard half of piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`: the highest bit really IS set, not just that no higher bit is needed) as the new local fact `F:nat-exists-most-significant-bit` (Mathlib's `testBit` is Bool-valued; ours stays Nat-valued), admitted axiom-free on the first real kernel-check attempt via an independent fuel/half-recursion (same `div_mod_lt_mul_iff`+`n_lt_mul_two` bound `declare_size_aux_lt_pow` uses, split on `beq half zero` mirroring Mathlib's `Nat.binaryRec`) rather than a `size`-recursion lemma -- `Nat.size` re-confirmed to not shortcut this, since its own development only ever proves an upper bound; pieces 1-3 of the 4 pieces blocking `lt_xor_cases` are now all DONE, piece 4's status needs a fresh check before dispatching the final composition |
