# Lane: nat-bitwise-assoc — same-fuel ASSOCIATIVITY for `land`/`lor`

<!-- plan-section: lane-status -->

**Your lane's block (`OPEN`, nat-bitwise-assoc, 2026-08-29).** Neither
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) nor
`F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) closed this session. What
landed instead is a real, tested, reusable piece of the infrastructure the
brief named as needed — `Nat.land_aux_le_left`/`Nat.land_le_left` — plus a
precise diagnosis of why the natural next step (a fuel-parametrized
`land_aux_assoc_of_fuel`, mirrored on `land_aux_comm_of_fuel`) does not go
through the way commutativity did, and what it would actually take.

**What landed and is kernel-checked.**

- `Nat.land_aux_le_left : ∀ fuel m n, Le (landAux fuel m n) m` — `landAux`
  never exceeds its LEFT operand, at ANY fuel, sufficient or not. This is
  exactly the bound the brief flagged: *"a nested `landAux fuel a b` in the
  fuel-recursion's ARGUMENT position is not obviously bounded by fuel, so
  the re-fuelling step may need a lemma saying `landAux fuel a b ≤ a`
  ... before the outer application's fuel is known sufficient."* No such
  lemma existed; this is it.
- `Nat.land_le_left : ∀ a b, Le (land a b) a` — the one-line `land`-headed
  corollary at `fuel := m := a` (defeq to `land a b`, no extra proof step,
  same shape as `land_aux_eq_land_of_le`'s corollary).

Both proved by ordinary induction on `fuel` alone
(`agree_by_fuel_induction`, no sufficient-fuel hypothesis needed at all,
unlike fuel-irrelevance): the `m = 0` and `n = 0` leaves close via
`land_aux_zero_left_any_fuel` and the literal-`n = 0` guard trick already
used throughout `rec_agreement.rs`; the "both positive" leaf bounds
`2*rec + bit` by `2*(m/2) + (m%2) = m` via `mul_le_mul_left`,
`add_le_add_left`/`add_le_add_right`, `le_trans`, and the executable
div/mod identity (`div_mod_exec`, extracted with `helpers::and_left`
following `division.rs`/`group.rs`'s `div_mod_unique` pattern — a NEW
private helper `bit_product_le_left` bounds `(m%2)*(n%2) ≤ m%2` via
`n%2 ≤ 1` monotonicity, since `mod_lt` + `le_of_lt_succ` give `n%2 ≤ 1`
directly and this route needed no `cases_mod_two` case split at all).

Detail moved to [`../notes/247-nat-bitwise-assoc.md`](../notes/247-nat-bitwise-assoc.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-bitwise-assoc | `Nat.land_aux_le_left`/`Nat.land_le_left` (the nested-value bound the assoc brief named); `land_assoc`/`lor_assoc` remain open — precise diagnosis + concrete next-steps recorded above for the next lane |
