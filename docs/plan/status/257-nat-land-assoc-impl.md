# Lane: nat-land-assoc-impl -- `land_aux_eq_zero_of_left_eq_zero` landed, a fully-worked implementation-ready derivation for `land_aux_assoc_of_fuel`

<!-- plan-section: lane-status -->

**Your lane's block (`OPEN`, nat-land-assoc-impl, 2026-08-29).** This lane
executed `docs/plan/status/252-nat-assoc-dichotomy.md`'s traced-but-unbuilt
theorem, verified the plan's own case tree against the actual guard
argument order and helper signatures, and landed it with tests. Neither
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) nor
`F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) closed this session --
this is the fourth lane to stop short of `land_assoc` itself, but the
first to leave `land_aux_assoc_of_fuel` (the theorem that actually blocks
it) with a complete, line-by-line, implementation-ready derivation rather
than a sketch.

## What landed and is kernel-checked

**`Nat.land_aux_eq_zero_of_left_eq_zero : ∀ fuel a b c,
Eq (landAux fuel a b) 0 → Eq (landAux fuel a (landAux fuel b c)) 0`**
(`rec_agreement.rs`), exactly the statement `252` traced. Built via
`agree_by_double_fuel_induction` (its "two independently chosen fuels"
design reused here for three plain value arguments plus one fuel --
nothing in that helper actually requires the third generalized argument
to BE a second fuel, only that it be universally quantified alongside the
induction variable, which is exactly what this statement needs).

**Every step of `252`'s plan held, verified by compiling and running it,
not by re-reading the prose:**

Detail moved to [`../notes/257-nat-land-assoc-impl.md`](../notes/257-nat-land-assoc-impl.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-land-assoc-impl | `Nat.land_aux_eq_zero_of_left_eq_zero` (the propagation lemma `252` traced but did not build); a complete, implementation-ready, guard-slot-verified derivation for `land_aux_assoc_of_fuel`'s 4-leaf structure (corrected leaf split order to c,b,a; the hard leaf's double `div_mod_unique` reconstruction closing via `ih` + `mul_assoc` alone, no new lemmas); `land_assoc`'s fuel-bookkeeping shape (mechanical, `land_comm` one slot wider); `land_assoc`/`lor_assoc` remain open |
