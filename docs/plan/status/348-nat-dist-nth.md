# Lane: nat-dist-nth — declare `Nat.dist`/`Nat.nth` to unblock nursery draw 6

<!-- plan-section: lane-status -->

**Both declared; the screen now admits both modules at their predicted
counts.** ADR-0645/draw-6's notes measured the unblock as declaring two
kernel constants (`Nat.dist`, `Nat.nth`) so the R9 name screen admits
`Mathlib.Data.Nat.Dist` (18 rows) and `Mathlib.Data.Nat.Nth` (11 rows) —
exactly the two held-out-safe families a draw needs. Both landed.

- **`Nat.dist n m := add (sub n m) (sub m n)`** (`nat_prelude/dist.rs`) is
  Mathlib's own definition over our `sub`/`add` — same statement, so a later
  `ml430` mirror flip is honest. Landed with 7 theorems (`dist_comm`,
  `dist_self`, `dist_eq_sub_of_le[_right]`, `dist_zero_right`/`_left`,
  `dist_succ_succ`), each proved from lemmas already in the prelude
  (`sub_eq_zero_of_le`, `zero_le`, `sub_zero`, `add_zero`/`zero_add`,
  `add_comm`, `succ_sub_succ`) — no new induction needed.
- **`Nat.nth`** (`nat_prelude/nth.rs`) is deliberately NOT Mathlib's
  construction — Mathlib's is noncomputable, classically case-splitting on
  `Set.Finite (setOf p)`, and this kernel has neither `Set`/`Finset` nor
  `Classical.choice`. Built as an honest substitution in `Nat.minFac`'s
  style: `Nat.nthAux (dec : Nat -> Bool) (fuel k n : Nat) : Nat`, a
  fuel-bounded search over a decidable `Bool` predicate, using the same
  fuel/`Bool.rec` device `Nat.beq`/`Nat.land`/`Nat.sumRange` already use,
  generalized to two accumulators. `Nat.nth dec bound n := nthAux dec bound
  0 n`. Type differs from Mathlib's `(Nat -> Prop) -> Nat -> Nat`, so any
  `ml430` mirror against it stays open — documented in `nth.rs`'s module
  doc, following the `minFac`/`multichoose` precedent in `CLAUDE.md`.

Detail moved to [`../notes/348-nat-dist-nth.md`](../notes/348-nat-dist-nth.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | nat-dist-nth | `Nat.dist` (def + 7 theorems, `nat_prelude/dist.rs`) and `Nat.nth`/`Nat.nthAux` (fuel-bounded, non-mirroring, `nat_prelude/nth.rs`) declared axiom-free; three evaluation-test functions added; kernel-environment-snapshot and refill-headroom regenerated, confirming the screen admits `Mathlib.Data.Nat.Dist` (18) / `Mathlib.Data.Nat.Nth` (11) exactly as ADR-0645 predicted |
