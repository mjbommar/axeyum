# Lane: nat-xor-algebra — `Nat.xor_assoc`, `Nat.xor_xor_cancel`, `Nat.xor_ne_zero_iff`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.eq_of_testBit_eq + Nat.xor_assoc landed; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, 2 pieces remain with an exact route)`, nat-xor-algebra, 2026-08-29).**

## What landed

Piece 4 of the 4 pieces `docs/plan/status/260-nat-lt-xor-cases.md` named as
blocking `F:ml430-nat-lt-xor-cases-c43a1e85` was itself four sub-targets
(Mathlib's `xor_trichotomy` proof composes `xor_assoc`,
`xor_xor_cancel_left`, `xor_xor_cancel_right`, `xor_ne_zero_iff`). This lane
lands **one of those four in full, plus the general infrastructure the other
three now need only a small amount more to close**:

New file `crates/axeyum-lean-kernel/src/nat_prelude/xor_algebra.rs`:

```
Nat.eq_of_testBit_eq : ∀ m n, (∀ i, Eq (testBit m i) (testBit n i)) → Eq m n
Nat.xor_assoc        : ∀ a b c, Eq (xor (xor a b) c) (xor a (xor b c))
```

Both admitted axiom-free, both with concrete-discriminating + symbolic
evaluation tests, both registered as new local facts (`F:nat-eq-of-testbit-eq`,
`F:nat-xor-assoc`; neither has an `ml430` mirror — see "Codomain / mirror
check" below).

Detail moved to [`../notes/264-nat-xor-algebra.md`](../notes/264-nat-xor-algebra.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-xor-algebra | Landed `Nat.eq_of_testBit_eq` (new general "same bits imply the same number" extensionality lemma, generalizing `Nat.zero_of_testBit_eq_zero`) and `Nat.xor_assoc` (via `Nat.testBit_xor` applied twice per side plus the new extensionality lemma, using a from-scratch `xor_bit` Boolean-algebra toolkit — `digitize`/`cases_bool`/`beq_digitize_one`/`bool_xor_assoc`/`congr_bool_to_nat`/`xor_bit_assoc` — confirmed by Python truth-table simulation before any Rust; a real `TypeMismatch` bug was isolated via a throwaway probe module rather than by reading a poisoned 147-test failure list), new file `nat_prelude/xor_algebra.rs`, both axiom-free with concrete+symbolic evidence, both new local facts (no `ml430` mirrors: read directly at the pinned Mathlib commit, `xor_assoc`/`xor_xor_cancel`/`xor_ne_zero_iff` are Lean4 core lemmas cited but not defined in `Bitwise.lean`); `F:ml430-nat-lt-xor-cases-c43a1e85` stays `open` — `Nat.xor_xor_cancel_left`/`_right` and `Nat.xor_ne_zero_iff` remain, with an exact diagnosed route through a `y ∈ {0,1}` round-trip lemma this lane discovered is needed (the natural "cancel" identity is FALSE for general `y : Nat`, unlike `xor_assoc`'s identity which stays at the `digitize`/`Bool` level throughout) |
