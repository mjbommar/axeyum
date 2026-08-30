# Lane: nat-xor-ne-zero — `Nat.xor_ne_zero_iff`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.xor_ne_zero_iff landed, axiom-free; F:ml430-nat-lt-xor-cases-c43a1e85 stays open -- all four piece-4 sub-targets now landed, three larger pieces remain)`, nat-xor-ne-zero, 2026-08-29).**

## The exact statement

Read directly from the pinned Batteries checkout
(`/data0/axeyum/lean-import-toolchain/mathlib4/.lake/packages/batteries`,
commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`),
`Batteries/Data/Nat/Bitwise/Lemmas.lean:68`:

```lean
theorem xor_ne_zero_iff {x y : Nat} : x ^^^ y ≠ 0 ↔ x ≠ y := by simp
```

Confirms the "Lean core, not Mathlib-authored" reading `docs/plan/status/264-nat-xor-algebra.md`
and `docs/plan/status/268-nat-xor-cancel.md` already established for its three
siblings (`xor_assoc`, `xor_xor_cancel_left`, `xor_xor_cancel_right`, all also
in the same Batteries file, lines 51-60). No `ml430` fact exists to flip, so
this lands as a new local fact, `F:nat-xor-ne-zero-iff`.

## What landed

`Nat.xor_ne_zero_iff : ∀ a b, Iff (Not (Eq (xor a b) 0)) (Not (Eq a b))`,
admitted axiom-free on the first successful attempt (after fixing a compile
error, no `TypeMismatch` from the kernel at all — this route never poisoned
the shared prelude build), in `crates/axeyum-lean-kernel/src/nat_prelude/xor_algebra.rs`.

Detail moved to [`../notes/270-nat-xor-ne-zero.md`](../notes/270-nat-xor-ne-zero.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-xor-ne-zero | Landed `Nat.xor_ne_zero_iff` (piece 4's fourth and last sub-target toward `F:ml430-nat-lt-xor-cases-c43a1e85`), read directly from the pinned Batteries checkout (`Batteries/Data/Nat/Bitwise/Lemmas.lean:68`, confirming the "Lean core, not Mathlib" reading two prior lanes established for its siblings); built via `mt` (modus tollens, previously declared but unused in this prelude) applied twice rather than an `Iff`-of-`Eq` intermediate; the `mpr` direction confirmed NOT needing the cancel lemmas per the prior lane's own handoff, via a new per-bit lemma reusing `round_trip_le_one`; the `mp` direction via a new `Nat.xor_self`-shaped argument; every route confirmed by Python truth-table simulation before writing Rust, and no `false_true_elim` needed anywhere; new fact `F:nat-xor-ne-zero-iff`, axiom-free; all four of piece 4's sub-targets now landed, leaving 2 of the original 4 larger pieces (`lt_of_testBit`, `xor_trichotomy` composition) plus `lt_xor_cases` itself |
