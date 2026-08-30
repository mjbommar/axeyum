# 374 — Euler's theorem (a^phi(n) = 1 mod n)

<!-- plan-section: lane-status -->

Status: IN PROGRESS (WIP commit -- investigation done, construction starting).

## ADR-0716's claim, checked

ADR-0716 says both residue-permutation ingredients are landed
(`Int.euler_unit_coprime`, `Int.euler_unit_injective`) and treats the
theorem as within reach. Verified both exist and are correctly stated
(`int_prelude/euler_totient.rs`). But that file's OWN module doc already
documents that the theorem itself does NOT land there, for two reasons:
no `Nat.prodRangeIf` existed at the time, and no permutation-invariance
lemma for a predicate-restricted product existed either. Since then,
`Nat.prodRangeIf` (definition + equations + congr_lt) HAS landed
(`nat_prelude/subset_product.rs`), but that file's own doc says the
permutation-invariance step is still missing on the Nat side, and sizes
porting it (an adjacent-transposition swap induction) at ~650 lines,
"same order of magnitude" as the file itself.

Full details in progress -- see commit history on this file.
