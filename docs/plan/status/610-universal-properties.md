# Lane: universal-properties — name the universal properties already proved (W1-3, W3-13)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, universal-properties, 2026-09-04).** Landed
`Nat.Peano.initial` and `Int.Characterization.initial` in a new
`crates/axeyum-lean-kernel/src/characterization/universal_property.rs`,
naming the initial-object / natural-numbers-object universal property that
`Nat.Peano.categorical` and `Int.Characterization.categorical` already prove
but never state under that name. Both are built entirely from already-proved
theorems (`iter_zero`/`iter_succ`/`iter_pred`/`iter_unique`/`rec_unique`) —
no new induction, no new axioms. `entries.len()` is now 34 (was 32);
`Weakening::defects()` now 24 (was 22), two new mutation-verified negative
controls (`NatInitialDropUniqueZero`, `IntInitialDropUniqueZero`) confirmed
rejected by the kernel. Non-vacuity test instantiates both at their own
carrier. Fact ledger, ADR-1610 and the census/gates still to run.

<!-- plan-section: landed-changes -->

| 2026-09-04 | universal-properties | `Nat.Peano.initial` / `Int.Characterization.initial` added, 34 axiom-free entries, 24 mutation-verified defects |
