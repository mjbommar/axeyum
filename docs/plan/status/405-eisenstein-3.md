# Lane: eisenstein-3 — build `Nat.sumRangeIf` and close ADR-1544's residues 2, 3, 5

<!-- plan-section: lane-status -->

**Status: WIP (eisenstein-3, 2026-09-02).** Picking up ADR-1540 / ADR-1544.
Landed and axiom-free before this lane: the side condition,
`Nat.sumRange_permute`, `Nat.eisenstein_floor_sum`, `Nat.ble_select_add_of_ne`,
`Nat.gauss_fold_sumRange_eq`. Open, in order: **residue 2** (the residue/fold
reconciliation, blocked on `Nat.sumRangeIf`, measured ABSENT in every prelude
against a `prodRangeIf` control returning 12), **residue 3** (the mod-2
bookkeeping), **residue 5** (the `min`-free corollary needing
`div (q * succ x) pp <= n` at `pp = succ (2m)`, `q = succ (2n)`).

<!-- plan-section: landed-changes -->

| 2026-09-02 | eisenstein-3 | lane opened; status stub only |
