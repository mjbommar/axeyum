# Lane: tactic-list-int — `simp::list`, `decide`/`tactic` over ℤ and ℚ

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, tactic-list-int, 2026-09-03).** Closing two named
cuts: ADR-1586 §4's `simp::list` design sketch (not built by the `simp`
lane), and ADR-1589's ℕ-only `Tactic<D: NatOps>` (ℤ/ℚ scoped out). In
progress: `simp::list` producer + congruence-layer gaps in
`list_prelude/ops.rs`, `decide` over `Int`/`Rat`, and a combinator over both
carriers. Will update this block with SHAs and final numbers at close-out.

<!-- plan-section: landed-changes -->

| 2026-09-03 | tactic-list-int | lane opened, status stub |
