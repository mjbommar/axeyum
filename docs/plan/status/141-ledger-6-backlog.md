# Lane: ledger-6 — registering the proved-but-unregistered Ch.14/24 backlog

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, ledger-6, 2026-08-27).** Registered 12 facts for
declarations that landed in `crates/axeyum-lean-kernel/src/creal/` (mostly
`integral.rs`, `power.rs`, `uniform_convergence.rs`, `congruence.rs`) but were
never added to `artifacts/facts/`: the exact mesh-point Riemann-sum split
identity and its two supporting lemmas, the domain-restricted
Equiv-congruence-from-uniform-continuity bridge, sub-interval restriction of
uniform continuity, the two-independent-index `close_within` bridge, the
free-parameter shared-accuracy-close lemma, the full `powerSeriesTerm` family
(definition + congruence + coefficient-boundedness domination +
Weierstrass-M-test-specialized uniform convergence), and `CReal.mulPowCongr`
(the same statement as `powerSeriesTerm_congr`, but produced mechanically by
the `congruence.rs` `CongruExpr`/`derive` deriver rather than hand-built).
The `Int.ModEq` family named in this batch's brief
(`add_modEq_left`/`add_modEq_right`/`mod_modEq`/`modulus_modEq_zero`/
`modEq_sub`) was already fully registered under the `ml430-int-*` ids with
complete 4-row evidence each — confirmed, not duplicated.

Validator: `818 facts checked, 0 errors` (was 806 before this batch).

Detail moved to [`../notes/141-ledger-6-backlog.md`](../notes/141-ledger-6-backlog.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Registered 12 facts: `F:creal-riemannsum-split-exact`, `F:creal-riemannsum-split-scale-invariant`, `F:creal-riemannsum-split-exact-of-uc`, `F:creal-congrofuniformlycontinuous`, `F:creal-uniformlycontinuouson-restrict`, `F:creal-close-within-of-within-indexed`, `F:creal-riemannsum-sharedaccuracyclose-at`, `F:creal-powerseriesterm`, `F:creal-powerseriesterm-congr`, `F:creal-powerseriesterm-abs-le`, `F:creal-powerseriesuniformconvergeson`, `F:creal-mulpowcongr`. |
