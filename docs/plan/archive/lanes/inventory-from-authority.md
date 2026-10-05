# Lane: inventory-from-authority

<!-- plan-section: lane-status -->

Status: **done** (2026-08-31). Audited every kernel test whose name promises
completeness, and closed the gap the earlier round of fixes left open.

**The brief's premise was partly stale.** Every prelude flagged as still
iterating a hand list already carries an environment-derived exhaustiveness
assertion: `nat_prelude_tests.rs`, `int_prelude_tests.rs`,
`rat_prelude_tests.rs`, `complex_tests.rs`, `creal_point_tests.rs` (and
`creal_tests.rs`, the original). `prelude_tests.rs` reaches the same place by
the stronger route of scanning for anything assumed at all.

What none of them fixed: **they filter the environment by a hand-written
NAMESPACE PREFIX**, which is as much a literal as the name list it replaced. 27
introduced declarations sit outside their introducing prelude's filter, and
seven are reached by no completeness guard at all — `nat`'s
`Max.max`/`Min.min`/`Squarefree`/`instMinNat`, `cpoint`'s
`CReal.add_right_cancel`, and `characterization`'s two `iter` definitions.

`every_declaration_a_prelude_introduces_is_checked_and_axiom_free`
(`cross_prelude_collision_tests.rs`) derives ownership from the `DEPENDS_ON`
build-order diff — the function that file already had for the collision gate —
so no file needs to know what it owns and no namespace string appears in the
check. 2,581 introduced declarations checked; the partition is asserted
exhaustive in both directions. Reasoning and the alternatives rejected:
ADR-1225.

It surfaced **no violation** on its first run, and that is the reported result
rather than a dressed-up one: nine of ten environments carry nothing assumed, so
every footprint in them is empty by construction. The gain is coverage — seven
declarations nothing was watching, and an eighth outside a namespace can no
longer arrive unnoticed.

## Landed changes

| change | where |
| --- | --- |
| ownership-derived inventory gate, no namespace prefix (`5df826aba`) | `crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs` |
| ownership partition asserted exhaustive, two controls (`a93a4300c`) | same |
| `prelude-inventory-ownership`, 7 mutations each killing one test (`eee1908a8`) | `scripts/tests/mutation_controls.py` |
| ADR-1225 | `docs/research/09-decisions/adr-1225-…-build-order-diff.md` |
