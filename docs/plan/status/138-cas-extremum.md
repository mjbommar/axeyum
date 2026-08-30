# Lane: cas-extremum — exact polynomial EXTREMUM (ADR-0603 row 3, EVT)

<!-- plan-section: lane-status -->

**Landed (`WIP`, cas-extremum, 2026-08-27).** Added
`crates/axeyum-cas/src/extremum.rs`: `polynomial_extremum` /
`verify_extremum_certificate`, the exact polynomial-fragment Extreme Value
Theorem — ADR-0603 row 3, mirroring `real_algebraic.rs`'s `polynomial_ivt` /
`verify_ivt_certificate` (row 3 for IVT). Differentiates
(`poly::rat_derivative`), Sturm-isolates `p'`'s real roots
(`algebraic::real_roots`), filters to the interior of `[a,b]`, and compares
finitely many candidate values exactly via two new `real_algebraic.rs`
exports (`algebraic_cmp`, a total order via sign-of-difference;
`eval_poly_at_algebraic`, polynomial evaluation at an algebraic argument,
reduced mod the minimal polynomial first to bound Horner cost). The checker
does not trust the producer's candidate list: it re-isolates `p'`'s roots
from scratch and rejects on a cardinality mismatch, which is what makes a
dropped-candidate mutation (the interesting one) actually falsifiable rather
than merely asserted.

20 tests (all passing): 4 correctness spot-checks (interior max, endpoint
max, a genuine tie between an interior point and an endpoint, an irrational
argmax bracketed exactly — no floats), 5 degenerate cases (constant `p`,
`a == b`, no interior root in range, repeated derivative root), 9 mutation
tests (corrupted coefficient/derivative/critical-point/bracket, dropped
candidate, fabricated extra candidate, duplicated candidate, wrong-argmax
self-consistency, out-of-range argmax index — none panic), 2 cost-curve
tests. Plus one `#[ignore]`d exploratory probe (not a committed regression
check) that found the isolation cost curve: sparse critical points up to
degree 22 cost 16 ms–13.7 s and decline soundly at degree 24; a "thick"
(every-coefficient-nonzero) degree-6 polynomial costs ~24 s before declining
— isolation cost tracks coefficient structure, not degree alone.

No panics found in anything called from this module (`crate::algebraic`,
`crate::sturm`, `axeyum_ir::poly`, `axeyum_ir::RealAlgebraic`) when fed
adversarial/mutated data; `AlgebraicReal`'s `test_support::make_unchecked`
(cfg(test), already existed for `real_algebraic.rs`'s own IVT mutation
tests) is reused for the swapped-critical-point and corrupted-bracket
fixtures here.

`docs/research/10-cas/decidability-map.md` updated with the EVT
polynomial-fragment row (per-capability contract table) and a pointer from
the "Algebraic numbers" zero-testing row.

Detail moved to [`../notes/138-cas-extremum.md`](../notes/138-cas-extremum.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `7705b0776` | feat(cas): exact polynomial EXTREMUM certificate (ADR-0603 row 3, EVT) |
| 2026-08-27 | `86d888a82` | wip(cas): scaffold `extremum` module for ADR-0603 row 3 (EVT) |
