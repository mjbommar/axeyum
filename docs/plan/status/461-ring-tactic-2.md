# Lane: ring-tactic-2 — the ring producer over ℤ and ℚ, and the ℕ sorting fix

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, ring-tactic-2, 2026-09-03).** Continuing
`ring-tactic-1` (ADR-1580): fix the ℕ producer's documented intra-monomial
sorting incompleteness, then build `ring::int` and `ring::rat`. In progress.

<!-- plan-section: landed-changes -->

| 2026-09-03 | ring-tactic-2 | `ring::nat::Problem::sort_factors`: intra-monomial commutativity, `x*y = y*x` now an identity (was a documented sized negative) |
