# Notes: graded-families

Detail moved out of [`../status/graded-families.md`](../status/graded-families.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **MVT row 2 is an inherited assertion, not a dedicated refutation** — and
  the EVT unavailability it inherits from is itself marked "in progress" in
  `crates/axeyum-cas/src/extremum.rs`. MVT row 3 (`polynomial_mvt`) is
  unbuilt but every ingredient (`rat_derivative`, `polynomial_ivt`,
  `polynomial_extremum`) already ships — cheapest next task in this note.
- **LUB row 2 is a clean absence** — no constructive-LUB counterexample
  exists anywhere in the codebase; `spivak.md`'s "classical LUB unavailable"
  was never technically an overclaim (it never said "refuted"), but this is
  the clearest case of asserted-not-proved unavailability found this
  session. LUB row 3 is `extremum::polynomial_extremum`, reused from EVT,
  for the polynomial-range special case only.
- **Taylor remainder is the least-developed family**: row 1 is explicitly
  sized in `creal/polynomial.rs`'s own module doc but not started (needs an
  n-fold `hasDerivative` package — only pairwise combinators exist); row 2 is
  undecided which statement would even need refuting; the CAS `series` route
  is certified but answers a weaker question (truncation identity, no error
  bound) than the remainder theorem.
- **FTA's infrastructure is far more built than `spivak.md` said**:
  `CReal.sqrt` (2026-08-23) and `Complex.abs` incl. the triangle inequality
  `abs_add_le` (2026-08-26) both landed and were still marked absent/blocked
  in `spivak.md`; `Complex.polyMul` plus its two correctness theorems landed
  2026-08-27 (the same day as this note) and were still marked "genuinely
  blocked." Both corrected in `spivak.md`. FTA itself remains unbuilt: row 1
  needs a compactness argument not attempted here, row 2's applicability is
  unassessed (FTA may not even be in IVT/EVT's failure class), row 3 needs a
  complex root-isolation algorithm that does not exist in any form.

No facts were registered, no declarations were built, nothing under
`crates/` was touched (measurement/documentation task per brief).
