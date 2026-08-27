# Lane: graded-families — ADR-0603's four remaining graded statement families

<!-- plan-section: lane-status -->

**Done (`DONE`, graded-families, 2026-08-27).** Stated the four rows —
constructive general form, boundary refutation, exact decidable-fragment
form, labeled import — for MVT, LUB/completeness, Taylor remainder, and FTA
(the four theorems the 2026-08-27 architecture review §4 named as owed this
treatment, IVT/EVT already having it). Deliverable:
[`docs/curriculum/graded-statement-families.md`](../../curriculum/graded-statement-families.md),
linked from `spivak.md` (rows 8, 11, 20, 25–27) and from ADR-0603.

Measured with `prelude_theorem_inventory --release --include-constructed`
(theorem rows) and `kernel_declaration_projection --require-declaration`
(definitions; exits non-zero on absence), both rebuilt fresh this session
(`scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
prelude_theorem_inventory --example kernel_declaration_projection`), plus
`cargo test -p axeyum-cas --lib extremum::` (20 passed) and
`python3 scripts/validate-facts.py` (806 facts). Every negative was paired
with a positive control of the same declaration kind before being trusted.

**Headline findings** (see the doc for full citations):

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

<!-- plan-section: landed-changes -->

| 2026-08-27 | `DONE` | ADR-0603's four remaining graded statement families (MVT, LUB, Taylor remainder, FTA) stated as measured rows in `docs/curriculum/graded-statement-families.md`; two stale `spivak.md` claims corrected (`Complex.abs`/`CReal.sqrt` no longer absent; `Complex.polyMul` no longer blocked); ADR-0603 given a pointer postscript. |
