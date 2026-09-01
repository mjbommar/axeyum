# Lane: cas-coverage-audit

<!-- plan-section: lane-status -->

**Status:** landed 2026-08-31. The Spivak spine table's `C` (CAS, ADR-0603
row 3) column is audited chapter by chapter, a blank cell is now a gate failure,
and three other coverage documents that described calculus reachability without
mentioning the CAS carry dated pointers. [ADR-1300](../../research/09-decisions/adr-1300-a-coverage-table-must-state-a-verdict-for-every-producer.md).

## Why

Asked how much of Spivak is complete, the coordinator read
`docs/curriculum/foundational-books/spivak.md`'s route column — legend "Three
routes, not two: S / K / X", `axeyum-cas` named **once** in the whole file
against 28 mentions of `CReal` — and reported the `X` rows as terminal. `X` is
ADR-0603 **row 1**'s verdict; the CAS is **row 3**, the exact classical
statement on the decidable fragment.

Chapter 20 read `| 20 | Taylor polynomials | — | open |` while
`crates/axeyum-cas/src/taylor.rs` shipped Taylor's theorem with the Lagrange
remainder, naming ADR-0603 row 3 and Spivak ch. 20 in its own module doc.
Chapter 19 had **no row at all** while `partial_fractions.rs` named it in its
first sentence.

## Landed

| Change | Where |
|---|---|
| All 23 spine rows carry an audited `C` cell; chapter 19 added; six stale cells corrected with the refuted text quoted in a dated block | `docs/curriculum/foundational-books/spivak.md` |
| `check-spivak-cas-column.py` — a blank `C` is a failure; 8 guards, each mutation-verified | `scripts/check-spivak-cas-column.py` |
| 9 controls, one per guard plus a baseline-passes control | `scripts/tests/test_check_spivak_cas_column.py` |
| `SUITES["spivak-cas-column"]` — all 8 mutants killed by exactly one control each | `scripts/tests/mutation_controls.py` |
| Gate registered so it runs without a human typing it | `scripts/check.sh`, `justfile` |
| Dated CAS-route pointers on three documents that described calculus reachability with zero CAS mentions | `docs/learn/math/calculus-theorem-boundary.md`, `docs/mathematics-2026-08/04-reachability.md`, `docs/curriculum/03-destinations/calculus.md` |
| The decision | `docs/research/09-decisions/adr-1300-…` |

## Measured, and worth carrying

- **46 `cas-certificate` facts split 32 `cas-internal` / 14
  `kernel-reconstructed`**, read from `validate-facts.py`'s own
  `classify_cas_certificate_fact`. By area: 16 Euclidean geometry, 9
  binomial/telescoping, 6 IVT/EVT/extremum, 4 number theory, 4 GF(2), 2 MVT, 2
  Taylor, 2 partial fractions, 1 polynomial identity. Only 26 are Spivak-shaped.
- **The legend's own crate numbers were low.** "72,008 lines, 363 public
  functions across 53 modules" counts `src/*.rs` with `pub fn` at column 0 —
  excluding `mvpoly/`, `ntheory_certify/`, `sos/`, `bin/` and every `impl`
  method. All 68 `.rs` files under `src/`: **77,590 lines, 685 `pub fn`**.
- **Zero non-comment lines in the whole CAS mention continuity**, positive
  control 548 for `polynomial` — which is what makes chapter 6's
  `audited — none` a measurement rather than an assumption.
- **A survey grep on the crate path `axeyum-cas` over-flagged.**
  `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md` came
  back as a hole with 127 `CReal` and 0 `axeyum-cas`; it in fact handles row 3
  carefully and honestly across a dedicated section. Widening the signal to
  `CAS|ADR-0603|row 3|Gröbner|Zeilberger|…` cleared it. Match on the concept,
  not on one spelling of the crate path.

## Open, and it is the flywheel's own next task

**Chapters 5, 12, 13 and 14 have a real, certificate-carrying `C` route and
ZERO ledger facts** — marked *unregistered capability* in the cells.
`lib.rs::integrate` returns an antiderivative that certifies itself by
differentiate-and-zero-test on every call, and nothing in `artifacts/facts/`
records it. Four facts are cheap and each would move the
`cas-certificate` counter for a capability that already ships.

Also open, and a separate decision:
`docs/research/08-planning/capability-matrix.md` is generated from
`axeyum_solver::capabilities::CAPABILITIES`, so it is a *solver* capability
matrix under a name that promises the whole stack. Nothing in it is wrong; the
CAS simply cannot appear. Widening the generator's source is the fix.
