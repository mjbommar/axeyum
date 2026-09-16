# Lane `nra-single-cell` — single-cell CAD for QF_NRA (ADR-2121)

<!-- plan-section: lane-status -->

Status: the route, its certificate checker, its fuzz seed class and its mutation
suites are landed. The lever `AXEYUM_NRA_CAD=single-cell` ships **OFF**.

## What this lane was

ADR-2110 ended with "the model-constructing nlsat/CAD route is the
recommendation, not this lane's build". This is that build, bounded: ≤ 4
variables, total degree ≤ 8, conjunctive, coefficients inside the existing
`i128` clearing.

## The numbers

| | |
|---|---:|
| ADR-2110's CAD-only population | 45 |
| inside the slice's BOUND ceiling (≤4 vars, degree ≤8, coeff ≤ `1<<40`) | 24 |
| **corrected** shape ceiling (also genuinely conjunctive after `let` expansion) | **12** |
| excluded by the `1<<40` coefficient clearing alone | 9 |
| of the 24, decided by the route | 2 |
| QF_NRA A/B: A `default` → B `single-cell` | **117 → 123 (+6)** |
| stable losses / `sat`↔`unsat` flips | 0 / 0 |
| vs declared `:status` | 0 disagreements over 238 comparable verdicts |
| differential fuzz | 1500 instances, 239 decided (237 sat / 2 unsat), 0 disagreements |

## The two things worth carrying forward

**This lane's first sizing was wrong, and the way it was wrong generalises.** It
read `has_top_or` from ADR-2110's shape table — a column computed at the
**outermost node** of each assertion. `meti-tarski` files are one enormous
`let`-bound `and` tree, so an `or` six levels inside does not move it. The
ceiling was not a guess that came out high; it was the wrong question answered
exactly. A column computed at the top of a term is not a statement about the
term.

**An `unsat` from this route is CHECKED, not PROVED.** The certificate checker
establishes atom-cell sign-invariance exactly (no root strictly inside the cell,
by an independent Sturm count) but tests *delineability* by sampling three
further interior points. That is why the default does not move: every other
`unsat` producer here is gated by something exact, and making a sampling check
load-bearing on the default path is a decision to take deliberately.

## What was left undone, and why

- **The held-out 200-file QF_NRA draw was NOT run.** It is the gate for shipping
  ON; the decision is OFF, so spending a blind population on a lever that is not
  moving would spend it for nothing.
- **Lazard evaluation** (`references/cvc5/src/theory/arith/nl/coverings/lazard_evaluation.cpp:590`)
  is the named way to stop declining on a nullified polynomial. Not built.
- The three blockers, in measured order: a **clause loop** over sign atoms
  (`non-conjunctive`, 12 of 24 and 311 of 1500), an **algebraic sample**
  (`algebraic-witness`, 6 of 24), and a **fraction-free multivariate
  determinant** so the projection is not capped at Sylvester dimension 6
  (`projection`, 2 of 24 and 188 of 1500).

<!-- plan-section: landed-changes -->

| 2026-09-15 | `4447b5a14` | Exit criterion 1, committed before any code: the slice ceiling is 24 of ADR-2110's 45, and 9 are lost to the `i128` clearing. |
| 2026-09-15 | `c03bf39f7` | `nra_cell_cert.rs` — the cell-covering certificate and an independent checker, landed BEFORE the producer so the format is fixed by what can be checked. |
| 2026-09-15 | `31e150738` | `nra_single_cell.rs` — CDCAC behind `AXEYUM_NRA_CAD=single-cell`, OFF. `unsat` gated on the checker, `sat` on a rational model replay. |
| 2026-09-15 | `5755582bf` | Rational point cells are descended into; `algebraic-witness` split out of `algebraic-coarsening`; the conjunctivity correction (24 → 12) and the cause scan. |
| 2026-09-15 | `4ff928964` | The `generate_single_cell_shape` fuzz seed class and a route-level differential test; 195 unattributed declines found and closed. |
| 2026-09-15 | `db89894c9` | Two mutation suites (3 mutations, 3 kills, one named test each); clippy clean on solver+bench. |
