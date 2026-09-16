# Lane `nra-single-cell` — single-cell CAD for QF_NRA (ADR-2121)

<!-- plan-section: lane-status -->

Status: the route, its certificate checker, its fuzz seed class and its mutation
suites are landed. **`AXEYUM_NRA_CAD=single-cell-sat` is now the shipped
default** — it runs the route and keeps only its exact `sat` half. The full
`single-cell` arm ships **OFF**, because its `unsat` is the half gated on a
sampling delineability check.

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
| of that, attributable to the route deciding | **+4** (2 gains are files it declines) |
| 3x recheck: STABLE-GAIN / STABLE-LOSS / UNSTABLE | **6 / 0 / 2** |
| QF_NIA | 81 → 81, both movers UNSTABLE |
| QF_LRA control | 107 → 107, **0 movement of any kind** |
| `sat`↔`unsat` flips, all three divisions | **0** |
| vs declared `:status` | 0 disagreements over 594 comparable verdicts |
| differential fuzz | 1500 instances, 239 decided (237 sat / 2 unsat), 0 disagreements |

## The sat-only arm — what actually shipped

The reason the full route stays off applies to **one of its two halves**. A
`sat` is a rational model replayed exactly against the original assertions; only
the `unsat` is gated on a sampling delineability check. `single-cell-sat` runs
the route and withholds every `unsat` as
`CadDecline::UnsatWithheldSampledDelineability`, keeping the exact half.

| | |
|---|---:|
| QF_NRA: A `default` → B `single-cell-sat` | **117 → 121 (+4)** |
| gains / losses / flips | **4 / 0 / 0** |
| 3× recheck | **4 STABLE-GAIN, 0 STABLE-LOSS, 0 UNSTABLE** |
| vs declared `:status` | 0 disagreements over 236 comparable verdicts |
| wall clock | A 1,224 s, B **1,184 s** — the withholding arm is still faster |

The four gains are exactly the full arm's four `sat` verdicts; its two `unsat`
gains are gone, which is the arm doing what it was built to do — confirmed from
the mover list, not asserted from the design.

| QF_NIA | 82 → 81; the one row rechecks **BOTH-DECIDE** (`unsat` ×3 both arms) |
| QF_LRA control | 107 → 107, **0 movement of any kind** |
| flips / `:status` disagreements, all three divisions | **0 / 0 over 593 comparable verdicts** |

**Shipped.** `CAD_DEFAULT` moved from `CadPolicy::DEFAULT` to
`CadPolicy::SINGLE_CELL_SAT` — the first time this entry's shipped value has
changed. `AXEYUM_NRA_CAD=default` still selects the pre-ADR-2121 engine, through
an explicit arm in `parse_cad_arm` rather than the catch-all.

The trade is deliberate and worth stating plainly: the sat-only arm gives up
**two** stable gains the full arm had (its two `unsat` verdicts), in exchange for
a default on which **no verdict rests on a finite sample**.


## Gates

`clippy -D warnings` on solver + bench with `--features full`: exit 0.
`cargo fmt --all --check`: clean. `cargo check --workspace --all-targets` on
default features: clean. Solver lib sweep (`--skip reconstruct::`): **1562
passed, 0 failed**. `corpus_regression`: 2 passed. All **eight** nonlinear z3
differential fuzzes green with nonzero counts. `config_registry::tests`: 18
passed. Merge hygiene, links, `gen-plan --check`, `gen-adr-index`: PASS.
Holdout isolation: PASS at 206 held-out. `progress_frontier` (`--features full`,
`--test-threads=1`, load 2.9-3.3): **12 passed, 0 failed, no REGRESSION**, with
`frontier_nia_unsat` and `frontier_nra_degree` — the two families this route
could touch — both green. The five `bench-results/frontier/*.json` files the run
rewrites were restored and are NOT committed.

The route/dispatch integration suites (`route_trace`, `route_attribution`,
`dispatch_rung_refusal_declines`, `nra_fbbt_route`, `ufnra_route`,
`cas_ideal_route`, `decision_and_evidence_routes_agree`,
`math_resource_lra_routes`, `quantified_route_trace`): all green.

**Two suites failed on the first pass and both were load, not code.**
`auto::tests::pathological_overbound_stays_terminal_under_every_policy` and
`route_attribution::attribution_does_not_change_any_verdict` both assert inside a
5-second budget, and both were run in a parallel sweep on a box carrying a
four-core benchmark. Each passes on a quiet box at the same HEAD, and neither is
on a code path this lane touches. The number reported above is the quiet run.

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
