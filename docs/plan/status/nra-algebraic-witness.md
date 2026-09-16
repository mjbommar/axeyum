# Lane `nra-algebraic-witness` — exact replay at an algebraic sample (ADR-2134)

<!-- plan-section: lane-status -->

## Status

**In progress, 2026-09-16.** The lever is built and OFF. The larger finding is a
wrong sign in the trusted evaluator, fixed and not behind any lever.

| exit criterion | state |
| --- | --- |
| 1. sizing before code | **MET** — `algebraic-witness` = 7 of the pinned 200, 6 of them `unknown` |
| 2. design claims at `file:line` | **MET** — ADR-2134 §"Design claims" |
| 3. lever, exact replay, root objects, three fixtures, fuzz nonzero | **MET** — fuzz `algebraic_models=855`, 855 agreements, 0 disagreements |
| 4. interleaved A/B | **PARTIAL** — QF_NRA pinned 200 done and clean (+4, 4 STABLE-GAIN, 0 STABLE-LOSS, 0 flips, 4/4 replays accepted); QF_NIA, QF_LRA and held-out still running |
| 5. mutation | **MET** — 14 mutations across 4 suites, every one killed, `--check-anchors` 1130 anchors stale=0 |
| 6. gates | **PARTIAL** — clippy 903/903 targets 0 diagnostics, default-features workspace check 0, fmt 0, `config_registry` 18/0, staleness 0 unexplained, 29 dispatch suites green (none inert); lib sweep and `progress_frontier` still running |

## The finding

`RealAlgebraic::sign_at` decided a polynomial's sign at an algebraic point by
comparing that polynomial's values at the two ENDPOINTS of the isolating
bracket, and returned as soon as they agreed and were nonzero.

Two point samples are not an enclosure of a range. For `α = √2` bracketed by
`(1, 2)` and `q = 25x² − 70x + 48 = (5x − 6)(5x − 8)`:

    q(1) = 3 > 0     q(2) = 8 > 0     q(√2) ≈ −0.995 < 0

The function answered `Pos` for a value that is `Neg` — a wrong sign in a `pub`
API whose doc comment claimed the stronger property the code did not check.

Fixed with an exact Sturm root count over the bracket (`poly_big::RootCounter`),
not with a smaller interval: a small interval is not evidence, a root count is.

**Not a shipped wrong verdict, as far as this lane can show**, and the claim is
not made larger than that. Both existing callers feed `sign_at` polynomials whose
roots all sit in one sorted arrangement, and `sort_roots` declines unless the
isolating intervals are pairwise disjoint — so no root of `q` was ever inside
`α`'s bracket and the endpoint read happened to be sound. That invariant was
external to `sign_at` and not owned by it; this lane adds call sites.

The existing float-oracle property test **structurally could not** have found it:
its box is `c0, c1 ∈ −5..=5`, `c2 ∈ −3..=3`, and `q(1) > 0 ∧ q(2) > 0 ∧ q(√2) < 0`
has no integer solution there — the constraints force `c1 < −4.83` together with
a `c0` confined to an interval of width `< 0.08`. Replaced by an adversarial
family with an algebraic oracle and a non-emptiness assertion.

## Sizing (criterion 1)

Pinned 200 (`bench-results/board-ab-20260915/QF_NRA.tsv`, verified identical to
the prior lane's draw), `--trace`, shipped default arm:

**`algebraic-witness` = 7 of 200; 6 of the 7 are `unknown`, so the mover ceiling
is 6.** Triangulates ADR-2126's 6-of-24-in-bounds and ADR-2131's
5-of-16-admissible; the three have different denominators.

Behind `non-conjunctive`, via the clause loop's slot: the `clause-loop` arm moves
`non-conjunctive` 118 → 109 and DECIDED 19 → 24, and moves `algebraic-witness`
**7 → 7**. That null is weaker than it looks: `record_cad_decline` keeps the
FIRST cause and the loop runs after `non-conjunctive` is already recorded, so an
`algebraic-witness` decline arising inside the loop is masked. The 109
`non-conjunctive` rows are an upper bound that may hide some.

Full table and the seven file names:
`bench-results/nra-algebraic-witness-20260916/README.md`.

## The A/B, so far

Treatment `df2dfc0f…` against baseline `6261a505…`, one binary and two env
values, interleaved per file on pinned cores `5,13` and `6,14` of s5.

**QF_NRA pinned 200: `single-cell` 124 → `algebraic-witness` 128, +4.** Four
movers, all `unknown → sat`. **0 flips, 0 arm runs without a verdict token.**
Three-pass recheck: **4 STABLE-GAIN, 0 STABLE-LOSS, 0 UNSTABLE, exit 0 on all 24
runs.** Independent front-door replay of every gained `sat`:
`sat_with_algebraic_coordinate=4 replay_failures=0`; the same checker on the
shipped arm finds nothing and exits 3.

### The sizing did not predict the movers

Of the 6 sized `algebraic-witness` + `unknown` files, **1** moved. **3 of the 4
movers were sized `non-conjunctive`.** Traced, not guessed: both arms decline the
`nra-real-root` rung with `non-conjunctive`, and the verdict diverges at a later
rung where `nra.rs:339` → `decide_real_poly_constraint` → `decide_single_cell`
reaches the lever on a SUBPROBLEM. The decline slot keeps the FIRST cause, so the
census attributes the file to a rung the lever does not help.

**A first-wins decline slot makes a cause census non-predictive of a lever's
effect whenever the same decider is reachable from more than one rung.** The
ceiling of 6 above is neither an upper nor a lower bound on the measured +4.

## Landed changes

| date | sha | what |
| --- | --- | --- |
| 2026-09-16 | `1a2d58286` | `sign_at` read two endpoint samples as an enclosure — wrong sign at an algebraic point; exact Sturm side condition, three tests, plus this lane's sizing scaffolding (4 files) |

## Next

The A/B, the mutation controls and the gate sweep; then the ship decision.
