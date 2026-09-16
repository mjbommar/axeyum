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
| 4. interleaved A/B | **PARTIAL** — QF_NRA +4 (4 STABLE-GAIN, 0 STABLE-LOSS), QF_NIA flat after recheck, QF_LRA flat (0 movers), 4/4 replays accepted; **held-out NOT COMPLETE (23 of 200)**, exactness A/B NOT RUN |
| 5. mutation | **MET** — 14 mutations across 4 suites, every one killed, `--check-anchors` 1130 anchors stale=0 |
| 6. gates | **MET** — see the table below |

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

| division | A `single-cell` | B `algebraic-witness` | delta | movers | flips | missing |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_NRA (pinned 200) | 124 | **128** | **+4** | 4 | 0 | 0 |
| QF_NIA (200) | 85 | 84 | −1 | 1 | 0 | 0 |
| QF_LRA (200) | 107 | 107 | **0** | **0** | 0 | 0 |

QF_LRA — the division the lever cannot reach — moved nothing. QF_NIA's single
`sat → unknown` is **ambient, not a loss**: the three-pass recheck returns
NEITHER-DECIDES (both arms `unknown` 3/3), and arm A's lone `sat` in the sweep
came at 23,225 ms of a 24,000 ms budget. **0 STABLE-LOSS across all three.**

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

## Gates (criterion 6)

| gate | result |
| --- | --- |
| `scripts/check-clippy-complete.sh` | **903 of 903 workspace targets across 27 of 27 crates, all 903 compiled by this run, 0 diagnostics** |
| default-features `cargo check --workspace --all-targets` | 0, 56 s of real checking |
| `bench-results/real-opaque-20260914/run-dispatch-reason-suites.sh` | **29 suites green, none inert, 0 failures** — including the newly registered `nra_algebraic_witness` (4 passed) |
| `cargo test -p axeyum-solver --features full --lib -- --skip reconstruct::` | **1637 passed, 0 failed** |
| `progress_frontier --features full -- --test-threads=1` | **12 passed, 0 failed, no REGRESSION**, run pinned to `taskset -c 0-7` at host load 5.09 |
| `cargo fmt --all --check` | 0 |
| `config_registry` tests | 18 passed, 0 failed |
| `check-config-registry-staleness.py` | 0 unexplained (33 stale rows, all accepted with written reasons) |
| `scripts/tests/mutation_controls.py --check-anchors` | 1130 anchors, **stale=0** |
| `check-merge-hygiene.sh` | PASS |
| `scripts/check-links.sh` | all links ok |

The bare `cargo clippy --workspace --all-targets --all-features -- -D warnings`
returned green in **0.70 s** on this tree — the shape CLAUDE.md warns about, a
gate passing over code it never compiled. The 903/903 above is the wrapper's
number, and the wrapper had to touch all 14,392 build inputs to get it.

`bench-results/frontier/*.json` are modified by the ratchet run and deliberately
**not committed**.

## Landed changes

| date | sha | what |
| --- | --- | --- |
| 2026-09-16 | `1a2d58286` | `sign_at` read two endpoint samples as an enclosure — wrong sign at an algebraic point; exact Sturm side condition, three tests, plus this lane's sizing scaffolding (4 files) |

## What did NOT run

* **Held-out 200-file QF_NRA draw — NOT COMPLETE**, 23 of 200 files (0 movers)
  when the round closed. This is one quarter of the shipping criterion, so the
  ADR stays `proposed` and the lever stays OFF. Finishing it is a re-run of
  `ab-sweep.sh`'s `heldout` population, ~60 min on two pinned core pairs;
  nothing new has to be decided.
* **The binary-against-binary A/B pricing the `sign_at` exactness fix — NOT
  RUN.** That fix is not behind a lever and is in BOTH arms of every number
  above, so those numbers do not price it. It can only convert an accept into a
  decline, so what is unmeasured is lost coverage, never a wrong verdict.
  ~60 min per population.

## Next

The A/B, the mutation controls and the gate sweep; then the ship decision.
