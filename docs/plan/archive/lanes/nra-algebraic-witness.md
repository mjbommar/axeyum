# Lane `nra-algebraic-witness` — exact replay at an algebraic sample (ADR-2134)

<!-- plan-section: lane-status -->

## Status

**Measured and decided, 2026-09-17 (lane `AX-2134-HELDOUT`).** The lever is
built, reproducible, loss-free, and **stays OFF**: the ship criterion (0 stable
losses AND 0 flips AND ≥ 1 stable gain on BOTH the pinned and the held-out
lists) fails on the held-out gain clause. `CAD_DEFAULT` remains
`CadPolicy::SINGLE_CELL`; ADR-2134 remains `proposed`. The larger finding
(a wrong sign in the trusted evaluator, fixed, not behind any lever) is
unchanged.

| exit criterion | state |
| --- | --- |
| 1. sizing before code | **MET** — `algebraic-witness` = 7 of the pinned 200, 6 of them `unknown` |
| 2. design claims at `file:line` | **MET** — ADR-2134 §"Design claims" |
| 3. lever, exact replay, root objects, three fixtures, fuzz nonzero | **MET** — fuzz `algebraic_models=855`, 855 agreements, 0 disagreements |
| 4. interleaved A/B | **COMPLETE** — pinned at head `43f1e0f90`: 124 → 128, 4 STABLE-GAIN / 0 STABLE-LOSS / 0 UNSTABLE, 0 flips, 0 `:status` disagreements of 250; **held-out 200 (ADR-2126's draw, 0/200 overlap): 109 → 109, zero movers of any kind**, 0 flips, 0 disagreements of 216; QF_NIA / QF_LRA controls flat (2026-09-16); exactness A/B NOT RUN |
| 5. mutation | **MET** — 14 mutations across 4 suites, every one killed, `--check-anchors` 1130 anchors stale=0 |
| 6. gates | **MET** — see the tables below |
| 7. ship decision by the criterion | **DECIDED: does not ship** — held-out stable gains = 0 |

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

## The A/B, completed (2026-09-17, s7, head `43f1e0f90`)

`bench-results/nra-algebraic-witness-heldout-20260917/README.md`. One
`smtcomp_cli` (`--release --features full`, sha256 `d3606850…`), two
`AXEYUM_NRA_CAD` values, interleaved per file on s7 core pairs `1,9` / `3,11`,
24 s / 8 GiB, `$EPOCHREALTIME` timing (200 ms self-check read 203–205 ms).

| list | A `single-cell` | B `algebraic-witness` | delta | movers | flips | `:status` disagreements | nonzero exits |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| pinned 200 at head | 124 | **128** | **+4** | 4 (`unknown → sat`) | 0 | 0 of 250 | 0 |
| **held-out 200** | 109 | **109** | **0** | **0** | 0 | 0 of 216 | 0 |

Pinned recheck (s7 core pair `5,13`, 3× per arm, arms alternating within the
passes): **4 STABLE-GAIN, 0 STABLE-LOSS, 0 UNSTABLE, exit 0 on all 24 runs**
— the same four `meti-tarski/atan/problem/2/` files as on 2026-09-16. Held-out
recheck NOT RUN because its input is empty (0 movers), not because it was
skipped.

The held-out population is ADR-2126's (same script, `SEED = 20260916`;
re-drawn at head to the byte-identical list; `comm -12` against the pinned
list = 0). Arm A's 109 reproduces ADR-2126's arm A on it. The held-out list
holds 4 `atan/problem/2` files and both arms decide all four in ≤ 209 ms.

| criterion clause | pinned | held-out |
| --- | --- | --- |
| 0 stable losses | holds (0) | holds (0) |
| 0 flips | holds (0) | holds (0) |
| ≥ 1 stable gain | holds (4) | **fails (0)** |

**Decision: does not ship.** A lane re-opening this must draw a NEW held-out
population (new seed, said so); this one has been scored twice.

## The A/B, first round (2026-09-16, s5)

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
| 2026-09-17 | `e1befc425` | AX-2134-HELDOUT: the sizing at head — harness (`ab-cad-env.sh`, `drive-shard.sh`, `summarize.py`), the two shard lists per population, the binary SHA |

## Gates, 2026-09-17 (no code changed; docs and bench artefacts only)

Run from the lane worktree at `43f1e0f90` + this lane's commits, target dir
`/data0/axeyum/target/ax-2134-heldout` (created fresh 2026-09-17, so no
stale-mtime artefacts predate the tree), heavy cargo through
`scripts/cargo-serialized.sh`.

| gate | result |
| --- | --- |
| `test -p axeyum-solver --features full --test nra_algebraic_witness --test nra_clause_cert_2131 --test corpus_regression` | 4 + 12 + 2 passed, 0 failed |
| `test -p axeyum-solver --lib --features full nra` | **197 passed**, 0 failed (1784 filtered out) |
| `clippy --workspace --all-targets --all-features -- -D warnings` | 0 diagnostics, 52 `Checking` lines, exit 0 |
| `cargo check --workspace --all-targets` | exit 0 |
| `cargo fmt --all --check` | exit 0 |
| `scripts/check-suite-gating.py` | `suites=356 gated=55 excused=303` PASS |
| `scripts/check-merge-hygiene.sh` | `markers=0 adr_index=ok generated=current` PASS |
| `scripts/check-links.sh` | all links ok |
| `scripts/tests/mutation_controls.py --check-anchors` | `suites=204 anchors=1187 stale=0` |
| `scripts/check-config-registry-staleness.py` | 35 stale, 35 accepted, **0 unexplained** |
| `scripts/gen-adr-index.py --check` / `scripts/gen-plan.py --check` | both 0 |

## What did NOT run

* **The binary-against-binary A/B pricing the `sign_at` exactness fix — NOT
  RUN.** That fix is not behind a lever and is in BOTH arms of every number
  above, so those numbers do not price it. It can only convert an accept into a
  decline, so what is unmeasured is lost coverage, never a wrong verdict.
  ~60 min per population.
* **The eight nonlinear z3 differential fuzzes — NOT RUN on 2026-09-17**; they
  are mandatory only if the default moves, and it did not.
* **The held-out recheck — NOT RUN**, input empty (0 movers).

## Next

Nothing on this lever until a NEW held-out population is drawn. The
`sign_at` exactness A/B (two binaries, same arm, `ab-run.sh --binary-a`) is
the one unpriced change and is the next measurement if anyone touches this
area; it prices coverage, not soundness.
