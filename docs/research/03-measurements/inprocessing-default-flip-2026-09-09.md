# Roadmap 1.2 measured: `cnf_inprocessing` does NOT flip on

Measured 2026-09-09 on `s4` at `6dd85fc78`. Roadmap item 1.2
([`11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
asks whether `SolverConfig::default()`'s `cnf_inprocessing: false`
(`crates/axeyum-solver/src/backend.rs:390`) should become `true`, and states the
rule the item exists to enforce: **measure first, flip second.**

The measurement was taken. **The default stays off.** Nothing in
`backend.rs` changed; this note is the deliverable.

## The exit criterion, and what each half returned

> "Ratchets report PROGRESS or NOT COMPARABLE never REGRESSION at the pinned
> reference frame; every unsat under inprocessing still produces a DRAT that
> `check_drat` accepts. Then the default flips and the `inprocess.rs:138`
> comment is corrected."

| half | verdict |
|---|---|
| ratchets never REGRESSION | **FAILED** — `bv_reduction` REGRESSION at a comparable frame, reproduced |
| inprocessed `unsat` still DRAT-checks | **met**, and was already met before this run |
| corpus verdicts unchanged | 0 DISAGREE, but **7 decided files lost, 0 gained** |

Two of the three conditions are not met, so the flip is not licensed. The
comment half was already landed by ADR-1810 (see the last section).

## Method

Same host, same binary path, same pinning, arms run back to back. The only
difference between arms is the one-line default:

```sh
sed -i 's/cnf_inprocessing: false,/cnf_inprocessing: true,/' \
    crates/axeyum-solver/src/backend.rs
scripts/cargo-serialized.sh test -p axeyum-solver --features full \
    --test progress_frontier --test corpus_regression --no-run
taskset -c 0-7 ./target/debug/deps/progress_frontier-<hash> --test-threads=1 --nocapture
./target/debug/deps/corpus_regression-<hash> --nocapture
```

`--features full` is mandatory on both suites; both reported a NONZERO test
count in every run below (12 and 2 respectively), so no run is the
compiles-to-nothing trap.

Machine, from the ratchet's own `reference frame` lines: `s4`, 8 CPUs visible
under the pin, 12th Gen Intel Core i5-12600K, pinned to the P-cores per
[`frontier-ratchet-reference-frame.md`](../08-planning/frontier-ratchet-reference-frame.md).
The box was shared with other lanes; 1-minute load ran 2.9-12.4 across the four
sweeps. That contention is why the per-family comparability flags below are
quoted rather than summarized.

## 1. Capability frontier — REGRESSION on `bv_reduction`

`progress_frontier`, `--features full`, `taskset -c 0-7`, `--test-threads=1`.

| family | off (default) | on | committed baseline |
|---|---:|---:|---:|
| **`bv_reduction`** | **35** ratchetable, scale 1.13x | **26** REGRESSION, scale 1.14x | 30 |
| `lia_cuts` | 35 NOT COMPARABLE | 35 ratchetable | 26 |
| `nia_unsat` | 40 | 40 | 40 |
| `nra_degree` | 40 | 40 | 40 |
| `string_bound` | 40 ratchetable | 40 NOT COMPARABLE | 8 |

The `bv_reduction` rows are the ones that decide the item, and both of them are
**comparable** — neither carries a `NOT COMPARABLE` or `ADVISORY ONLY` flag, and
their calibration scales are within 1 % of each other (1.13x vs 1.14x, budgets
4510 ms vs 4580 ms). The inprocessing arm got the marginally *larger* budget and
still lost nine points. Verbatim:

```
FRONTIER bv_reduction = 35 (baseline 30), PROGRESS (+5 over baseline, ratchetable)
  reference frame [bv_reduction]: machine s4 (8 cpus, 12th Gen Intel(R) Core(TM) i5-12600K),
  load 2.88 -> 2.65, calibration 143.2 ms vs reference 127.0 ms => scale 1.13x, budget 4510 ms
```

```
FRONTIER bv_reduction = 26 (baseline 30)
  reference frame [bv_reduction]: machine s4 (8 cpus, 12th Gen Intel(R) Core(TM) i5-12600K),
  load 6.40 -> 7.88, calibration 145.4 ms vs reference 127.0 ms => scale 1.14x, budget 4580 ms
REGRESSION [bv_reduction]: frontier 26 < committed baseline 30 — a roadmap lever lost ground.
```

The suite exits 101 with `11 passed; 1 failed` in the `on` arm and 0 in the
`off` arm.

**Reproduced on a second tree.** The same A/B was run first at `60e261039`
(before merging 33 commits including `TickValve` and ADR-1811's preprocessing
merge) and gave `bv_reduction` 34 off / **26 on**, REGRESSION, at scales 1.08x
and 1.09x. Two baselines (34, 35) against two identical inprocessing readings
(26, 26), across a 33-commit gap. The regression is not a load artifact.

The other four families are unaffected: they do not route through the
bit-blast-to-SAT path where inprocessing lives, and their numbers move only with
the calibration flags.

## 2. Corpus verdicts — 7 files lost, 0 gained, 0 DISAGREE

`cargo test -p axeyum-solver --features full --test corpus_regression`,
2 tests passed in each arm.

| | off (default) | on |
|---|---:|---:|
| files | 218 | 218 |
| **agree** | **137** | **130** |
| **unknown** | **31** | **38** |
| parse-skipped | 50 | 50 |
| **DISAGREE** | **0** | **0** |
| incremental sweep | 12 files / 39 queries, 0 DISAGREE | identical |
| wall time | 17.4 s | 35.0 s |

`DISAGREE = 0` in both arms, so **no verdict became wrong** — the soundness
property holds and the `sat` models still replay. What moved is capability: the
extra encoding work spends the 2 s per-file budget before the search reaches an
answer. Every one of the seven is a timeout, and the direction is one-way:

| file | on-arm result |
|---|---|
| `cvc5/qf_abv/…bv__issue8809.smt2` | `timeout in 2000 ms` (expected sat) |
| `cvc5/qf_fp/…fp__issue7858-1.smt2` | `timeout in 2000 ms` (expected sat) |
| `cvc5/qf_s/…strings__bug768.smt2` | `timeout in 2000 ms` (expected sat) |
| `cvc5/qf_slia/…issue6681-split-eq-strip-l.smt2` | `timeout in 2000 ms` (expected sat) |
| `cvc5/qf_slia/…replace-find-base.smt2` | `timeout in 2000 ms` (expected unsat) |
| `cvc5/qf_slia/…rw_555.smt2` | `timeout in 2000 ms` (expected unsat) |
| `cvc5/qf_slia/…str-pred-small-rw_538.smt2` | `timeout in 2000 ms` (expected unsat) |

**Gained: none.** An eighth file, `cvc5/qf_s/…strings__issue3440.smt2`, still
agrees but crosses the `undecided/slow` reporting threshold (`sat in 1857 ms`),
which is why the flagged-line count moves by 8 while the verdict count moves
by 7.

## 3. Inprocessed `unsat` still carries a checkable DRAT

This half of the criterion is met, and it was met before this measurement.

```
cargo test -p axeyum-solver --features full --test sat_bv -- cnf_inprocessing
running 3 tests
test cnf_inprocessing_unsat_is_drat_proof_checked ... ok
test cnf_inprocessing_agrees_with_baseline_and_replays ... ok
test cnf_inprocessing_records_stats_and_eliminates_variables ... ok
test result: ok. 3 passed; 0 failed
```

At corpus scale the answer is
[`inprocessed-unsat-proof-coverage-2026-09-08.md`](inprocessed-unsat-proof-coverage-2026-09-08.md):
117 of 117 inprocessed `unsat` on the pinned 200-file QF_BV parity list checked
against the **ORIGINAL** formula through `ReductionLink` (ADR-1780), 0 against
the reduced one, 0 carrying neither key. **The certificate is not what blocks
this flip.** Cost is.

## 4. One test encodes the default rather than stating it

With the flag flipped, `cargo test -p axeyum-solver --features full --test sat_bv`
is `33 passed; 1 failed`:

```
---- cnf_compaction_admits_a_var_budget_the_uncompacted_count_exceeds stdout ----
panicked at crates/axeyum-solver/tests/sat_bv.rs:1144:9:
without compaction the var-bound budget must refuse the encoding, got Sat(Model { … })
```

The cause is `sat_bv.rs:1139`, the test's own negative control:

```rust
let no_inprocess = SolverConfig::default().with_cnf_variable_budget(budget);
```

It spells "inprocessing off" as "the default", so flipping the default deletes
the control instead of failing it — the arm it means to refuse now runs
compaction and succeeds. Whenever this flip is revisited, that line must become
an explicit `.with_cnf_inprocessing(false)` **before** the default moves, not
after. Left unchanged here because this lane does not own `sat_bv.rs` and the
flip is not happening.

## What would change the answer

The regression is a budget effect, not a correctness one, and the shape is
already known from
[`inprocessing-cost-decomposition-2026-09-08.md`](inprocessing-cost-decomposition-2026-09-08.md):
BVE is 81 % of inprocessing cost, and 16 of 195 files spend their entire slice
inside a BVE that is then cut off unfinished. The seven files lost here are the
same failure mode at a 2 s budget instead of 24 s. So the lever is admission,
not the passes:

- `TickValve` (roadmap 1.5, `crates/axeyum-cnf/src/ticks.rs`) exists but is
  **not on the shipping path** — `grep -rn TickValve crates/axeyum-solver/src/`
  returns nothing at `6dd85fc78`. Routing it in, with a budget-derived grant, is
  the change that would make this measurement worth repeating.
- Until then any re-measurement should re-run exactly the two suites above and
  compare against this note's `off` column, which is the tree's current
  behaviour and not a historical figure.

## Related

- ADR-1810 already corrected `inprocess.rs`'s misleading sentence about what the
  shipping path enables; the corrected text is at `inprocess.rs:146-153` and
  states that inprocessing is default-**off** and `cnf_vivify` a no-op without
  it. Roadmap 1.2's "and the `inprocess.rs:138` comment is corrected" clause was
  therefore satisfied ahead of this item, and the line number in the roadmap is
  stale by that move.
- [`corrections-to-the-inprocessing-story.md`](corrections-to-the-inprocessing-story.md)
  reached the same conclusion at a 24 s budget on the QF_BV parity list: parity
  on decided count, behind on PAR-2. This note is the shorter-budget,
  whole-corpus, post-ADR-1810 confirmation, and at 2 s the gap is wider.
