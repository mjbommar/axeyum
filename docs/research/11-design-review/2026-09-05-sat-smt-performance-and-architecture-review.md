# SAT/SMT performance and architecture review, 2026-09-05

Measured on this date against `main` at `0d38d5beb`. Every number below was
read from an artifact, a gate's own output, or source at that commit; the
command that produced it is given where it is not obvious. Companion to the
[2026-08-27 architecture review](2026-08-27-architecture-review.md), which
covered the kernel and prelude side; this one covers the solver stack.

Three questions were asked, in this order:

1. What is the state of the SMT/SAT roadmap?
2. What performance instruments exist, and what is missing?
3. Where does the architecture cost performance?

The answers, in one line each: the solver roadmap has been paused in practice
since 2026-08-22 and its planning text has not caught up; full-solver timing is
well instrumented but there are no micro-benchmarks and nothing fails when time
regresses; and the least engineered of three Boolean search engines sits under
every division where the solver is weakest.

---

## 1. Roadmap state

### 1.1 Activity

Commits touching the solver crates (`axeyum-solver`, `-cnf`, `-bv`, `-aig`,
`-rewrite`, `-smtlib`) against all commits, by ISO week:

| Week | Solver-crate commits | All commits |
|---|---:|---:|
| 2026-W33 (Aug 10) | 71 | 456 |
| 2026-W34 (Aug 17) | 129 | 1,744 |
| 2026-W35 (Aug 24) | 33 | 3,280 |
| 2026-W36 (Aug 31) | 2 | 1,387 |

```sh
git log --since=2026-08-01 --format='%ad' --date=format:%G-W%V -- crates/axeyum-solver ... | sort | uniq -c
```

The last change to a decision procedure was the LIA theory-core minimisation
fix (`40a1ab969`, ADR-0538, 2026-08-21). The last solver-side capability
landing of any kind was the LRAT certification route (`2b515a947`, ADR-0613,
2026-08-28). Since 2026-08-22 exactly one commit has touched a decision-
procedure file, and it broke two dependency edges without changing behaviour
(`0348564ab`). Every lane since has been kernel, prelude, or fact-ledger work.

### 1.2 Measured position

The parity ledger ([`bench-results/PARITY.md`](../../../bench-results/PARITY.md))
is the honest instrument: an external list pinned by sha256 before the run,
same machine, same budget, and `DISAGREEMENTS > 0` voids an entry. Latest
valid entry per division:

| Division | Measured | Axeyum / reference | Ratio | Reference |
|---|---|---|---:|---|
| QF_SLIA | 2026-08-21 | 193 / 193 | 100.0% | cvc5 1.3.4 |
| QF_BV | 2026-08-17 | 187 / 194 | 96.4% | Bitwuzla 0.9.1 |
| UF | 2026-08-21 | 83 / 93 | 89.2% | cvc5 1.3.4 |
| QF_LIA | 2026-08-21 | 113 / 139 | 81.3% | cvc5 1.3.4 |
| QF_RDL | 2026-08-21 | 102 / 148 | 68.9% | cvc5 1.3.4 |
| QF_LRA | 2026-08-21 | 88 / 134 | 65.7% | cvc5 1.3.4 |
| QF_UFLIA | 2026-08-21 | 113 / 180 | 62.8% | cvc5 1.3.4 |
| QF_IDL | 2026-08-21 | 66 / 118 | 55.9% | cvc5 1.3.4 |
| QF_NIA | 2026-08-21 | 39 / 83 | 47.0% | cvc5 1.3.4 |

Zero disagreements in every entry. Bit-vectors and strings are at parity; the
deficit is linear arithmetic, then nonlinear integers. The
[2026-08-21 gap analysis](../../plan/gap-analysis-smt-solvers-2026-08-21.md)
§9.0.1 established that the remaining linear-arithmetic losses are algorithmic:
three cheap fixes were built and refuted (dropping the LRA atom cap gave 0 new
decisions and 54 memory aborts; 5x the clock converted 1 IDL file in 10; the
probe-budget reallocation caps at 1.33x).

### 1.3 Red and stale on `main` today

Both commands below were run at `0d38d5beb`; exit statuses were read directly,
not through a pipeline.

- **`scripts/check-parity-freshness.py` exits 1.** All nine divisions are past
  the 14-day budget (stalest QF_BV at 18.6 days). Between 2,440 and 2,792
  commits under `crates/` have landed since each measurement. Enforced in
  `scripts/check.sh:947` and `justfile:879`, so the aggregate gate is red for
  this reason alone.
- **`scripts/analyze_solver_module_graph.py --check` exits 1.** Largest
  dependency cycle grew 58,215 to 59,175 lines; evidence-layer fan-out widened
  67 to 77 modules (`evidence`) and 55 to 60 (`reconstruct`). The
  [2026-08-29 lane](../../plan/status/280-solver-cycle-regression.md) broke two
  edges and reported the gate fixed; either something regressed after or the
  baseline was never re-pinned. Enforced at `scripts/check.sh:1456`.
- **Two committed parity lists have never been run.** `QF_ABV.txt` and
  `QF_UF.txt` exist under `bench-results/parity-lists/` with no ledger entry.
- **Not verified here.** The frontier ratchets (`progress_frontier`) and the
  corpus sweep (`corpus_regression`) were not run; both need a build.

### 1.4 Planning text vs. ledger

[`docs/plan/global/20-next-actions.md`](../../plan/global/20-next-actions.md)
(last substantive solver edit 2026-08-19) disagrees with the ledger it
summarises:

| Block | Says | Ledger / landed work says |
|---|---|---|
| A3 QF_NIA | 34/89 = 38.2%; "move to A4" | 39/83 = 47.0% (2026-08-21) |
| A4 QF_UFLIA | 94/180 = 52.2%; "no slice authorized" | 113/180 = 62.8%; the +22 fix (ADR-0538) landed and is not recorded here |
| A5 LRA/IDL/RDL | "no production change authorized" pending census | three candidate changes already built, measured, refuted (gap analysis §9.0.1) |
| A8 SMT-LIB | first slice is command capture; `set-option` inert, `get-*` no-ops | ADR-0541 closed multi-query `check-sat`, `get-model`, `get-value`, `get-unsat-core`, `get-proof`, `set-option` honouring five options |

A lane briefed from this file today would re-derive closed work or be told
not to touch what has already been measured.

Two items the tracks still carry as open were sized and deprioritised on
2026-08-21 and should carry that verdict: transcendentals, nested arrays and
parametric datatypes appear in 0 of 2,200 competition files; the CAV-2024
bit-blasting abstraction has an addressable set of 7 QF_BV files.

---

## 2. Performance instruments

### 2.1 What exists

**Micro-benchmarks: none.** No crate has a `benches/` directory; `criterion`,
`divan` and `#[bench]` appear nowhere in any `Cargo.toml` or source file
(hits for the word "criterion" are prose in `lra_theory.rs`, `simplex.rs` and
two tests). The "micro" tier named in the
[benchmarking methodology](../08-planning/benchmarking-and-performance-methodology.md)
is `corpus/micro/`, a directory of small SMT-LIB files run through the corpus
harness by `just bench-micro`, not a per-function timing harness.

**Full-solver timing: substantial.** The `axeyum-bench` harness emits
versioned artifacts (v14 and later) with `summary.par2_mean_s`, per-instance
`translate_ms` / `solve_ms` / `model_lift_ms`, and a
`summary.layer_attribution` block that splits the pure-Rust BV pipeline into
`bit_blast_share`, `cnf_encode_share`, `solve_share`, `model_lift_share` and a
`sat_dominates` boolean at threshold 0.5. Around it:

| Instrument | Measures | State on 2026-09-05 |
|---|---|---|
| 72 baselines, `bench-results/baselines/` | decide rate, PAR-2 vs Z3 4.13.3 per division | last refreshed 2026-08-25 |
| [`SCOREBOARD.md`](../../../bench-results/SCOREBOARD.md) | generated per-division decide%, DISAGREE, PAR-2 | 35 rows, 24 logics, 0 disagreements |
| [`PARITY.md`](../../../bench-results/PARITY.md) + `parity-details/*.tsv` | decided vs cvc5/Bitwuzla on pinned lists; per-file `axeyum_ms`, `z3_ms`, `unknown_kind`, `detail` | all 9 divisions stale, gate red |
| [`smtcomp-repro-20260721/`](../../../bench-results/smtcomp-repro-20260721/README.md) | full SMT-COMP scoring replica; QF_BV PAR-2 head-to-head vs cvc5 and Bitwuzla (same 19/24, ~3% slower) | one run, 2026-07-21 |
| `bench-results/frontier/*.json`, `progress_frontier.rs` | largest `N` decided in 4 s on five parametric families; machine calibration with `comparable` / `ratchetable` flags | five baselines, pinned 2026-08-25 |
| `axeyum-scenarios` + `scenario_scaling` / `scenario_pipeline_report` | oracle-free workloads reporting typed `BvLayerStats` | example binaries, not gated |
| 28 examples under `crates/axeyum-bench/examples/` | one-off profiles, probes, A/B tools (`preprocess_timing`, `cnf_core_bench`, `uf_pair_profile`, `xor_cdcl_probe`, …) | ad hoc |
| `criterion` `benches/` (§4 item 3), `just bench-criterion[-<crate>]` | function-level timing for the six named hot paths (`CdclT::solve`, `solve_with_drat_proof`, `tseitin_encode`, `Aig::and`, `Incremental::check`, `EGraph::merge`/`explain`) plus `TermArena` interning (D5's before/after instrument) | added 2026-09-05, one loaded-host run each, not yet a ratchet — see [`microbenchmarks-2026-09-05.md`](../08-planning/microbenchmarks-2026-09-05.md) |
| **timing ratchet** — `TIMING_*` baselines in `progress_frontier.rs`, `"timing"` block in `bench-results/frontier/*.json` | calibrated solve time (`solve_ms / scale`) at a few `N` pinned deep inside each frontier, against a committed ceiling = 1.5x the slowest of 8 measured sweeps | landed 2026-09-05 (recommendation 1, first slice); enforced only when `machine.comparable`, advisory otherwise |
| [`bench-results/sat-core-gate-b-20260905/`](../../../bench-results/sat-core-gate-b-20260905/README.md), `gate_b_sweep.rs` | BatSat/native/CaDiCaL/Kissat head-to-head on identical Axeyum-generated CNF (gate (b)) | one run, 2026-09-05 (p4dfa exhaustive, Noetzli a seeded 100-file sample) |

Layer attribution has already answered one methodology question. On the p4dfa
QF_BV family (`qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json`) the SAT
share is **0.974** (bit-blast 0.009, CNF encode 0.016); on Noetzli it is
~0.95; on `bench_ab` it is 0.24 and encoding dominates. So gate (a) of the
CDCL-priority decision, "does SAT time dominate", is family-dependent and is
true on the hard families.

### 2.2 What is missing

1. **Nothing fails when time regresses.** The frontier gate is capability at a
   fixed budget; the parity gate is decide count; the corpus gate is soundness.
   A PAR-2 regression on a committed baseline is visible only if someone
   re-reads the JSON. There is no timing ratchet.

   *Addendum, 2026-09-05 (appended, the finding above stands as written):* a
   first slice now exists. `progress_frontier.rs` carries a per-family
   `TimingBaseline` — a few `N` pinned deep inside the frontier, a calibrated
   total, and a committed ceiling — and fails the `frontier` step of
   `scripts/check.sh` and `just frontier` when that total worsens beyond a band
   measured over eight sweeps. It reads the curve the capability sweep already
   produces, so it costs no extra solving, and it is advisory on exactly the
   runs the capability ratchet is advisory on. What it does **not** yet cover is
   the 72 `bench-results/baselines/` PAR-2 means, which remain compared to
   nothing.
2. **Layer attribution exists only on the BV path.** `BvLayerStats` is typed
   and good; there is no equivalent for the arithmetic, EUF or string routes
   (time in propagate vs. conflict analysis vs. simplex pivots vs. explanation).
   The 2026-08-21 linear-arithmetic diagnosis classified 800 files by hand from
   per-file TSVs because no instrument said where the 24 seconds went.
   *(2026-09-05, lane `perf-route-timing`: instrumented — `TheoryLayerStats` in
   `crates/axeyum-solver/src/layers.rs`, collected by `crate::cdclt::CdclT`
   behind an off-by-default `TheoryLayerStatsGuard`; `simplex_pivots` stays
   `None` until a concrete theory adapter exposes a pivot count.)*
3. **`RouteTrace` carries no timings.** `route_trace.rs` has no elapsed or
   duration field; a declined route's cost is invisible.
   *(2026-09-05, lane `perf-route-timing`: instrumented — `RouteTrace::elapsed`/
   `total_elapsed` and the opt-in `RouteTrace::to_json_with_timing`; the
   default `RouteTrace::to_json` is unchanged.)*
4. **Gate (b) — MEASURED 2026-09-05, mixed result.** The methodology makes
   the native SAT core's priority contingent on (a) SAT dominance and (b) a
   consistent gap between the best Rust adapter and CaDiCaL/Kissat on
   axeyum-generated CNF. (a) was already measured true on p4dfa and Noetzli.
   (b) is now measured: on p4dfa (exhaustive, 113/113 files, 20s budget)
   Kissat/CaDiCaL decide 10-11 files vs. 4-6 for BatSat/native — a real but
   modest gap (six files out of 113); on a 100-file seeded Noetzli sample the
   gap nearly vanishes (86-89/100 across all four engines). The native proof
   core is never worse than BatSat and sometimes better, so this data argues
   against BatSat as the stronger in-tree engine if either becomes the
   default. Zero cross-engine disagreements, zero invalid models. Full
   writeup: [2026-09-05 gate (b)
   note](2026-09-05-gate-b-sat-core-measured.md); artifact:
   [`bench-results/sat-core-gate-b-20260905/`](../../../bench-results/sat-core-gate-b-20260905/README.md).
5. **No profiling recipes.** Nothing in `scripts/`, the `justfile` or the
   contributor guide invokes `perf`, `samply`, `flamegraph`, `dhat` or
   `heaptrack`.
6. **Head-to-head timing is stale.** The only PAR-2 comparison against cvc5
   and Bitwuzla on identical files is the 2026-07-21 replica.

---

## 3. Architecture

### 3.1 Where the design is strong

The layering is what
[`docs/internals/architecture.md`](../../internals/architecture.md) says it is:
interned term arena, rewrite, dispatch, bit-blast to an AIG with its own
structural-hash table (`AndUniqueTable`, open-addressed, no `HashMap`),
Tseitin to a flat clause vector, SAT, with lift maps retained so every `sat`
replays against the original terms.

The native proof-producing CDCL core
([`crates/axeyum-cnf/src/proof_sat.rs`](../../../crates/axeyum-cnf/src/proof_sat.rs),
2,961 lines) is a credible modern design: a flat clause arena with per-clause
headers, blocking-literal watch lists, VSIDS with geometric decay and rescale,
phase saving plus target rephasing, Luby and EMA-glue restarts with
Glucose-style blocking, LBD glue tiers, and `reduce_db`. The LRAT route
(ADR-0613) runs the fast backward checker as an *untrusted* hint producer and
lets the small linear `check_lrat` accept, so the trusted base shrinks while
the checking rate rose ~106x. That is the project's identity sentence applied
correctly.

CNF preprocessing exists as separate passes: bounded variable elimination
(`bve.rs`), subsumption (`simplify.rs`), vivification (`vivify.rs`), XOR
extraction with GF(2) elimination (`xor_*.rs`), and cube-and-conquer
certificate composition (`cube.rs`).

The CDCL(T) spine ([`cdclt.rs`](../../../crates/axeyum-solver/src/cdclt.rs))
drives genuinely online theories: EUF on a real e-graph (`euf_egraph.rs`),
LRA on a warm Dutertre and de Moura simplex (`lra_online.rs`), LIA
(`lia_online.rs`), difference logic by negative-cycle detection
(`dl_online.rs`), strings (`string_theory.rs`), and two combined theories
(`combined_theory.rs`, `combined_theory_lia.rs`).

### 3.2 Debts that cost performance

Each item names the file, the measurement, and the division it touches.

**D1. Three Boolean search engines, and the weakest carries the weakest
divisions.**

| Engine | File | Clause storage | Heuristics | Where it runs |
|---|---|---|---|---|
| BatSat via RustSAT | `axeyum-cnf` adapter | external | MiniSat-class | default for `SatBvBackend` (QF_BV) |
| native proof core | `proof_sat.rs` | flat arena + headers, blocking literals | VSIDS, target rephase, EMA-glue + Luby restarts, LBD tiers | only when `native_cdcl` or `prove_unsat` is set |
| CDCL(T) driver | `cdclt.rs:189` `struct CdclT` | `clauses: Vec<Vec<Lit>>` (`cdclt.rs:276`) | own VSIDS/restart loop | every arithmetic, EUF, string and combined route |

Every division below 70% in §1.2 runs on the third engine. It has no clause
arena, no blocking literals and no in-search simplification. The
benchmark gate that keeps BatSat as the BV default has never been asked about
this engine, and the modern core sits unused on the proof path.

**D2. The theory interface is too thin for an efficient CDCL(T).** The trait
(`euf_egraph.rs`, `pub trait TheorySolver`) has four methods:

```rust
fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>>;
fn push(&mut self);
fn pop(&mut self);
fn propagate(&self) -> Vec<TheoryProp>;
```

Consequences, each measured or documented elsewhere in the tree:

- No final-check hook, so a theory cannot separate a cheap partial check from
  a complete one. `lra_online.rs`'s own header says `assert` re-decides
  feasibility on the warm simplex on every call.
- `propagate` takes `&self` and returns a freshly allocated `Vec` per call:
  no driver-owned propagation queue, and the theory cannot mark what it has
  already propagated.
- Conflicts and explanations are eager `Vec<TheoryLit>`; there is no lazy
  explanation.
- Dynamic atom registration is not in the trait; `cdclt.rs:191` notes that
  "dynamic theory variables may follow Tseitin auxiliaries" and the alignment
  is managed by side tables.

This is the structural reason the 2026-08-21 diagnosis found "slow CDCL(T)"
in QF_LRA and found `MAX_ONLINE_LRA_ATOMS = 1_024` load-bearing (removing it
gave 0 new decides and 54 memory aborts). Z3's theory interface carries final
check, new-equality and new-disequality callbacks, lazy explanation and
relevancy for exactly these reasons.

**D3. Dispatch is a hand-ordered portfolio of one-shot routes.**
[`auto.rs`](../../../crates/axeyum-solver/src/auto.rs) is 9,638 lines with 52
distinct route labels (`grep -oE '"[a-z]+(-[a-z0-9]+)+"' | sort -u`). Each
route re-normalises and re-lowers its own view of the query: 15 `lower_terms(`
and 6 `tseitin_encode(` call sites in the solver crate outside tests. The
deadline is shared (`config_with_remaining_deadline`) but the work is not: a
declined route's encoding is discarded. The 7,881-line warm engine
(`incremental.rs`) is referenced zero times from `auto.rs`. Part of what the
ledger records as QF_IDL and QF_RDL timeouts is time spent in earlier declined
routes; the diagnosis found 6 s reserved for `lia-dpll`, which then declines
instantly on a size constant it could have evaluated at `t = 0`.

**D4. Rationals are two `i128` fields.**
[`rational.rs:12`](../../../crates/axeyum-ir/src/rational.rs) is
`struct Rational { num: i128, den: i128 }`; `simplex.rs:18` maps overflow to
`SimplexOutcome::Unknown`. Consequences on the record: the parser rejects 26
QF_UFLIA files carrying 2^256 EVM literals (cvc5 decides 6 of them); the
Handelman lane needed a carried relaxation to fit `1.6·10^57` into range; the
LRA atom cap is partly an overflow guard rather than a memory bound. The
standard design is an `i128` fast path with a big-integer slow path;
`axeyum-ir/src/poly_big.rs` already holds bignum polynomial code and `wide.rs`
holds `WideUint` for bit-vectors, so the precedent exists in both directions.
The gap analysis rates this ADR-sized because every arithmetic route is built
on `Value::Int(i128)`.

**D5. Determinism is bought with ordered maps and paid for again with a slow
hasher.** Counts of type-position occurrences in `crates/*/src`:

| Crate | `BTreeMap` | `BTreeSet` | `HashMap` | `HashSet` |
|---|---:|---:|---:|---:|
| axeyum-solver | 550 | 355 | 311 | 160 |
| axeyum-cnf | 25 | 14 | 4 | 1 |
| axeyum-ir | 3 | 0 | 14 | 1 |
| axeyum-egraph | 0 | 0 | 8 | 2 |
| axeyum-aig | 0 | 0 | 0 | 0 |

The term intern table (`arena.rs:43`, `intern: HashMap<TermNode, TermId>`)
uses `std::collections::HashMap` with the default SipHash. No fast
deterministic hasher (`rustc-hash`, `ahash` with a fixed seed) and no
insertion-ordered map (`indexmap`) is a workspace dependency. The combination
is slow on both sides for no determinism gain: `BTreeMap` in hot paths is a
known constant-factor tax, and SipHash on the intern table is the other half
of the same trade.

*Measured 2026-09-05* (recommendation 6, scoped to `axeyum-ir` only): the
intern table and six other lookup maps now use `rustc-hash`'s `FxHashMap`
(`axeyum-ir/src/fast_map.rs`); the audit for this pass also found and fixed
two live iteration-order determinism bugs (`Assignment::functions`/
`real_div_zeros` returned raw hash order to callers). On a 16.8 MiB public
QF_BV file the throughput delta was small and noisy under fleet load
(pooled median ~2%, pooled min ~7% faster; see
[2026-09-05-intern-table-hasher-measured.md](2026-09-05-intern-table-hasher-measured.md)),
which does not by itself justify extending the sweep to `axeyum-solver`'s
~470 hot-path maps — that needs recommendation 3's micro-benchmarks on a
quiet host, not another CLI wall-clock reading.

**D6. Inprocessing is off by default and is preprocessing.**
`backend.rs:372` sets `cnf_inprocessing: false`; `sat_bv_backend.rs:232-245`
runs the passes once before search. Nothing interleaves simplification with
search in any of the three engines.

**D7. Single-threaded search by design.** `rayon` is a dependency of
`axeyum-bench` only; in-solver threading appears in `cube.rs`, the quantifier
instance-set reconstruction and `incremental.rs`. Acceptable under the
determinism promise, but cube-and-conquer here is a certificate-composition
feature rather than a search accelerator, while Z3 5.x ships shared-search-tree
threading.

**D8. The theory core is one dependency cycle.** 26 modules, 59,175 lines,
gate red (§1.3). The [decomposition note](../../refactor-2026-08/03-solver-decomposition.md)
concluded no crate cut yields a small trusted core today. The performance
consequence is that the CDCL(T) spine cannot be built, tested or benchmarked
apart from dispatch.

---

## 4. Recommendations, ordered by measured leverage

1. **Turn PAR-2 into a ratchet.** `progress_frontier.rs` already carries
   machine calibration and a comparable-or-advisory verdict. Reuse that frame
   to fail a committed baseline whose `par2_mean_s` worsens beyond the
   calibrated noise band. Until this exists, every timing number in
   `bench-results/` is advisory.
2. **Measure gate (b).** Dump axeyum CNF from the p4dfa and Noetzli families
   (SAT share 0.97 and 0.95) and run BatSat, the native core, CaDiCaL and
   Kissat on identical DIMACS. About a day of work; it decides whether the
   native core becomes the default and whether D1's third engine should be
   replaced rather than tuned.
3. **Add micro-benchmarks for six hot paths**, bound to the same calibration
   scheme so they can gate: `CdclT::propagate`, `proof_sat` propagate,
   `tseitin_encode`, `AndUniqueTable` insert, simplex pivot, e-graph merge
   with explain.
4. **Widen the theory trait and unify the engines.** Add final check, lazy
   explain, a driver-owned propagation queue and dynamic atom registration;
   then move `CdclT` onto the `proof_sat` clause arena or make the native core
   the CDCL(T) driver's search. This is the Track 1 P1.5 keystone the roadmap
   already names, and it is the QF_IDL/QF_RDL/QF_LRA deficit by another name.
5. **Bignum fallback for `Rational`.** One ADR, then `simplex.rs` and the
   parser. Unblocks the 26 QF_UFLIA files and lets the LRA atom cap become a
   memory bound.
6. **Swap the hasher.** A seeded fast hasher plus `indexmap` where iteration
   order is observable; measure on the intern table first.
7. **Stage attribution for theory routes and elapsed time per route in
   `RouteTrace`.** The next linear-arithmetic diagnosis should not need a
   hand-built TSV.
8. **Profiling recipes in the `justfile`** (`samply` or `perf record` plus
   `flamegraph`) with the pinned-core advice the frontier note already gives.
9. **Re-measure the board and rewrite the A-programme blocks** (§1.3, §1.4).
   Not a performance item, but every item above is priced off numbers that are
   currently 15 to 19 days old and a queue that points lanes at closed work.

---

## 5. What this review does not establish

- No timing was re-run here. Every number is read from a committed artifact
  dated 2026-07-21 through 2026-08-25, or from source at `0d38d5beb`.
- The frontier ratchets and the corpus sweep were not executed; their state
  is unknown.
- The claim that `CdclT` is the slowest of the three engines is inferred from
  its data structures and from the diagnosis notes, not from a head-to-head
  on identical CNF. Recommendation 2 is the measurement that would settle it.
