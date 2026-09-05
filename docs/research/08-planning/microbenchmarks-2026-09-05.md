# Micro-benchmarks, 2026-09-05

Status: measured
Companion to the
[2026-09-05 design review](../11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md),
§2.1 ("Micro-benchmarks: none") and §4 item 3.

## What this is

Before this date no crate had a `benches/` directory and neither `criterion`,
`divan`, nor `#[bench]` appeared anywhere in the workspace. This note records
the first run of seven `criterion` (`harness = false`) micro-benchmarks added
across five crates, each on a fixed, committed or deterministically-seeded
input:

| # | Bench | Crate | Target | Hot path |
|---|---|---|---|---|
| 1 | `cdclt_solve_php_6_7` | `axeyum-solver` | `cdclt_propagate` | `CdclT::solve` (Boolean search only, trivial theory) |
| 2 | `proof_sat_solve_php_6_7` | `axeyum-cnf` | `proof_sat_solve` | native proof-producing CDCL core, `solve_with_drat_proof` |
| 3 | `tseitin_encode_bvmul16` | `axeyum-cnf` | `tseitin_encode` | `tseitin_encode` on a 16-bit multiplier AIG |
| 4 | `aig_and_construction_4000_nodes` | `axeyum-aig` | `and_unique_table` | `Aig::and` / `AndUniqueTable` structural hashing |
| 5 | `simplex_incremental_check_feasible_lp` | `axeyum-solver` | `simplex_pivot` | `Incremental::check` (Dutertre–de Moura pivot loop) |
| 6 | `egraph_congruence_chain_merge_explain` | `axeyum-egraph` | `congruence_chain` | `EGraph::merge` + `EGraph::explain` |
| 7 | `arena_intern_20000_bv_const` | `axeyum-ir` | `arena_intern` | `TermArena` interning (`intern: HashMap<TermNode, TermId>`, default `SipHash`) |

Benches 1 and 2 run over the **same committed input** —
`corpus/micro-cnf/unsat-pigeonhole-6-7.cnf`, pigeonhole formula PHP(7,6): 7 pigeons into
6 holes, UNSAT, 42 variables / 133 clauses — so their medians are directly
comparable, not an apples-to-oranges reading. The existing
`corpus/micro-cnf/sat-forced.cnf` and `unsat-unit.cnf` are 2-clause fixtures
(one status literal each); neither has enough search depth to separate
propagate/decide/backjump/restart cost from fixed per-call overhead, so a
fixed pigeonhole formula was generated instead and committed alongside them.

Bench 7 is deliberately named `arena_intern`, not renamed to something more
specific: another lane is about to swap the term arena's hasher away from
`std`'s default `SipHash` (D5 in the design review), and this bench is that
lane's before/after instrument on this exact table.

## Method

- Host: `s4` (the shared dev box), 16 logical CPUs.
- Pinned to performance cores with `taskset -c 0-7` via `just
  bench-criterion`/`just bench-criterion-<crate>`, matching the pinning
  advice already established for the frontier ratchets
  ([reference-frame note](frontier-ratchet-reference-frame.md)).
- Commit: `fb177bb4e` for the `axeyum-aig`, `axeyum-cnf`, `axeyum-egraph`,
  and `axeyum-ir` benches (the `axeyum-aig` bench needed one fix commit
  after its first run panicked — see "What the first run found" below — so
  those five numbers postdate that fix). The `axeyum-solver` benches
  (`cdclt_solve_php_6_7`, `simplex_incremental_check_feasible_lp`) were run
  at `47093a877`, one commit later: `corpus/micro-cnf/php-6-7.cnf` was
  renamed to `unsat-pigeonhole-6-7.cnf` in between (see "The corpus-file
  rename" below) to fix an unrelated existing test; the CNF bytes did not
  change, so the two sets of numbers are still a valid same-input
  comparison.
- Load average (1 min, from `/proc/loadavg`) immediately before the sweep:
  17.9-36.7 across the individual runs (it moved between runs — this host
  runs many concurrent agent lanes; `cargo-serialized.sh`'s own lock queue
  had 4-5 other lanes' cargo invocations waiting at points during this
  session). **This host was heavily loaded during this run** (other
  lanes were building concurrently, consistent with
  [`serialize-heavy-compute`](../../contributor-guide/measurement-hazards.md)
  guidance that this box is shared). Per the frontier-ratchet reference-frame
  convention, a run at this load is **ADVISORY ONLY**: it establishes that
  every bench compiles, runs, and reports a plausible nonzero timing, and it
  is the first CdclT-vs-native-core ratio ever measured, but it is **not** a
  baseline to gate a future run against without a matching-load re-measure.
- Command run once per crate: `taskset -c 0-7 cargo bench -p <crate>
  [--features bench-internals] --bench <name> -- --warm-up-time 1
  --measurement-time 3` via `scripts/cargo-serialized.sh bench …` (the
  workspace-mandated wrapper for heavy cargo invocations).
- "Median" below is `criterion`'s own reported point estimate for `time`
  (criterion reports mean with confidence interval by default at this sample
  size; the `[time: ...]` line's middle value is quoted as the median
  estimate per `criterion`'s own terminal summary).

## What the first run found

The `axeyum-aig` bench's first run **panicked**, not merely reported a
number: it asserted `and_requests == AND_NODE_COUNT` (every one of 4,000
`Aig::and` calls counted exactly once), and hit `4004 != 4000`. Reading
`Aig::and`'s source explains why: `simplify_and_by_absorption` can
recursively call `and` again internally when an operand's structure matches
an OR/consensus pattern, which the seeded pool of literals and their
negations does occasionally produce. The invariant that actually holds is
`and_requests >= AND_NODE_COUNT`; the bench was fixed (commit `fb177bb4e`)
and reruns clean. Recorded here because a bench that silently reported a
wrong number instead of panicking would have been worse than no bench.

## The corpus-file rename

`corpus/micro-cnf/php-6-7.cnf` (the pigeonhole formula generated for these
benches) was renamed to `unsat-pigeonhole-6-7.cnf` one commit after it
landed. `axeyum-cnf` already has an existing self-test,
`dimacs_micro_corpus_solves_through_sat_trait` (`src/lib.rs`), that
enumerates every `.cnf` file under `corpus/micro-cnf/`, asserts the count is
exactly 2 (now 3), and picks its expected SAT/UNSAT verdict per file from
whether the filename contains the substring `"unsat"` (matching the existing
`sat-forced.cnf` / `unsat-unit.cnf`). `php-6-7.cnf` is UNSAT but its name did
not contain `"unsat"`, so that test would have taken the SAT branch and
panicked on the real `Unsat` result. Renamed to fit the convention, bumped
the count assertion to 3, and reran the test:
`cargo test -p axeyum-cnf --lib dimacs_micro_corpus_solves_through_sat_trait`
→ 1 passed (commit `47093a877`).

## Results

| Bench | Target crate | time [min median max] | Median |
|---|---|---|---|
| `aig_and_construction_4000_nodes` | `axeyum-aig` | `[311.07 µs 323.62 µs 335.70 µs]` | **323.6 µs** |
| `tseitin_encode_bvmul16` | `axeyum-cnf` | `[230.81 µs 238.79 µs 246.89 µs]` | **238.8 µs** |
| `proof_sat_solve_php_6_7` | `axeyum-cnf` | `[5.3265 ms 5.6819 ms 6.0565 ms]` | **5.682 ms** |
| `cdclt_solve_php_6_7` | `axeyum-solver` | `[39.122 ms 39.606 ms 40.111 ms]` | **39.606 ms** |
| `simplex_incremental_check_feasible_lp` | `axeyum-solver` | `[258.01 µs 267.71 µs 278.35 µs]` | **267.7 µs** |
| `egraph_congruence_chain_merge_explain` | `axeyum-egraph` | `[1.0489 ms 1.6429 ms 2.4302 ms]` (11% outliers — noisy under load) | **1.643 ms** |
| `arena_intern_20000_bv_const` | `axeyum-ir` | `[6.8131 ms 7.0235 ms 7.2480 ms]` | **7.024 ms** |

`egraph_congruence_chain_merge_explain`'s wide interval (1.05-2.43 ms, 11
outliers of 100 samples, 10 of them "high severe") is a direct symptom of
the host load noted above, not a property of the code; a rerun on an idle
host would be expected to tighten it substantially.

## The CdclT-vs-native-core ratio

On the identical `unsat-pigeonhole-6-7.cnf` input (PHP(7,6), UNSAT, 42
vars / 133 clauses), `CdclT::solve` (`cdclt_solve_php_6_7`, driven by a
trivial always-consistent theory so only the Boolean search is measured)
took a median of **39.606 ms**; the native proof-producing core
(`proof_sat_solve_php_6_7`, `solve_with_drat_proof`) took a median of
**5.682 ms**. **`CdclT` is ~7.0x slower than the native core on this
instance** (39.606 / 5.682 = 6.97).

This is the first direct, identical-input comparison between the two
Boolean search engines named in the design review's D1 (`axeyum-solver`'s
`CdclT` — `Vec<Vec<Lit>>` clause storage, no blocking literals, own
VSIDS/restart loop — versus `axeyum-cnf`'s native proof-producing core —
flat clause arena with per-clause headers, blocking-literal watch lists,
VSIDS with geometric decay, phase saving plus target rephasing, Luby and
EMA-glue restarts, LBD tiers, `reduce_db`). It is a **single instance at
default settings under high host load** — not a corpus sweep, not a
statistically powered comparison, and not by itself sufficient to decide
recommendation 4 (widen the theory trait and move `CdclT` onto the
`proof_sat` arena, or make the native core the CDCL(T) driver's search).
Recommendation 2 in the design review (BatSat/native-core/CaDiCaL/Kissat on
identical DIMACS from real hard families such as p4dfa and Noetzli) is the
measurement that would actually settle engine choice; this ratio is a first
data point pointing at the same question from the small end.

## What this does not establish

- No timing ratchet exists yet. This tier does not gate anything;
  recommendation 1 in the design review (reuse the `progress_frontier`
  calibration frame to fail a regressing baseline) has not been built for
  it. See the "Micro tier" paragraph added to
  [`benchmarking-and-performance-methodology.md`](benchmarking-and-performance-methodology.md).
- One run each, on a loaded shared host. Every number here is a single
  `criterion` sample run, not a repeated/statistically-controlled
  measurement; treat every figure as an order-of-magnitude read, not a
  precise baseline.
- Full `criterion` HTML reports were not generated (`cargo_bench_support`
  only, no `plotters`/`html_reports` — see the `criterion` dependency
  comment in the workspace `Cargo.toml`); the numbers here are read from
  the terminal summary `criterion` itself prints, not from a report file.
