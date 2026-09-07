# Boolean core: benchmarks, the per-conflict throughput gap, and the cost of a certificate

Lane `bench-boolean-core`, running diary. Started 2026-09-07.

This file is written **as the work happens**, including the entries where the
expectation recorded before a measurement turned out to be wrong. Entries are
appended, never rewritten: a corrected prediction stays visible next to its
correction.

## 0. The question, and what was already known

Three prior artifacts define the starting point, and none of them is repeated
here:

- [`bench-results/sat-core-gate-b-20260905/`](../../../bench-results/sat-core-gate-b-20260905/README.md)
  — on the 113-file p4dfa slice at a 20 s budget the decided counts are
  **Kissat 11, CaDiCaL 10, native proof core 6, BatSat 4**. Its own "what this
  does not establish" says, verbatim: *"No profiling was done."*
- [`2026-09-05-native-core-vs-kissat-search-stats.md`](../11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md)
  — on the 8 non-outlier files all three engines decide, the native core needs
  a median **1.38x more conflicts** than Kissat and processes them at a median
  **0.637x** Kissat's rate, i.e. Kissat does roughly **1.57x more conflicts per
  second**. It also refuted the strong "it is all inprocessing" guess: Kissat's
  own profiler attributes 45.5-100% (mean 58.7%) of its wall time to core
  search on every file measured.
- The same note's closing limitation is this lane's entry point:

  > **The native core's own time breakdown is not measured at all** — no
  > decision counter, no propagation counter, no restart counter exists in
  > `ProofSearchProgress` to compare against Kissat's `search%`/`probe%` split
  > on the native side. […] Adding that instrumentation is a production change
  > to `axeyum-cnf` (`ProofSearchProgress`), explicitly out of scope for that
  > measurement lane — **a natural next step for a lane that owns that crate.**

So the gap is measured and its *magnitude* is not in question. What is missing
is a cause named at the level of a function and a data-structure choice.

`perf` is not available on this fleet, so the method is counters plus targeted
A/B, not a flamegraph.

## 1. Pre-registered expectations (written before any measurement)

Recorded here so that being wrong is visible later. These came from reading
`proof_sat.rs` only — no measurement yet, and reading is exactly the evidence
class this repository warns is weakest.

**H1 — `analyze` allocates and zeroes an O(#variables) array on every
conflict.** `Cdcl::analyze` opens with

```rust
let mut seen = vec![false; self.assign.len()];
```

That is one heap allocation plus one `memset` of `nvars` bytes **per
conflict**, regardless of how few variables the conflict actually touches.
MiniSat, BatSat, CaDiCaL and Kissat all keep a persistent mark array and clear
only the entries they touched. On a p4dfa instance with ~10^5-10^6 variables
this is 100 KB-1 MB of memset per conflict, and it also evicts the working set
the same conflict is about to read. Predicted to be the single largest
contributor to the per-conflict gap on large instances, and — critically —
**invisible on a small instance**, because on PHP(7,6) with 42 variables it is
42 bytes.

**H2 — `analyze` heap-allocates once per resolution step.** Inside the
resolution loop:

```rust
let lits = self.lits(clause_id).to_vec();
```

a fresh `Vec` per antecedent clause walked, purely to satisfy the borrow
checker while `bump_var` mutates `self.activity`. Predicted second largest.

**H3 — `Watch` is 16 bytes where the reference solvers use 8.**
`Watch { clause: CRef /* usize */, blocker: CnfLit }`. `CRef` is `usize` = 8
bytes; with `CnfLit` at 4 bytes and alignment 8 the struct is 16. CaDiCaL and
Kissat use a 32-bit clause reference and a 32-bit blocker, 8 bytes total.
Watch-list traversal is the single hottest memory stream in a CDCL solver, so a
2x inflation of it costs directly. Predicted third.

**H4 — `watches: Vec<Vec<Watch>>` is a pointer chase per literal.** Each
literal's watch list is a separately heap-allocated `Vec`, so visiting a
literal's watchers costs a dependent load before any watcher is read, and the
lists are scattered across the allocator's arena rather than laid out together.
Kissat uses one flat watch arena. Predicted real but smaller than H1-H3, and
much harder to fix.

**H5 — `compute_lbd` allocates a `Vec` per learned clause** and sorts it.
Predicted small (learned clauses are short) but free to fix.

**Ranking predicted before measuring: H1 > H2 > H3 > H4 > H5.**

**H6 — DRAT logging overhead.** Predicted 5-15% of search wall time for the
in-memory `Vec<DratStep>` sink. Prediction recorded because no authoritative
published figure exists for DRAT logging overhead in CaDiCaL or Kissat, so ours
is worth publishing whatever it is.

## 2. The methodological trap this lane was warned about, restated

Measured in this repository on 2026-09-06: `cdclt_solve_php_6_7` (42 variables)
said engine A beat engine B by 3.4%, while on a 330,000-variable real skeleton
the same swap decided 4 **more** files at 12.9% better PAR-2 — opposite
directions.

H1 above predicts *exactly* that failure mode for this lane's own headline
bench: `proof_sat_solve_php_6_7` has 42 variables, so the O(#vars) memset it
would need to expose is 42 bytes and it will show approximately nothing. **If
H1 is right, the existing committed micro-benchmark is structurally incapable
of detecting the largest defect in the file it benchmarks.** That prediction is
recorded here before the measurement so that it counts either way.

Consequence for the benches this lane adds: every one states the real workload
it proxies, and the headline ones are validated against real corpus DIMACS
(p4dfa) rather than against pigeonhole.

## 3. Log

*(appended as the work happens)*

### 2026-09-07 — lane opened

Read `proof_sat.rs` (6,280 lines), the gate-b artifact, and the three prior
design-review measurement notes. Wrote §1's expectations before touching a
build. Nothing measured yet.
