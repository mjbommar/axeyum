# Lane: qfbv-sat-misses (roadmap 3.9)

<!-- plan-section: lane-status -->

Status: complete (2026-09-10). The class is gated by a decide-frontier ratchet
and the miss is attributed. Roadmap 3.9 moves from "not started" to **MEASURED,
BUILD (three bounded items)** — and the cause is **not** encoding size.

## What this lane did

Item 3.9 asked which of encoding size, search, or admission costs us 43 of 166
real satisfiable QF_BV instances at a 10 s budget. All three appear, in disjoint
sub-classes, and the largest one is none of them: **on a measurable part of this
class we compute the right answer and then discard it.**

## The substantive findings

1. **We decide instances we report as `unknown`.** Nine instances — two of them
   real SMT-LIB files through the shipping front door — return `unknown` at a
   10 s budget after spending **29-43 s**, and `sat` at 300 s after spending the
   **same** time. `sat_bv_backend.rs:327` re-reads the clock after
   `primary_sat_search` returns and discards the result. The overrun is already
   paid; a late `sat` is replay-checked exactly like a timely one.
2. **The budget is not enforced during that search.** The CDCL core tests its
   deadline every `DEADLINE_CHECK_INTERVAL = 1_024` **conflicts**
   (`proof_sat.rs:62`, `:3453`); the whole search here is **under 256 conflicts
   at 28-51 conflicts/second**, so the test can never fire. Overrun **1.15x to
   8.01x**.
3. **Encoding size is refuted by our own data.** `bvwide-mul-w01024` has
   **8,891,930** CNF clauses and decides in 5.9 s; `bvwide-addcmp-w12288` has
   **430,038** — 20.7x fewer — and does not. At the frontier, lowering plus CNF
   is **1.0%** of the budget. Circuit ~`w^1.0`, wall clock ~`w^1.8`, cost per
   conflict ~`w^2.0`.
4. **Admission over-refuses once, measurably.** `ABSOLUTE_CLAUSE_CEILING`
   (`sat_bv_backend.rs:2154`) refuses `bvwide-mul-w02048` on a *projected*
   100,681,731 clauses; the real encoding is **35,609,626** — estimator **2.83x**
   pessimistic, instance **1.80x under** the cap. Admitted, it decides in 41.0 s.
5. **`BitLoweringMode::DemandSliced` removes ZERO gates here** (byte-identical
   AIG and CNF on both families) and costs **51.6x** more lowering. Item 3.3's
   carve-out 1 closes DO NOT BUILD. The off-by-default is **not** stale: every
   operator in this class is a conservative *barrier* in ADR-0157's own
   exact-propagation class, so there is nothing to slice.

Two questions the item asked by name: the 19 that never reach the solver are
**not** an admission gate (`auto.rs:1953`, `:1958`, `:2408` are timeouts;
`node_budget`/`cnf_clause_budget` are never assigned on the shipping path), and
there is **no width threshold** in the measured range — at 300 s the whole real
`ndist.b` family decides, to width 29,980.

## Landed changes

| change | where |
| --- | --- |
| the real SMT-LIB class, 21 files, all `:status sat` | `corpus/public-curated/non-incremental/QF_BV/smtlib-pspace-ndist/` |
| width-graduated corpus, 29 files, status by construction | `corpus/public-curated/synthetic/QF_BV/width-graduated/` |
| its generator, witness checked before emission | `scripts/gen-graduated-qfbv-width.py` |
| the decide-frontier ratchet + soundness/non-vacuity controls | `crates/axeyum-solver/tests/qfbv_width_frontier.rs` |
| the per-stage attribution probe | `crates/axeyum-bench/examples/qfbv_sat_attribution.rs` |
| the measurement | `docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md` |
| roadmap row 3.9 rewritten | `docs/solver-comparison-2026-09/11-roadmap-and-plan.md` |

## Verification

- `qfbv_width_frontier` **3 passed**, and it is known to discriminate: the first
  draft set `ADDCMP_FLOOR` from the release frontier and **exactly one** of the
  three tests died, reporting `frontier fell to width 1024`.
- `corpus_regression` 2 passed; `axeyum-bv --lib` 34 passed; `axeyum-solver
  --lib --features full` **1678 passed**; clippy `-D warnings` clean on both
  touched crates; `cargo fmt --all --check`, `check-links.sh` and
  `check-merge-hygiene.sh` all exit 0; `cargo check --workspace --all-targets`
  green after merging local main.
- `progress_frontier` passed 12/12 but its artifact reports
  `"comparable": false, "ratchetable": false` — **ADVISORY ONLY, ratchet not
  enforced**, so that green is not evidence. Artifacts restored, not committed.

## Caveats a reader must carry

- **Item 3.1's 166-instance sample is not reproducible from its recipe.**
  Re-running it gives 200 satisfiable files, not 168. The miss set was
  reconstructed **by name** from item 3.3's per-file tables (42 of 43 recovered,
  all `:status sat`); **six basenames are ambiguous** across `sage*/`
  directories and the `Sage2` copy was taken. Only the **9 at ≤1 MB** were
  measured. Every "43" is item 3.1's number quoted, not re-derived.
- A frontier is a function of the budget, the build profile **and** the entry
  point. Release/backend: 8,192 and 1,024. Debug/front-door (what the gate
  runs): 1,024 and 1,024. The floors are calibrated to the second.

## Next

- **Keep a completed result that arrives late** (`sat_bv_backend.rs:327-332`).
  Nine of nine flip. Needs a recorded decision — the budget stops being an upper
  bound on wall time, which it already was not — and an examination of the
  `unsat`, proof-carrying and incremental routes that this lane did not do.
- **Make the deadline cadence time-bearing** (`proof_sat.rs:62`, `:3453`). A
  propagation-count cadence beside the conflict one keeps the determinism the
  current design protects.
- **Re-measure the Tseitin multiplier in `estimate_blast_clauses`**
  (`sat_bv_backend.rs:2163`) — 2.83x high on `bvmul`. Do **not** simply raise
  `ABSOLUTE_CLAUSE_CEILING`; the 8x gate charge exists because a 4,096-bit
  `bvmul` OOM'd during lowering.
- **The conflict rate itself** — 28-51/s against a reference `10^4`-`10^6`, with
  cost per conflict quadratic in the width. Wants its own item and a profile.
  First thing to look at: these searches are propagation-bound, and the `addcmp`
  circuit is a `w`-stage ripple-carry chain.
- The **33 unmeasured named misses** (3-90 MB), and the **19** that never reach
  the solver, are both untouched here.
