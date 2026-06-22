# Benchmark Results

Committed benchmark artifacts that serve as project evidence. Scratch runs stay
under `bench-results/local/`, which is gitignored.

## Current authoritative record (2026-06-20)

- [`baselines/qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json`](baselines/qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json):
  **the headline QF_BV head-to-head.** Pure-Rust `sat-bv` (rustsat-batsat,
  CNF inprocessing on, node/CNF budgets 3M var / 8M clause) vs **z3 4.13.3** on
  the full public `QF_BV/20221214-p4dfa-XiaoqiChen` slice (113 files), 20 s each.
  Result: **axeyum 8 sat / 105 unknown / 0 unsat, DISAGREE = 0, replay failures = 0**;
  the Z3 oracle agrees on all 7 it was compared against. PAR-2 mean 37.6 s. This
  is **parity, both hard-capped** — axeyum uniquely decides `string1x8.3` (z3
  times out @20.5 s), z3 uniquely gets `compose.p3`/`s2_nr4`, and the other 105
  defeat both. Layer attribution confirms the gap is **search-bound, not encoding**:
  SAT solve is 97.4 % of pipeline time; bit-blast + CNF-encode + model-lift
  together are < 2.6 %. The companion [`qf-bv-p4dfa-z3-standalone-20s.json`](baselines/qf-bv-p4dfa-z3-standalone-20s.json)
  is the Z3-only run at the same budget.
- **Fair multi-config comparison family** (2026-06-18 → 06-20): the
  `qf-bv-p4dfa-fair-*` baselines isolate single levers at matched budgets vs Z3 —
  plain `sat-bv`, `+preprocess`, `+preprocess-inprocess`, and `lazy-bv` (CEGAR) —
  at 3 s and 20 s. Finding: solver-side preprocessing is **measured-maxed** (decides
  the same set as single-pass on this slice), and `lazy-bv` is **inert here** (the
  slice is arithmetic-free, 0 heavy ops) — confirming the lever is stronger
  *reduction algorithms* (`axeyum-rewrite`) or the SAT core, not more iteration.
  The [`qfbv-curated-sat-bv-*-vs-z3-2s.json`](baselines/) trio is the smaller
  curated cross-check (same conclusion at 2 s).

## Recent capability movement (Unknown-reduction front, 2026-06-21 → 06-22)

The QF_BV perf artifacts above are **unchanged** — there have been no QF_BV-perf
commits since 06-20. The recent week's measured movement is on the **completeness /
decide-rate** front (the "depth gap" in [PLAN.md](../PLAN.md#the-gap-to-z3cvc5-itemized)),
measured by the env-gated Unknown-gap dump in the **adversarial Z3 differential
fuzzers** (not by committed JSON artifacts — these are fuzz-measured decide rates):

- **QF_NRA** Unknown `109 → 64` (polynomial normalization + any-coefficient
  linear-definition substitution); the **CAD decision side is complete** (N-variable
  algebraic critical-point lifting landed).
- **QF_NIA** Unknown `498 → 146` (no-overflow guard on the integer-multiplier
  bit-blast).
- **QF_UFLIA** Unknown `311 → 18` (replay-checked sat models for arithmetic-sorted UF).
- **Soundness:** **five standing adversarial Z3 differential gates** (bv, nia,
  uflia, abv, nra) now all sweep clean (DISAGREE = 0). The NRA/CAD development
  surfaced and fixed **three wrong-unsat bugs** the unit tests missed — exactly the
  "test it harder" discipline, not avoidance.

> Note: the canonical live tracker for this front is [STATUS.md](../STATUS.md)
> (owned by the arithmetic/CAD work in flight); this section is the benchmark-side
> snapshot only.

## Baselines

- [`baselines/qf-bv-20221214-p4dfa-z3-1s.json`](baselines/qf-bv-20221214-p4dfa-z3-1s.json):
  Phase 2 public QF_BV baseline over the SMT-LIB 2024 non-incremental
  `QF_BV/20221214-p4dfa-XiaoqiChen` family. Reproduce with
  `just bench-public-qfbv-baseline` after fetching `qf_bv`.
- [`baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json`](baselines/qf-bv-20221214-p4dfa-z3-1s-rewrite-default.json):
  Phase 3 rewrite-measurement baseline over the same slice, with
  `--rewrite default`. The run rewrites all 113 instances, applies
  255,551 default denotation-preserving rules, records 8,706,521 input DAG
  nodes vs 8,450,857 output DAG nodes, and reports zero status
  disagreements, rewrite decision changes, sat/unsat conflicts, or model
  replay failures. Reproduce with `just bench-public-qfbv-rewrite` after
  fetching `qf_bv`.
- [`baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json`](baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n1000.json):
  Phase 5 public pure-Rust `sat-bv` vs Z3 supported-slice baseline over the
  same SMT-LIB family, with `--backend sat-bv --compare-z3 --node-budget
  1000`. The run records 113 files, 1 `sat`, 112 structured node-budget
  `unknown`s, 0 unsupported, 0 errors, 0 model replay failures, 1 Z3 oracle
  agreement, and 0 oracle disagreements. Reproduce with
  `just bench-public-qfbv-sat-bv-compare` after fetching `qf_bv`.
- [`baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json`](baselines/qf-bv-20221214-p4dfa-sat-bv-z3-compare-1s-n5000-cnf7k-20k.json):
  Phase 5 guarded-admission rerun over the same slice, with `--backend sat-bv
  --compare-z3 --node-budget 5000 --cnf-var-budget 7000 --cnf-clause-budget
  20000`. Artifact version 7 records submitted query-plan mode, replay
  policy, and refinement-round configuration in addition to node/CNF admission
  budgets. The current artifact includes the sparse-CNF XOR/mux helper
  optimization. The run records 113 files,
  1 `sat`, 112 structured `unknown`s (111 `NodeBudget`, 1 `EncodingBudget`),
  0 unsupported, 0 errors, 0 model replay failures, 1 Z3 oracle agreement, and
  0 oracle disagreements. Reproduce with
  `just bench-public-qfbv-sat-bv-guarded` after fetching `qf_bv`.
- [`baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json`](baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-1s-n5000-cnf7k-20k-r16.json):
  Phase 5 replay-refinement diagnostic over the same slice, with `--backend
  sat-bv --query-plan replay-refine --refine-rounds 16 --compare-z3
  --node-budget 5000 --cnf-var-budget 7000 --cnf-clause-budget 20000`. The run
  records 113 files, 1 `sat`, 112 structured `unknown`s (95 `EncodingBudget`,
  17 `NodeBudget`), 0 unsupported, 0 errors, 0 model replay failures, 1 Z3
  oracle agreement, and 0 oracle disagreements. It proves replayable slicing is
  soundly instrumented but does not yet expand public decisions. With the
  sparse-CNF pass, the immediate
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2` target reaches a fourth
  support set and then refuses at 7,888 CNF variables / 25,197 clauses under the
  committed 7,000-variable / 20,000-clause caps. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine` after fetching `qf_bv`.
- [`baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json`](baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-10s-n5000-cnf7k-30k-r16-j8.json):
  Phase 5 relaxed-admission replay-refinement diagnostic over the same slice,
  with `--backend sat-bv --query-plan replay-refine --refine-rounds 16
  --compare-z3 --timeout-ms 10000 --node-budget 5000 --cnf-var-budget 7000
  --cnf-clause-budget 30000 --jobs 8`. The run records 113 files, 2 `sat`,
  111 structured `unknown`s (94 `EncodingBudget`, 17 `NodeBudget`), 0
  unsupported, 0 errors, 0 model replay failures, 2 Z3 oracle agreements, and
  0 oracle disagreements. The newly decided public instance is
  `MobileDevice/mobiledevice_bit8_na1_nr1_twocond.smt2`, which reaches full
  replay at 6,312 CNF variables / 25,054 clauses. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-relaxed` after fetching
  `qf_bv`.
- [`baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json`](baselines/qf-bv-20221214-p4dfa-sat-bv-z3-replay-refine-exact-10s-n5000-cnf8k-30k-r64-b64-j8.json):
  Phase 5 exact-target relaxed replay-refinement diagnostic over the same
  slice, with `--backend sat-bv --query-plan replay-refine-exact
  --refine-rounds 64 --refine-batch 64 --compare-z3 --timeout-ms 10000
  --node-budget 5000 --cnf-var-budget 8000 --cnf-clause-budget 30000
  --jobs 8`. Artifact version 9 records `refine_batch` in the query-plan
  config. The run records 113 files, 2 `sat`, 111 structured `unknown`s, all
  `EncodingBudget`, 0 unsupported, 0 errors, 0 model replay failures, 2 Z3
  oracle agreements, and 0 oracle disagreements. It reduces submitted public
  query shape to 237,924 DAG nodes and removes the node-budget unknown class
  in this diagnostic profile, but it does not increase the public decision
  count beyond the relaxed support-slice run. The MobileDevice decision reaches
  full replay at 6,302 CNF variables / 25,020 clauses, with 3,301 ms BatSat
  solve time versus 1,097 ms Z3 oracle solve time in this run. Reproduce with
  `just bench-public-qfbv-sat-bv-replay-refine-exact` after fetching `qf_bv`.
