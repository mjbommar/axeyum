# Benchmark Results

Committed benchmark artifacts that serve as project evidence. Scratch runs stay
under `bench-results/local/`, which is gitignored.

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
