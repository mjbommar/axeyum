# SMT-COMP reproduction — first real runs

The in-tree replica of the SMT-COMP scoring pipeline (see `README.md`), exercised
on **real solvers and real benchmarks**. Reference solvers (cvc5 1.3.4,
bitwuzla 0.9.1, both static) are staged in the gitignored
`references/smtcomp-solvers/`; the solver under test is
`target/release/examples/smtcomp_cli` (a thin CLI over `axeyum_solver::solve_smtlib`,
the exact Single-Query interface an entrant needs — see the crate example).

All numbers below are reproducible via `run_repro.sh` / `compete.py`. Times are
hardware-dependent; runs were pinned to 24-core hosts (this box and `s0`, which
share the filesystem — "similar hardware" per the task).

## Run 1 — Single Query Track, QF_BV, 3 solvers (local, 24 benchmarks, T=10s)

```
### division QF_BV  (N=24, competitive)
  solver      e     n    PAR2-wall    seq-cpu
  bitwuzla    0    19        103.0        3.0
  cvc5        0    19        103.6        3.6
  axeyum      0    19        106.1        6.1
  biggest-lead correctness rank (top2): 1.000
  largest-contribution correctness ranks: axeyum/cvc5/bitwuzla = 0.000

### Best Overall Ranking
  axeyum / cvc5 / bitwuzla   overall_score = 0.8650   (= (19/24)^2 * log10(24))
```

Reading it:
- **All three solvers are sound** (`e=0`) and solve the **same 19/24**. The 5
  misses are the hard `brummayerbiere3` multiplier-unsats (`mulhs16/32/64`, …)
  that time out for every solver at T=10s.
- On the one hard instance all three crack (`mulhs08`, unsat): axeyum **5.73 s**,
  cvc5 2.75 s, bitwuzla 2.40 s — a real head-to-head.
- On `mulhs16/32/64` axeyum returns a clean `unknown` at its 9 s internal cap
  while cvc5/bitwuzla are wall-killed at 10 s. All score `n=0` (no error).
- PAR-2 wall separates them: bitwuzla < cvc5 < axeyum — axeyum an honest third,
  ~3 % behind on this slice.
- **0 wrong answers** across all 72 (solver, benchmark) pairs.

## Run 2 — distributed execution (local ⊕ s0), then central scoring (16 benchmarks, T=6s)

Execution sharded 0/2 on this box and 1/2 on `s0` (each dumped raw results to
the shared FS); scoring merged centrally — the same execution/scoring split
SMT-COMP uses (BenchExec per-pair results → central `smtcomp` tool).

```
### division QF_BV  (N=16, competitive)
  solver      e     n    PAR2-wall    seq-cpu
  cvc5        0    13         38.9        2.9
  axeyum      0    12         48.1        0.1
  biggest-lead correctness rank (top2): 1.077   (= (13+1)/(12+1))

### Best Overall Ranking
  cvc5      overall_score = 0.7949   (= (13/16)^2 * log10(16))
  axeyum    overall_score = 0.6773   (= (12/16)^2 * log10(16))
```

At the tighter 6 s limit axeyum solves 12/16 vs cvc5's 13/16 — both sound. The
merged scoreboard is byte-identical whether the 16 pairs run on one host or two,
confirming scoring is deterministic and location-independent.

## What this establishes

1. The scoring engine matches the rules (40 unit tests, one per §7 clause plus
   §6 selection).
2. The axeyum Single-Query CLI is **competition-shaped and sound** on real QF_BV
   benchmarks — the prerequisite artifact for an actual entry (targeting
   SMT-COMP 2027; the 2026 window closed 2026-05-27).
3. Execution distributes cleanly across the s-nodes and re-scores centrally,
   giving a local rehearsal harness at competition scale.

## Honest gaps (not yet reproduced)

- **Model-Validation track** needs the Dolmen validator to turn `get-model`
  output into VALID/INVALID; the scoring for it is implemented and tested, the
  external validator is not yet wired.
- **Unsat-Core track** needs the cross-solver core re-validation loop.
- **Incremental track** needs the `trace-executor` stdin protocol.
- **"Easy benchmark" removal** (§6) needs the 2018-2024 historical results.
- Full SMT-LIB library ingestion (the real division pools) vs. our curated
  corpora — the pipeline is corpus-agnostic; only the inputs differ.
