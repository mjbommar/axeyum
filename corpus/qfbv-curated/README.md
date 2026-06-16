# corpus/qfbv-curated — committed QF_BV measurement slice (P4.5)

A small, **committed**, deterministic QF_BV slice for the measured axeyum-vs-Z3
head-to-head harness (plan task
[P4.5](../../docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md)). It is the
fixed instrument every Track 1 performance change is measured against.

## What's here

36 small (`< 3 KB`) QF_BV instances, three per family, drawn from a spread of
SMT-LIB QF_BV families so the slice is diverse (sat + unsat, several solvers'
benchmark styles). Files are flattened and named `<family>__<original>.smt2`.

Families: `brummayerbiere3`, `brummayerbiere4`, `bruttomesso`, `crafted`,
`dwp_formulas`, `log-slicing`, `pspace`, `stp_samples`, `wienand-cav2008`,
`bmc-bv`, `20190311-bv-term-small-rw-Noetzli`, `bench_ab`.

## Why committed + small

- **Committed**: unlike the 41 GB fetched `corpus/public/` (gitignored), this slice
  is in-repo so the baseline is reproducible by anyone, and CI can run it.
- **Small**: it runs at `--jobs 4` with a short timeout without OOM (per the
  build/host limits) — the project rule is to *measure once on a committed slice*,
  never sweep the public corpus.

## How it was selected

Deterministically (file selection only, no solving): for each family, the three
smallest `*.smt2` files under `corpus/public/non-incremental/QF_BV/<family>/`
(by size, then name), copied with a `<family>__` prefix. Regenerating the slice
reproduces the same files.

## Running the head-to-head

```sh
just bench-qfbv-curated   # sat-bv vs Z3, oracle-enabled, → bench-results baseline
# or directly:
cargo run -p axeyum-bench --features z3 -- corpus/qfbv-curated \
  --backend sat-bv --compare-z3 --timeout-ms 2000 --jobs 4 \
  --out bench-results/baselines/qfbv-curated-sat-bv-vs-z3-2s.json
```

The run reports decided counts, PAR-2, and the **soundness gate**: `agree` (vs
Z3), `DISAGREE` (must be 0), and `model_replay_failures` (must be 0). The baseline
artifact is committed under `bench-results/baselines/`; subsequent Track 1 changes
report their PAR-2 delta against it.
