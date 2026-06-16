# corpus/qfbv-curated — committed QF_BV measurement slice (P4.5)

A small, **committed**, deterministic QF_BV slice for the measured axeyum-vs-Z3
head-to-head harness (plan task
[P4.5](../../docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md)). It is the
fixed instrument every Track 1 performance change is measured against.

## What's here

43 QF_BV instances drawn from a spread of SMT-LIB families so the slice is diverse
(sat + unsat, several solvers' benchmark styles). Files are flattened and named
`<family>__<original>.smt2`.

**Selected by term width, not file size.** The slice caps the maximum declared
bit-vector width at **64 bits** (actual max in the slice: 32). This is deliberate:
a 3 KB file can declare a 20,000-bit vector or a 1024-bit multiplier, and
bit-blasting those allocates *gigabytes* — sat-bv currently lacks graceful
refusal of oversized encodings (the node budget is enforced after the eager
lowering allocation; a known robustness gap, tracked for Track 1 P1.2). The width
cap keeps the slice fast and bounded so it can run repeatedly without OOM.

Families: `brummayerbiere3`, `bruttomesso`, `crafted`, `dwp_formulas`,
`stp_samples`, `wienand-cav2008`, `bmc-bv`, `20190311-bv-term-small-rw-Noetzli`,
`bench_ab`, `calypto`, `check2`, `20220315-ecrw`.

## Baseline (recorded)

`sat-bv` vs Z3 4.13.3, 2 s timeout, encoding budgets, `--jobs 2`:
**32/43 decided** (8 sat + 24 unsat), 11 `unknown` (budget/timeout), **agree=32,
DISAGREE=0, model_replay_failures=0**, PAR-2 ≈ 1.07 s. Artifact:
`bench-results/baselines/qfbv-curated-sat-bv-vs-z3-2s.json`. The 11 unknowns are
the performance gap the Track 1 inprocessing/preprocessing work targets.

## Why committed + small

- **Committed**: unlike the 41 GB fetched `corpus/public/` (gitignored), this slice
  is in-repo so the baseline is reproducible by anyone, and CI can run it.
- **Small**: it runs at `--jobs 4` with a short timeout without OOM (per the
  build/host limits) — the project rule is to *measure once on a committed slice*,
  never sweep the public corpus.

## How it was selected

Deterministically (file selection only, no solving): for each family, the small
(`< 4 KB`) `*.smt2` files under `corpus/public/non-incremental/QF_BV/<family>/`
in name order whose **maximum declared `BitVec` width ≤ 64**, up to 4 per family,
copied with a `<family>__` prefix. Regenerating with the same rule reproduces the
same files.

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
