# instrument-coverage per-division re-run, 2026-09-07

Reproducible re-run of `bench-divisions-2026-09-07`'s per-division timing
sample, against a `smtcomp_cli` binary carrying this lane's four new
`--trace` instruments (`BvLayerStatsGuard`, `FrontDoorStatsGuard`,
`DlOnlineStatsGuard`, plus the pre-existing `TheoryLayerStatsGuard`). Full
writeup, methodology, and the before/after coverage table are in
[`docs/research/12-performance/instrument-coverage-2026-09-07.md`](../../docs/research/12-performance/instrument-coverage-2026-09-07.md).
Read that first — this directory is data, not narrative.

## Contents

- `<DIV>.tsv` — one per division. Columns: `division`, `file`, `wall_ms`,
  `verdict`, `log_path` (the full captured stdout for that run, under
  `logs/`, since a query can now print more than one `; …` trace line).
- `logs/<DIV>.<n>.log` — the raw stdout `run_division.sh` captured per file.
- `aggregate.json` — per-division and overall coverage, produced by
  `scripts/aggregate.py`. Carries `non_additivity_guard_violations`
  (empty on this run — asserted per-file `traced_ms <= wall_ms * 1.15`,
  exits 1 on any violation).
- `scripts/run_division.sh` — runs one division's sample. Usage:
  `run_division.sh <DIV> <loss-list.txt> <smtcomp_cli-binary> <out.tsv> <log-dir> [N=8]`.
- `scripts/sweep.sh` — drives `run_division.sh` across all 12 divisions in
  the same order and selection as `bench-divisions-2026-09-07`.
- `scripts/aggregate.py` — TSVs in, per-division coverage JSON out; exits 1
  if the non-additivity guard finds a file whose traced time exceeds its
  own wall clock.
- `scripts/test_aggregate_guard.py` — mutation-checks `aggregate.py`'s
  guard itself: a synthetic honest fixture must pass, a synthetic
  impossible-sum fixture must fail. Run:
  `python3 bench-results/instrument-coverage-2026-09-07/scripts/test_aggregate_guard.py`.

## Reproducing

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli
bash bench-results/instrument-coverage-2026-09-07/scripts/sweep.sh
python3 bench-results/instrument-coverage-2026-09-07/scripts/aggregate.py \
  bench-results/instrument-coverage-2026-09-07/*.tsv
```

Selection rule, protocol, and file lists are identical to
`bench-divisions-2026-09-07` (see that lane's own README) — this reuses the
same committed loss-census lists, not a fresh draw.

Measured at solver commit `2ee156a66d5d9afa7ece49a27a2147443a9bafb1` (this
lane's own instrumentation commit), run on s4 (not idle — this lane's own
concurrent clippy/test/build gates were running at the same time; see the
diary for why the headline before/after comparison is still valid).
