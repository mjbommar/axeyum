# bench-divisions per-division timing sample, 2026-09-07

Reproducible timing sample for the `bench-divisions` lane's per-division
stage-breakdown work. Full writeup, methodology, results table, and the
`theory_assert_ms` double-counting correction are in
[`docs/research/12-performance/bench-divisions-2026-09-07.md`](../../docs/research/12-performance/bench-divisions-2026-09-07.md).
Read that first — this directory is data, not narrative.

## Contents

- `<DIV>.tsv` — one per division (`QF_ABV`, `QF_BV`, `QF_IDL`, `QF_LIA`,
  `QF_LRA`, `QF_NIA`, `QF_NRA`, `QF_RDL`, `QF_SLIA`, `QF_UF`, `QF_UFLIA`,
  `UF`). Columns: `division`, `file`, `wall_ms`, `verdict`, `trace_line`
  (the raw `; theory-layer ...` line when one was printed, empty otherwise).
- `aggregate.json` — per-division stage sums, produced by
  `scripts/aggregate.py`. Carries both the corrected conservative total
  (`traced_total_ms`, `traced_fraction_pct`) and the naive, known-wrong sum
  that includes double-counted `theory_assert_ms`
  (`naive_traced_total_ms_DO_NOT_TRUST`) — kept so the QF_UF anomaly that
  found the double-count stays visible.
- `report.md` — `aggregate.json` rendered as a markdown table.
- `scripts/run_division.sh` — runs one division's sample against a built
  `smtcomp_cli` release binary. Usage:
  `run_division.sh <DIV> <loss-list.txt> <smtcomp_cli-binary> <out.tsv> [N=8]`.
- `scripts/aggregate.py` — TSVs in, per-division JSON stage breakdown out.
- `scripts/report.py` — `aggregate.json` in, markdown table out.

## Reproducing a division's sample

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli   # no --features full
bench-results/bench-divisions-2026-09-07/scripts/run_division.sh \
  QF_IDL bench-results/parity-losses-20260905/QF_IDL.txt \
  target/release/examples/smtcomp_cli \
  /tmp/QF_IDL.tsv 8
python3 bench-results/bench-divisions-2026-09-07/scripts/aggregate.py /tmp/QF_IDL.tsv
```

Selection rule: the first `min(8, N)` lines of the division's committed
2026-09-05 (or, for `QF_NRA`, 2026-09-06) loss-census file
(`bench-results/parity-losses-20260905/<DIV>.txt` /
`bench-results/parity-losses-20260906/QF_NRA.txt`), in file order — no
shuffling, no cherry-picking. That census's `class`/`last_route` columns are
refuted (see its own `README.md`); only the file list itself is used here.
Protocol matches `scripts/parity-run.sh`: 24 s wall, 8 GiB `ulimit -v`,
`AXEYUM_TRACE=1` added.

Measured at solver commit `d51d4ef04878b40f5d00a1a6b4aed405b35cae4e`
(local `main` == `origin/main` at lane start), built and run on s7
(idle, `/proc/loadavg` ~1.0 throughout).
