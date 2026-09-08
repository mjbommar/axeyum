# Route-attribution sweep, 2026-09-07

Per-division sweep carrying the route columns ADR-1760 added, plus the
virtual-best-over-our-own-routes analysis it exists to support. Narrative,
method and findings are in
[`docs/research/12-performance/route-attribution-2026-09-07.md`](../../docs/research/12-performance/route-attribution-2026-09-07.md)
and [ADR-1760](../../docs/research/09-decisions/adr-1760-the-front-door-carries-route-attribution.md).
Read those first — this directory is data, not narrative.

## Contents

- `<DIV>.tsv` — one per division. Columns: `division`, `file`, `wall_ms`,
  `verdict`, **`decided_by`**, **`bound_by`**, **`last`**, `bound_ms`,
  `trace_total_ms`, `attempts`, `log_path`.

  Three route columns and not one. `decided_by` is which route produced the
  verdict, `bound_by` is which route consumed the budget, `last` is which route
  spoke last. Collapsing them is what produced the misclassifications ADR-1760
  documents; a consumer must never have to infer the binding route from the
  last one.

- `logs.tgz` — the 1,200 per-file stdout captures, including each
  `; route-trail <json>` line carrying the whole ordered trail with per-attempt
  `elapsed_ns`. The TSV keeps the summary; the trail stays in the log because
  it is a JSON object with one entry per dispatch attempt and does not belong
  in a tab-separated column.

  Compressed rather than committed as 1,200 loose files: uncompressed they are
  12 MB, since the largest trails run past 100 KB on their own (a `UF` query
  whose quantifier loop re-dispatched thousands of times). `tar xzf logs.tgz`
  restores the `logs/` tree the TSVs' `log_path` column names.

  The `log_path` column holds the ABSOLUTE path from the machine that produced
  the run. To re-aggregate after extracting, rewrite that column to the local
  `logs/` directory first — `aggregate.py` reads the path as given and reports
  a file whose log it cannot open as trail-less rather than guessing.

- `aggregate.json` — deciding-route distribution, binding-route distribution on
  losses, and the virtual-best figures, per division and overall.

- `cost_ab.tsv` / `cost_ab.txt` — the A/B behind the "no measurable cost with
  collection off" claim, and its scoring.

## Scripts

- `scripts/run_division.sh <DIV> <list> <bin> <out.tsv> <log-dir> [N] [BUDGET_S]`
- `scripts/sweep.sh` — all 12 divisions, one process each.
- `scripts/aggregate.py <DIV>.tsv …` — the analysis. Exits 1 on any
  impossibility-guard violation and on a vacuous population.
- `scripts/test_aggregate_guard.py` — control suite for `aggregate.py`'s
  guards. Every guard gets a fixture it must pass AND one it must fail, and the
  headline arithmetic is pinned against a hand-computed fixture.
- `scripts/cost_ab.sh` / `scripts/cost_ab.py` — the alternating-arm cost A/B.
  `cost_ab.py --self-check` injects a synthetic 5% slowdown and requires the
  verdict to flip, so a clean result is a measurement rather than an
  insensitive instrument.

## Selection

The deterministic first `min(N, total)` lines of each committed parity list in
`bench-results/parity-lists/`, N=100, 24 s wall budget, 8 GiB `ulimit -v`.

Parity lists rather than the loss-census lists, deliberately: they carry files
we WIN as well as files we lose, and a loss-only population has no deciding
routes to distribute — which is the whole question.

## Reference frame

Divisions ran in parallel, one process each, on an otherwise idle 16-core host.
`wall_ms`, `bound_ms` and `trace_total_ms` are therefore comparable **within**
this run and should not be compared against a differently loaded one. The
deciding-route column is dispatch-order-deterministic and is not load-sensitive
at all, so the virtual-best analysis is unaffected.

`wall_ms` includes process startup; `trace_total_ms` does not. On short files
the two differ by most of `wall_ms`, so the route analysis uses the trail's own
timings throughout.

## Reproducing

```sh
cargo build --release -p axeyum-bench --example smtcomp_cli
bash bench-results/route-attribution-2026-09-07/scripts/sweep.sh
python3 bench-results/route-attribution-2026-09-07/scripts/aggregate.py \
  bench-results/route-attribution-2026-09-07/*.tsv
python3 bench-results/route-attribution-2026-09-07/scripts/test_aggregate_guard.py
```
