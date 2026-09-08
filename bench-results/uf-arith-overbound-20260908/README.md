# QF_UFLIA over-bound UF+arithmetic dispatch, 2026-09-08

Data for the `euf-driver-mbtc` lane. The writeup — what was measured, why, and
what changed — is
[`docs/research/12-performance/uf-arith-overbound-2026-09-08.md`](../../docs/research/12-performance/uf-arith-overbound-2026-09-08.md).
Read that first; this directory is data, not narrative.

## Contents

Every TSV carries `#` header lines naming the binary's `sha256`, the policy in
force, and the load average at start, before the column header. Columns:
`file`, `wall_ms`, `verdict`, `route_line` (the ADR-1760 `; route …`
attribution), `trail` (the `; route-trail …` JSON).

- `base-QF_UFLIA58.tsv`, `probe-QF_UFLIA58.tsv`, `skip-QF_UFLIA58.tsv` — the
  committed 58-file 2026-09-05 loss list
  (`bench-results/parity-losses-20260905/QF_UFLIA.txt`) under the lane's base
  commit and under the two new arms.
- `base-QF_UFLIA200.tsv`, `probe-QF_UFLIA200.tsv` — the same two solvers over
  the full committed 200-file division list
  (`bench-results/parity-lists/QF_UFLIA.txt`), which is the regression check on
  the files we already win.
- `hard12.perf.flat.txt` — a flat CPU profile of one loss file under the base
  solver: where the 24 s actually goes inside the route that consumes it.
- `scripts/build-pinned.sh` — builds the base and working-tree binaries and
  copies each OUT of `target/`, so a later build cannot swap the file a sweep
  is reading.
- `scripts/sweep.sh` — runs one list through a pinned binary under the parity
  protocol (24 s wall, 8 GiB `ulimit -v`, one file at a time), `--trace` on.
- `scripts/run-ab.sh` — the arms, in order, loss population first.
- `scripts/analyze.py` — summarizes one or more TSVs and compares consecutive
  pairs per file. **Its exit status is 1 when two arms disagree on a
  `sat`/`unsat`**, so a soundness break fails rather than being printed.

## Reproducing

```sh
bench-results/uf-arith-overbound-20260908/scripts/build-pinned.sh
bench-results/uf-arith-overbound-20260908/scripts/run-ab.sh
python3 bench-results/uf-arith-overbound-20260908/scripts/analyze.py \
  bench-results/uf-arith-overbound-20260908/base-QF_UFLIA58.tsv \
  bench-results/uf-arith-overbound-20260908/probe-QF_UFLIA58.tsv
```

## The one number to read

`...and NOTHING ran after it` in the analyzer's output: files that reached the
over-bound UF+arithmetic decision point and on which no solver route ran
afterwards. Front-door `fd:*` routes are excluded from that count on purpose —
they are recorded on every file after dispatch returns, and counting them made
the first pass of this analysis report the exact opposite of the truth.
