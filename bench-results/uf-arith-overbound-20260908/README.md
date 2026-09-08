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
- `base-QF_UFLIA200.tsv`, `reserve-QF_UFLIA200.tsv` — base against the shipped
  default over the full committed 200-file division list
  (`bench-results/parity-lists/QF_UFLIA.txt`): the regression check on the files
  we already win. 116 -> 125 decided, +10 / -1, zero disagreements.
- `probe-half-QF_UFLIA200.tsv` — the REJECTED half-budget version of the same
  arm, kept because it is the evidence that set the constant: +9 / -4 against
  the same base.
- `reserve-QF_UFLIA58.tsv` — the shipped default on the loss population: +9 / -0.

**No CPU profile is committed, and that is a finding rather than an omission.**
This host runs `kernel.perf_event_paranoid = 4`, so `perf record` collects
nothing at all — it exits successfully and writes a zero-sized `perf.data`. A
`perf report` on it says `zero-sized data … nothing to do`. Anyone reaching for
a flat profile here needs a host with a lower `paranoid` setting first; the
route-level attribution below is what stands in for it.
- `scripts/build-pinned.sh` — builds the base and working-tree binaries and
  copies each OUT of `target/`, so a later build cannot swap the file a sweep
  is reading.
- `scripts/sweep.sh` — runs one list through a pinned binary under the parity
  protocol (24 s wall, 8 GiB `ulimit -v`, one file at a time), `--trace` on.
- `scripts/run-ab-parallel.sh` — the three arms over the loss population, run
  CONCURRENTLY so contention is common-mode; `scripts/run-regression.sh` and
  `scripts/run-reserve-arms.sh` do the same for the 200-file list.
  `scripts/build-reserve.sh` pins a second working-tree binary under its own
  name so a rebuild cannot swap one a sweep is executing.
- `scripts/mutate.sh` — the mutation control on the reachability guard: it puts
  the removed behaviour back and asserts its own anchor applied first.
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
