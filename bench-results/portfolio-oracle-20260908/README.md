# Parallel-portfolio oracle, 2026-09-08

Data for the `parallel-portfolio` lane. The writeup — what was measured, why,
and what it decides — is
[`docs/research/12-performance/parallel-portfolio-oracle-2026-09-08.md`](../../docs/research/12-performance/parallel-portfolio-oracle-2026-09-08.md).
Read that first; this directory is data, not narrative.

## The question

Not *"if we ran the same routes concurrently, how much waiting disappears?"* —
the [2026-09-07 sweep](../route-attribution-2026-09-07/README.md) answered that
(1.33x on files we decide, median 84% binder share on files we lose) and
concluded a portfolio was not the largest available win. That answer is sound.

This is the other question: **is there a route that would have decided this file
quickly, which we never reached because a slower one ran first?** One dominant
route is consistent with a large answer to it, and the QF_ABV attribution note
already carried a counterexample.

## Contents

- `probe/<DIV>.tsv` — `scripts/portfolio-oracle.py`. Per file: a **control** run
  at the 24 s competition budget and, when that loses, a **probe** run at 120 s
  with `--trace`, scored from the deciding route's own `elapsed_ns`.
- `solo/<DIV>.tsv` — `scripts/route-solo-sweep.py` over
  `examples/route_solo`. Per file per route: that route run **alone**, one route
  per process, at 24 s.
- `frames/<DIV>.frame` — load average before and after each division, per slot.
  All three hosts carried another lane's A/B sweep throughout, so **timings here
  are advisory**; the decide/not-decide bit is what the conclusions rest on.

Population: the committed `bench-results/parity-losses-20260905/<DIV>.txt` lists
(403 files, 11 divisions). Hosts s5/s6/s7, `taskset`-pinned slots, 8 GiB
`ulimit -v`.

## Three things to know before quoting a number from here

1. **`STALE-DECIDED` is the largest column.** The loss lists are from
   2026-09-05 and the tree has moved under them; a prize scored against the
   list rather than against a re-measured control would count the ladder's own
   recent wins as a portfolio's.

2. **The column is `PRIZE-CANDIDATE`, never `PRIZE`.** The probe estimates an
   arm cost as `preamble + the deciding route's own segment`, which is valid
   only for a single-pass ladder. `LOOPED-NOT-SCORED` marks files whose front
   door re-dispatches (a string-bound ladder, a refinement loop), where that
   segment is one round of many — on
   `QF_SLIA/…/new.8618.corecstrs.readable.smt2` the segment is 1,172 ms and the
   file needs 110,546 ms. Confirming a candidate needs a route-selection knob
   `SolverConfig` does not have.

3. **The two instruments are complementary, and neither is sufficient.** The
   probe cannot see a route starved by one whose budget is a *fraction of the
   wall* — raising the wall raises its share too, so `bmc-arrays/bubbleSort.smt2`
   is unknown at 24 s and still unknown at 120 s while `abv-lazy-row` alone
   decides it in 1.2 s. The solo prober cannot see the shipped front door: it
   runs the flat assertion view with no preprocessing, so a negative from it is
   "not shown", never "cannot".

`scripts/portfolio-oracle-table.py` joins the two; `scripts/portfolio-oracle-aggregate.py`
summarises the probe alone. Both exit non-zero on a cross-route verdict
disagreement, and `route-solo-sweep.py --expected` exits 3 on a verdict that
contradicts the census's `reference_verdict` — cross-route agreement is not a
correctness check, since routes can agree with each other and all be wrong.

## Unfinished sweeps, and how to collect them

Five solo sweeps were still running when this landed. **They are the measurement
that decides the open question** — the one confirmed portfolio-only file came
out of `QF_UFLIA`'s first 35 files, and no other finished division has one.

| host | slot | divisions | state at hand-off |
|---|---|---|---|
| s7 | 12-15 | `QF_UFLIA` | 35 of 58 |
| s5 | 0-3 | `QF_NIA` | 24 of 61 |
| s7 | 8-11 | `QF_NIA_b` (files 32-61) | ~5 of 30 |
| s6 | 4-7 | `QF_IDL` | 26 of 54 |
| s6 | 8-11 | `QF_RDL`, then `QF_SLIA` | 21 of 47 |
| s5 | 4-7 | `QF_LIA` | 9 of 27 |

Each writes its TSV only on completion; the per-file lines already produced are
in `partial/<DIV>.solo.progress.txt` here, so the coverage is visible rather
than implied. To collect a finished one:

```sh
scp <host>:~/pp-oracle/solo/<DIV>.tsv   bench-results/portfolio-oracle-20260908/solo/
scp <host>:~/pp-oracle/solo/<DIV>.frame bench-results/portfolio-oracle-20260908/frames/<DIV>.solo.frame
```

`QF_NIA_b` is the second half of `QF_NIA`'s list run on a separate core set; its
rows merge with `QF_NIA`'s without overlap.

A second pass adding `dl-online` and `qf-bv` (which the first sweeps predate) is
queued behind `QF_LRA` and `QF_UFLIA` on s6/s7 and has already run for the four
divisions in `solo2/`.

## Reproducing

```sh
scripts/portfolio-oracle-slot.sh 0-3 QF_LRA          # probe, one pinned slot
scripts/route-solo-slot.sh      12-15 QF_LRA         # solo, one pinned slot
python3 scripts/portfolio-oracle-table.py \
  --probe bench-results/portfolio-oracle-20260908/probe/*.tsv \
  --solo  bench-results/portfolio-oracle-20260908/solo/*.tsv
```
