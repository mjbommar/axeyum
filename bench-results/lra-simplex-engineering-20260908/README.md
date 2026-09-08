# QF_LRA simplex pivot-rule A/B, 2026-09-08

Raw measurements behind
[`docs/research/12-performance/lra-simplex-engineering-2026-09-08.md`](../../docs/research/12-performance/lra-simplex-engineering-2026-09-08.md).
Read the note for what the numbers mean; this file records only how they were
taken, so a re-run is possible and a mis-reading is not.

## Arms

**One binary**, arm selected at run time by `AXEYUM_SIMPLEX_PIVOT`:

- `bland` — `EnteringRule::Bland`, the pre-2026-09-08 behaviour.
- (unset) — `EnteringRule::MinimiseFillIn`, the new default.

Two binaries were deliberately **not** used: with two builds any difference is
confounded by everything else that changed between them.

Host `s4`, `taskset -c 0-7`, 24 s and 8 GiB per file, one file at a time.
**The host was not idle** — other lanes were sweeping concurrently throughout.
That is fine for the counter columns, which are clock-free, and it is the
reason the wall-time table was taken separately (below) rather than read off
these files.

## Files

| file | population | how |
|---|---|---|
| `qf_lra_miss33_{bland,fillin}.tsv` | the 33-file QF_LRA miss population (`../adr-1701-slice-1-20260905/qf_lra_population.tsv`) | arms run **sequentially**, same core half |
| `qf_lra_200_{bland,fillin}.tsv` | the committed 200-file parity list (`../parity-lists/QF_LRA.txt`) | arms run **concurrently on opposite core halves** — see below |
| `qf_lra_commonly_decided_timing.tsv` | the 96 files both arms decide | arms run **sequentially, one file at a time**; this is the only file whose wall times are comparable |

Columns are `file`, `verdict`, the raw `; theory-layer` trace line (and, for
the 200-file pair, the `; route` line). The timing file is
`file`, `arm`, `verdict`, `total_ms`.

### Why the 200-file pair was run concurrently, and what that costs

It is a **verdict** comparison — a no-regression check — and running the arms on
opposite core halves halves its wall clock. That is the previous lane's
documented departure from one-arm-at-a-time, for the same reason.

What it costs is exactly what you would expect: a file whose real runtime sits
just under the budget can land on either side of it. It did.
`spider_benchmarks/no_op_accs` appears as a **gain** in these files and is not
one — run alone it decides `unsat` in **both** arms at ~20.7 s. Every boundary
file was re-run individually and the note reports the individually-confirmed
count (**+1**), not the sweep count (+2).

**Do not score these two files without that re-check.** The sweep's gain column
is an upper bound on gains and, symmetrically, its loss column is not a lower
bound on losses.

## Scripts

`lane-scratch/` (not committed — scratch, per lane hygiene) held `ab.sh`,
`arm.sh`, `time_arms.sh`, `score.py`, `score_timing.py`. They are three loops
and two table printers; the commands they run are the ones written out above,
and the note quotes every number they produced.
