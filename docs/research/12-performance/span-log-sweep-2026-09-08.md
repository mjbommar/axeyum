# The span log over 300 files: what six divisions look like as event rows

Measured 2026-09-08 at solver commit `049afd423`, on **s6** and **s7**, one
process at a time per host, 24 s and 8 GiB per file, over the first 50 files of
each committed list in `bench-results/parity-lists/`.

```
scripts/span-log-sweep.sh <DIVISION> <out.jsonl> 50 24000
```

Six divisions, 300 files: `QF_ABV`, `QF_BV`, `QF_IDL`, `QF_LIA`, `QF_LRA`,
`QF_NIA`. Each run wrote a JSON Lines span log
(`smtcomp_cli --trace-json`, `axeyum_solver::span_log`).

## The same-binary control comes first

Two passes over the same 20 `QF_BV` files, back to back on s7 with nothing else
on it:

| | |
|---|---|
| verdicts that moved | **0 of 20** |
| deterministic counter identical | **20 of 20** |
| wall clock, median move | 1.8% |
| wall clock, worst move | 24.7% — on a **3 ms** file |
| wall clock, worst move over 1 s (n=5) | **1.5%** |

So the work counter is exactly reproducible and the wall clock is not. Any
wall-time difference under about 1.5% on a long file, or under a millisecond on
a short one, is the machine.

## Three findings the log made visible

### 1. `--memory-limit-mb 8192` does not bind, and the files it fails to bind
   were previously invisible

Three `QF_LRA` files were killed by the **kernel**, not by any budget:

```
Out of memory: Killed process 2543608 (smtcomp_cli)
total-vm:32671856kB anon-rss:26639452kB
```

Reproduced by hand: 26.6 GB resident, 18.2 s wall, exit 137, under
`--timeout-ms 24000 --memory-limit-mb 8192`. Each of the three left **no row at
all** in the sweep before `scripts/span-log-sweep.sh` was changed to write the
run header the binary could not (`9b40d9007`) — so `QF_LRA` reported 47 files
for a 50-file list and nothing said which three were missing.

The named files:

- `QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2`
- `QF_LRA/LassoRanker/CooperatingT2/afagp-fail.t2.c_Iteration1_Lasso_7-phaseTemplate.smt2`
- `QF_LRA/LassoRanker/CooperatingT2/elmhes.c.i.elmhes.pl.t2.fixed.t2.c_Iteration5_Loop_6-phaseTemplate.smt2`

The first of these is already named in `lra_online::BYTES_PER_ADMITTED_ATOM`'s
docs as the file that aborted at 7.8 GB under the retained-coefficient cost
model. It now aborts at 26.6 GB. **"Where do these bytes go" is the open work
that ADR-1752's admission constant is a placeholder for, and this is a second
measurement of the same file at 3.4x the earlier figure.**

### 2. Two admission screens, two policies, and one refusal 2.3% over its cap

Grouping every `outcome: exhausted` span by the bound it names:

A file can carry more than one, so these do not sum to a file count.

| bound family | files |
|---|---:|
| deterministic budget | 40 |
| projected memory, refused before encoding | 33 |
| admission screen, refused before running | 30 |
| timeout during search | 30 |
| refinement loop ran out of clock | 27 |
| the online UFBV canonical CDCL(T) search's own budget | 5 |

Within the admission screens, two different policies:

- **`QF_LRA`, budget-derived** (`lra_theory.rs`, ADR-1752): the cap is
  `memory_limit_mb / BYTES_PER_ADMITTED_ATOM`, which at 8 GiB is 13,107 atoms.
  Fourteen files refused, carrying 13,637 to 69,199 atoms. The closest is over
  by **4.0%**.
- **`QF_ABV` online UFBV, fixed**: the cap is the constant 1024, and does not
  move with the budget. Fourteen refusals at 1048 (three of them), 1415, 1518,
  2231, 2647, 5220, 7034 (five) and 8202 semantic atoms. **The closest is over
  by 2.3%** — 24 atoms.

The two screens are in the same tree and answer the same question differently.
The `QF_LRA` cap at least moves when a caller pays for it; the UFBV one does
not, and refuses a file 24 atoms past a constant while the memory limit that
constant is standing in for demonstrably does not bind (finding 1).

### 3. Half of `QF_NIA` spends its whole budget in ONE refinement round

All 50 `QF_NIA` files entered the lazy abstraction/refinement loop.

| | |
|---|---:|
| rounds, minimum | 1 |
| rounds, median | 2 |
| rounds, maximum | 106 |
| files whose entire budget is **one** round | **25 of 50** |
| median wall clock of those | 11.2 s |

A round count of 1 and a round count of 106 need opposite fixes — a faster
inner decision versus a better refinement — and until the loop was one span
with a count, both looked the same from outside: `unknown` after 24 s on the
`nia-linearize` route. Forty-four of the fifty files flow into that one route,
and forty-two of those come out `unknown`; it is the widest dead band in the
sweep.

What the log still cannot say is where the time goes **inside** a round.
`LazySmtCounters` totals `skeleton_solve`, `theory_check` and `core_extraction`
over all rounds and records no per-round split, so `loop_hist` is `null` and a
consumer is told so rather than shown equal rounds.

## What is instrumented, by division

The stage spans on a file sum to a fraction of its wall clock. They are **not a
partition** — a query that ran two routes carries stages from both, and a lazy
loop's `theory_check` sits inside the `theory_final_check` that called it — so
read the sum as a bound. A small one is time nothing instruments.

| division | median stage sum, as a share of wall |
|---|---:|
| QF_IDL | 66% |
| QF_ABV | 55% |
| QF_BV | 38% |
| QF_LRA | 34% |
| QF_NIA | 34% |
| **QF_LIA** | **4%** |

`QF_LIA` is 4% because `LiaCounters` carries counts and not one duration: the
integer routes have no stage timings at all. They reach the deterministic axis
through `simplex_pivots` and contribute nothing to a nesting view.

## Where a killed run's budget went

Twenty-three of 300 runs were killed by the watchdog, sixteen of them in
`QF_IDL`. On nine the span holding the budget was still **open**, so the route
inside it has no name — a trace records a route on the way out, and a route that
never returned never wrote itself down.

`QF_ABV/bmc-arrays/bubbleSort.smt2` is the clean example: the open span holds
**24.96 s of a 25.03 s run**, and every recorded rung together accounts for
**36 ms**. A summary that maximises over rungs that finished names `dl-online`
at 10 ms. Every number in that summary is correct and it is not the answer.

## Reproducing

```sh
scripts/span-log-sweep.sh QF_NIA /tmp/QF_NIA.jsonl 50 24000
```

The gallery built from these logs is `axeyum.com/profiling`; the sync script is
`scripts/sync_spans.mjs` in that repository.
