# DEADLINE-OVERRUN — what the fix actually bought

Merged `47f902ea1`, 2026-09-12. Arms: `main` at `22399a814` vs the lane branch.
Every A/B here is **interleaved per file** — both arms back to back on the same
pinned core, arm order alternating — so ambient load cancels in the difference.
That mattered: the box ran at load 14–16 throughout.

## The result

| division | converts | losses | flips |
|---|---:|---:|---:|
| QF_UFLIA | **+5** | 0 | 0 |
| QF_UFLRA | **+2** | 0 | 0 |
| QF_LRA | 0 | 0 | 0 |
| regression control (arith, already-decided, **677 files, complete**) | n/a | **0 real** (1 flake, proven) | **0** |

Both converted QF_UFLRA files agree with z3, cvc5 **and** their declared
`:status` (`Problem01_00` and `Problem02_10`, both `unsat`).

## The census is not the headroom

QF_UFLRA has **51** watchdog kills. All 51 were run, not sampled. **2 convert.**

The other 49 are two families — `cpachecker-induction.32_1_cilled…` and
`cpachecker-induction.minepump_spec*_product*` — that still land at
25.02–25.04 s, unchanged. z3 decides them in 0.2–0.5 s.

**A census of a failure MODE is not a count of fixable files.** The board-wide
149 says how often the solver overruns its own deadline, not how many files any
one fix wins. This is the third time in one session a count was read as
headroom; the other two were QF_NIA's width class and the watchdog's own first
census.

## The one apparent loss was noise, and here is the proof

`QF_LRA/sc/sc-5.base.cvc.smt2` came back `unsat` 22.43 s (main) →
`unknown` 24.13 s (lane) in the sharded control. Re-run three times interleaved
on a quiet core at a 24 s budget:

| run | main | lane |
|---|---|---|
| 1 | unknown 24.04 s | unknown 24.13 s |
| 2 | unsat 21.83 s | unsat 22.33 s |
| 3 | unsat 21.83 s | unsat 21.83 s |

The file sits on the 24 s boundary and flips for **both** arms with ambient
load. Reported rather than netted out. A single interleaved pairing still flakes
near the boundary — interleaving removes the systematic component of load, not
its variance.

## The residual is not where the lane's note predicted

That note closes by naming `lra::solve` (Fourier–Motzkin) "on a path whose
deadline is still `None` above it — one more constant to find". On merged main
`lra::solve` **takes** a deadline, **polls** it in both of its loops, and its one
production caller (`lra::decide_within`) passes a real one. That is not the gap.

The actual obstacle is upstream of any fix: **a watchdog kill destroys its own
diagnosis.** `minepump_spec1_product56` at a 24 s budget with `--trace` records
`fd:parse`, `probe`, `dl-online` declined, `nra-real-root` declined, `nra`
declined `unsupported` — all within 38 ms — and then **25 seconds of nothing**.
The worker is killed before it can record which route it was in, so the trail's
last entry names a route that had already returned. Lane `WATCHDOG-RESIDUAL`
(ADR-1926) starts there: instrumentation before fix.

## Files

| file | rows | what |
|---|---:|---|
| `uflra-watchdog-ab.tsv` | 29 | the watchdog files not covered by the serial arm |
| `uflra-ab-serial.tsv` | 41 | the serial board-order arm, includes both converts |
| `uflia-ab.tsv` | 199 | QF_UFLIA, the +5 |
| `lra-ab.tsv` | 199 | QF_LRA, the +0 |
| `regression-control.tsv` | **677** | already-decided arithmetic files, slowest-first — COMPLETE: 395 `sat>sat`, 251 `unsat>unsat`, 29 `unknown>unknown`, 1 flake, 0 flips |

Columns are `file, before, before_s, after, after_s` (the board-order arm carries
a header row; the sharded arms do not).

The regression control was deliberately ordered **slowest-first** using the
board's own timings: a file decided in 0.4 s cannot be affected by a deadline
poll, and 57% of the original list was that. The informative tier is the 117
files above 5 s.
