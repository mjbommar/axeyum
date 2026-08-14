# The frontier ratchet needs a reference frame, not a reference machine

**Status:** implemented in `crates/axeyum-solver/tests/progress_frontier.rs`
(2026-08-14). This note carries the measurements the code's constants are set
from; the rules themselves live next to the code that enforces them.

## The problem, in one table

`frontier_bv_reduction`, same commit, same machine (`server0`, i9-12900K,
24 threads), four readings inside 24 hours:

| frontier | conditions |
|---|---|
| 35 | written 23:33 during a 7-agent campaign, 1-minute load 34 |
| 38 | the committed JSON artifact |
| 39 | 2026-08-14 10:31, load 5.4 |
| 40 | re-run at load 1.17 (and 40 is `MAX_N`, the sweep ceiling) |

A 14 % spread with no code change. Committing the 35 ratchets the roadmap floor
down on a contaminated reading; committing the 40 sets a floor that no smaller
box — and not even this box under load — can meet. Both are wrong, so the
finding stayed in prose and no number moved. That is the failure this note
closes.

An earlier instance is already in the register: the same gate failing on a
4-core box at 26 against a baseline of 30, with the lost instances returning
`unknown` at ~4009 ms against a 4000 ms budget — at the measurement's own
resolution limit.

## Why "declare a reference machine" is not enough

It was the other option on the table, and this box refutes it. A 12900K is
8 performance cores (5.1-5.2 GHz) plus 8 efficiency cores (3.9 GHz), so the
*same binary on the same machine* runs at two speeds depending on where the
scheduler puts it.

And the frontier itself, measured directly — this is the decisive one:

| gate | pinning | frontier | what it reported |
|---|---|---|---|
| stock (fixed 4000 ms budget) | `taskset -c 16-23` (E-cores) | **29**, four runs out of four | **REGRESSION** below the committed baseline of 30 |
| calibrated, first (memory-bound) kernel | same | 35, 30, 30 | scale only 1.11-1.42x — under-compensated, see below |
| calibrated, shipped kernel | same, load 6.7 | **40** | scale 2.34x, budget 9370 ms; `PROGRESS (+10) — ADVISORY ONLY`; `NOT COMPARABLE` (27 % drift mid-sweep) |

Unpinned on the same box the same day: 39-40. So the calibrated gate recovers the
number the machine is actually capable of (29 to 40) while the stock gate reports
a regression that never happened, deterministically, four times out of four.

The stock gate reports a *regression that never happened* purely because the
work landed on efficiency cores. A hostname match would have certified that
comparison as valid. "The machine" is not a speed.

The calibrated gate does both halves of its job in that one line: it recovers
the number (29 to 35, above the baseline again) **and** refuses to let it be
used — a reader who saw only "PROGRESS +5" would have ratcheted a baseline off a
run whose budget was 42 % larger than the reference's.

## What the gate does instead

Immediately before each family's sweep, and again after it:

1. Time a frozen synthetic kernel (`calibration_kernel`, checksum-pinned) —
   deliberately unrelated to anything this repository optimizes. An earlier
   draft calibrated with a small `check_auto` instance, which is self-defeating:
   improving the lever under measurement would shrink the budget and cancel the
   improvement out.
2. `scale = median_now / CALIBRATION_REFERENCE_MS`, clamped to
   `[1/3, 3]`; the per-instance budget is `4000 ms x scale`. A busy or slower
   box gets proportionally more clock for the same instance, so the frontier it
   reports stays comparable with the reference machine's.
3. Record the machine (host, cpu count, model), both load averages, both
   calibrations, the scale, and both verdict flags in
   `bench-results/frontier/<family>.json`, next to the number.

And it says when it cannot compare:

- **Not comparable** — `scale` outside `[1/3, 3]`, or throughput drifted more
  than 25 % between the two calibrations. The frontier is printed and written,
  and the ratchet is *not enforced* on it. A `REGRESSION` from an uncomparable
  run is a statement about the box.
- **Not ratchetable** — `scale` outside `[0.9, 1.25]`. The number is real, but
  it may not be used to RAISE a baseline: a stretched budget can manufacture
  progress (the 35's environment), and an idle fast box does more work per
  second than the machine the baselines were set on (the 40).

`available_parallelism` reflects the CPU affinity mask, so a pinned run records
its own pinning in the artifact (`"cpus": 8` under `taskset -c 0-7`).

## The proxy has to be validated against the thing it proxies

This is the part that is easy to skip and was nearly skipped here. The first
kernel walked 4 MiB — main memory — and so was latency-bound on a resource both
core types share. It reported E-cores as **1.2x** slower while the `bv_reduction`
sweep is **1.84x** slower there (median over every instance above 200 ms, same
commit, same load, from the two runs' JSON curves). Under-reporting the slowdown
under-compensates the budget, which is the exact failure the calibration exists
to prevent: with that kernel the E-core run recovered only 29 to 30.

Candidates, measured under the test profile's flags (`opt-level=0`,
`debug-assertions`, `overflow-checks`), `taskset` on each core class:

| kernel | P-core | E-core | ratio | against the solver's 1.84 |
|---|---|---|---|---|
| 4 MiB stride walk | 142.5 ms | 203.4 ms | 1.43 | far under, and noisy (P ranged 114.9-143.7) |
| 32 KiB dependent chain | 64.7 ms | 109.0 ms | 1.68 | under |
| **256 KiB dependent chain** | 70.4 ms | 137.8 ms | **1.96** | closest, stable to ~2 % |

(Absolute times in that table are from a standalone probe at 6M iterations; the
shipped kernel runs 10M, and in the test binary measures 127.1-128.1 ms on
P-cores and 221.5-246.7 ms on E-cores — ratio **1.74**, still the closest
available proxy for 1.84 and stable to 0.8 % on the reference core class. The old
4 MiB kernel measured 1.2x in that same binary.)

The shipped kernel is the third: an L2-resident buffer, a data-dependent
unpredictable branch, and an index that depends on the value just computed, so
the loop is a serial dependency chain with branch mispredictions — structurally
closer to propagation than to a streaming benchmark. **Any change to the kernel
must re-run this comparison.** A proxy whose ratio does not track the workload's
is a budget that compensates for the wrong thing, and it will look perfectly
healthy while doing it.

## Constants, and what would invalidate them

- `CALIBRATION_REFERENCE_MS = 127.0` — the **minimum** of five medians-of-nine
  on P-cores at load 4.0 (127.1, 127.3, 127.3, 127.5, 128.1 ms; a 0.8 % spread,
  so minimum and mean agree to within noise). The minimum rather than the mean
  because the error is asymmetric: a reference that is too slow shrinks every
  budget and manufactures regressions. `calibration_frames_the_measurement`
  prints the live median on every run, so a quieter measurement below it should
  be taken as a correction and committed.
- `CALIBRATION_CHECKSUM` freezes the kernel. Change the kernel and the test
  fails, because the reference then describes work that no longer exists.
- `CALIBRATION_REPEATS = 9`. With the old memory-bound kernel, three consecutive
  medians-of-**five** on the same pinning at load 12.4 were 219 / 114 / 352 ms.
  Nine samples (~1.2 s) survive one lane's build starting mid-window; the
  L2-resident kernel is also far steadier in its own right (0.8 % across five
  runs, against a 3x spread for the memory-bound one).

## What this does not fix

- **Contention that arrives mid-sweep** is detected (the drift check) but not
  corrected: the budget is fixed when the sweep starts. Per-instance
  recalibration is the obvious next step and costs ~3 % of budget per instance.
- **The kernel is a proxy.** A dependent chain with unpredictable branches over
  an L2-resident buffer tracks this solver's core-class sensitivity to within
  6 % (1.74 against 1.84), which is the closest of the three candidates measured
  — but no synthetic kernel tracks another program's slowdown exactly, and
  nothing guarantees it stays close as the solver changes. The clamp and the
  comparability band are there because of that, not in spite of it. Re-run the
  ratio comparison when the solver's inner loops change substantially.
- **The suite gets slower on a slower box, by construction.** The budget is
  stretched, so wall time stretches with it: a 2x-slower machine takes roughly
  2x as long, and the `[1/3, 3]` clamp caps that at 3x. The early stop after
  three consecutive undecided points bounds it in practice.
- **`MAX_N = 40` is a ceiling, not a frontier.** `bv_reduction` now reaches it,
  so a reading of 40 means "at least 40" and cannot show progress. That is a
  separate defect in the ratchet and is listed in this lane's `RESULT.md`.
