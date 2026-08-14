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

Calibration kernel (`calibration_kernel`, 4 MiB stride walk, median of 9),
2026-08-14, 1-minute load 7.6:

| pinning | medians (ms) |
|---|---|
| `taskset -c 0-7` (P-cores) | 118.9, 121.0, 122.0, 122.5, 123.0, 123.1, 126.0, 126.4 |
| `taskset -c 16-23` (E-cores) | 126.5, 132.2, 132.7 |
| unpinned, load 12.4 | 203.4, 274.1, 375.7 |

And the frontier itself, measured directly — this is the decisive one:

| gate | pinning | frontier | what it reported |
|---|---|---|---|
| stock (fixed 4000 ms budget) | `taskset -c 16-23` (E-cores), load 5.9 | **29** | **REGRESSION** below the committed baseline of 30 |
| calibrated | `taskset -c 16-23` (E-cores), load 7.1 | **35** | budget scaled 1.42x; `PROGRESS (+5) — ADVISORY ONLY`; `NOT COMPARABLE` (throughput moved 47 % mid-sweep) |

The stock gate reports a *regression that never happened* purely because the
work landed on efficiency cores. A hostname match would have certified that
comparison as valid. "The machine" is not a speed.

The calibrated gate does both halves of its job in that one line: it recovers
the number (29 to 35, above the baseline again) **and** refuses to let it be
used — a reader who saw only "PROGRESS +5" would have ratcheted a baseline off a
run whose budget was 42 % larger than the reference's.

The stock gate reports a *regression that never happened* purely because the
work landed on efficiency cores. A hostname match would have certified that
comparison as valid. "The machine" is not a speed.

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

## Constants, and what would invalidate them

- `CALIBRATION_REFERENCE_MS = 118.0` — the **minimum** of the eight P-core
  medians above. The minimum rather than the mean because it is the closest
  available estimate of uncontended speed, and because the error is asymmetric:
  a reference that is too slow shrinks every budget and manufactures
  regressions. The box was shared while this was taken, so the true idle value
  is probably a few percent lower; `calibration_frames_the_measurement` prints
  the live median on every run, so a quieter measurement below it should be
  taken as a correction and committed.
- `CALIBRATION_CHECKSUM` freezes the kernel. Change the kernel and the test
  fails, because the reference then describes work that no longer exists.
- `CALIBRATION_REPEATS = 9`. At load 12.4 three consecutive medians-of-**five**
  on the same pinning were 219 / 114 / 352 ms; nine samples (~1.2 s) survive one
  lane's build starting mid-window.

## What this does not fix

- **Contention that arrives mid-sweep** is detected (the drift check) but not
  corrected: the budget is fixed when the sweep starts. Per-instance
  recalibration is the obvious next step and costs ~3 % of budget per instance.
- **The kernel is a proxy.** It mixes ALU and memory-bandwidth pressure, which
  is the right shape for a bit-blasting solver, but no synthetic kernel tracks
  another program's slowdown exactly. The clamp and the comparability band are
  there because of that, not in spite of it.
- **`MAX_N = 40` is a ceiling, not a frontier.** `bv_reduction` now reaches it,
  so a reading of 40 means "at least 40" and cannot show progress. That is a
  separate defect in the ratchet and is listed in this lane's `RESULT.md`.
