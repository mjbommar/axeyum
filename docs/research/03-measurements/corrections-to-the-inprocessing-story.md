# Four corrections to what I said about inprocessing

Measured 2026-09-08 by the cost-decomposition lane over the pinned 200-file
QF_BV parity list at the protocol's 24 s / 8 GiB. Each item below is something
I asserted earlier in the day that the measurement contradicts.

## 1. Break-even is 12-24 s, not ~120 s

I relayed "the benefit only appears at roughly 5x the competition limit" as
established. Measured on the shipping path:

| arm | 1 s | 3 s | 6 s | 12 s | 24 s | PAR-2 |
|---|---:|---:|---:|---:|---:|---:|
| off | 158 | 172 | 177 | 184 | 186 | **817.5** |
| inproc | 124 | 144 | 156 | 172 | 188 | 1027.8 |
| inproc+vivify | 133 | 152 | 161 | 176 | 188 | 960.7 |

The crossover is at or below the 12-24 s band. The 120 s figure was never
re-derived on the current tree.

## 2. But it is NOT a win, and the honest statement is narrower than the table

One of the two apparently gained files was a harness flake -- a 575-byte query
whose `off` row said `killed` and which re-runs to `unsat` in 0 ms. The real
gain is ONE file, and that file decides in only 1 of 5 repeats under load.

**The defensible claim is parity on decided count at 24 s and BEHIND on PAR-2.**
Not a win. I would have quoted "+2 files" from the table; the lane checked its
own rows and found the flake.

## 3. The `sat`-reconstruction blocker I stated does not hold

I told the user that enabling inprocessing "would produce `sat` verdicts we
cannot check against the original term", relaying a sibling lane's reading. It
is wrong. `reconstruct_sat_result` composes `compaction.expand` with
`reconstruction.extend`, and `handle_sat_result` replays the model against the
original assertions; a bad model returns `Unknown`, never `sat`. Corpus
evidence: 188 decided per arm, 173 cross-checked against declared `:status`,
**zero disagreements and zero cross-arm conflicts**, with the inprocessing arms
GAINING rather than losing files -- the opposite of a broken reconstruction's
signature.

What IS genuinely unresolved is the **`unsat` certificate**: per ADR-1750 the
proof is checked against the REDUCED formula, so the BVE link is trusted rather
than checked. That -- not cost, and not model reconstruction -- is what blocks
enabling this by default.

I propagated a code-reading as a measured blocker. The lane that owned the
measurement checked it and refuted it.

## 4. My variance hypothesis was half right, and the half that was wrong matters

I proposed that a wall-clock cutoff halts a pass mid-way, and predicted
run-to-run instability tracking host load. Measured: truncation NEVER flipped
across identical repeats -- where BVE was cut off, it was always or never cut
off. Matched-file spread is 1.01x-1.03x even at load 40, and the truncating arm
is the STEADIER one (`bench_3293`: 12,314-12,365 ms with inprocessing on, a
1.00x spread, against 188-305 ms with it off, 1.62x).

So the effect is real as **budget DEPENDENCE** -- halving the budget halves the
spend, measured -- and not as run-to-run instability. The deterministic-budget
argument survives on determinism grounds; the "noisy under load" argument does
not. The quiet-host comparison did not run, so the spread is an upper bound.

## What the measurement found that nobody had asked for

- **BVE is 81% of inprocessing cost** (278 s of 342 s), subsumption 18%. The
  cost is inside the pass, not in re-encoding around it.
- **The single biggest lever:** 16 of 195 files spend their ENTIRE slice inside
  a BVE that is then cut off unfinished -- 55% of total spend on 8% of files --
  and five of those are decided by the baseline in 88-116 ms. A cheap admission
  test recovers nearly all of it. Median spend 28 ms; mean 63x the median.
- **Turn vivification ON**, which is the opposite of its reputation as the
  expensive pass: 45 ms of vivify converts an 11,468 ms TRUNCATED BVE into a
  27 ms COMPLETED one on four of five files, making inprocessing 20% cheaper
  overall with better shrink.
- **`dump_dimacs` is not a faithful mirror of the shipping encoding** -- 3 of 14
  comparable files differ, `dump_dimacs` larger every time, one by 2x. Any
  CNF-level measurement assuming otherwise is about a different formula.
- **Both sweep guards passed on an empty population** (`rows == attempted` is
  0 == 0). Found by walking into it, fixed with a negative control that now
  exits 1 where it previously exited 0.
