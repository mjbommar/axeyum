# The QF_LRA lane refuted my framing twice, and both corrections generalize

Measured 2026-09-08. Recorded because in both cases the wrong version is
plausible, was written into a brief by me, and would have directed weeks.

## 1. The "cheapest decisive measurement" was measuring nothing

I briefed a diagnostic as step 1: read `final_check_core_widenings` on the
QF_LRA miss population, on the grounds that a Farkas decline widens a conflict
to the entire asserted set and would look exactly like "simplex is slow".

The counter printed `n/a` on **every** QF_LRA file, and had since `ea85c9813`
(2026-09-07) moved the shipped QF_LRA route from `CdclT` to the native
proof-producing core. `native_cdclt::theory_layer_stats` ended in
`..Default::default()` under a comment saying it "does not measure" those
counters -- while all seven arrived inside its own `engine` argument, already
filled by `LraTheory::engine_counters`. **It was discarding values it held in
hand.**

Two things made this invisible:

- The eight fields ABOVE the gap printed real numbers, so the line looked
  healthy. A partially-populated record reads as a populated one.
- A prior lane had reported "H2 refuted, widenings = 0" -- **measured on a route
  QF_LRA no longer takes.** A refutation inherits the staleness of its route.

With the counter actually wired, the answer is genuinely zero: over 33 miss
files, all three decline arms are 0 in both pivot arms. So the conclusion was
right and the evidence for it was not. Do not spend effort on the Farkas decline
paths for QF_LRA.

The guard added with the fix is the reusable part: it destructures the struct
with **no `..` rest**, so the field list is the struct's rather than the
author's. It broke the build twice while counters were being added, as designed.

## 2. The sparse-tableau headline was the wrong ranking

I briefed the cross-linked sparse tableau as the headline item, on our own
recorded 1.41 ms/pivot at 350x425.

The tableau is **1.4% dense** (2,097 nonzeros in 148,750 cells), which makes the
rewrite look obvious. It is not. **The pivot's operation count was already
sparse** -- 1,392 multiply-adds, not 148,750. What was dense was everything
AROUND it: three `O(columns)` scans and 27 KB of allocation per pivot. Both were
removed WITHOUT any representation change, verified by byte-identical counters
(same pivots, same final checks, same cells written; `entering_scan_cells`
22,842 -> 604).

What remains for a sparse rewrite is a *cache* argument over 4.76 MB of storage
holding 50 KB of live data. Worth doing. **Do not predict the 40x the density
ratio suggests** -- the density ratio was never the operation count.

## 3. The finding under the finding, which is the transferable one

Switching the entering rule gained `blending/1` (unknown at 24 s -> unsat in
6.7 s) and cost `blending/24` (306 ms -> 3,105 ms, 10.1x, same verdict).

Both obvious explanations are **refuted by counters**: per-pivot cost is
identical (1,569 vs 1,561 cells) and mean core width is identical (45.8 vs 46.0
literals). The search simply takes 11.8x more final checks, and sweeping
`bland_threshold` over 0/1/10/100/1000 never recovers it.

> An entering rule is a **search-trajectory** change, not only a cost change,
> and its effect on the trajectory is uncorrelated with both quantities you
> would use to predict it.

"3.45x fewer cells per pivot" is true about one file's pivots and false about
the division. This is the same shape as the clause-database result the same day:
25% fewer conflicts, 28% more watch visits, net worse.

## 4. The measurement that is now the cheapest thing on this division

**22 of the 33 QF_LRA miss files print no theory-layer line at all** -- the
watchdog abandons the worker before it returns, and the counters live inside it.
The whole `sc/` (11) and `sal/` (7) families.

So "the simplex is slow" is a claim about **11 of 33** losses. For the other 22
we cannot see inside at all. That is the previously-noted third census class
with a mechanism attached.

## Carried forward

- QF_LIA and QF_UFLIA get the new pivot rule for free (same
  `simplex::Incremental`) but produce **no** `TheoryEngineCounters`, so a lane
  measuring there is blind exactly as this one was. Wiring it requires LIA to
  actually count the fields: they are `u64`, so a `0` would read as measured.
- The violated-basic priority heap is open and independent; `leaving_scan_rows`
  is now in the trace line, so it is one measurement from being costed.
