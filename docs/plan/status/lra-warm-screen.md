# Lane: `lra-warm-screen` — a builds-per-file screen for the warm simplex basis

<!-- plan-section: lane-status -->

**Lane LRA-WARM-SCREEN (`MEASURED, SHIPS OFF`, lra-warm-screen, 2026-09-16.)**
ADR: [ADR-2132](../../research/09-decisions/adr-2132-a-builds-per-file-screen-for-the-warm-basis.md).
Artifacts: `bench-results/lra-warm-screen-20260916/`.
Compute: **s5, physical core pairs `5,13` and `6,14`**, and nothing else (both
checked for a previous lane's leftover shards before the first timing; none).

[ADR-2125] shipped the warm basis `off` on 1 STABLE-GAIN against 2 STABLE-LOSS
and named the axis its successor should screen on: `simplex_cold_builds`, *"it
wins where the cubes are many and small and loses where they are few and
large"*. This lane sized that axis, built the screen, and found that **the axis
does not separate the held-out loss**.

### 1. The sizing, over the pinned 200, before any code

ADR-2125 committed per-file trail data for the whole pinned draw, so the axis did
not have to be re-run. The distribution is bimodal and the modes do not overlap:

```
180 of 200 reached the loop | 20 SILENT (report NOTHING, not zero)
 68 built >= 1 tableau; the rest 0

builds  ms/build  file
     1  23,908.0  latendresse/ecoliFBAyicesTest-3875-4
    28     283.5  latendresse/ecoliMILPglycerolYices3-50000  <- the PINNED stable loss
    42     548.1  miplib/danoint-266
841-1543  0.4-6.4  the sc/* family and friends               <- the winning shape

every row at or above 51 builds costs <= 12.2 ms/build
every row above 20 ms/build has <= 42 builds
=> any threshold in [43, 51] separates the two shapes exactly
```

`MIN_WARM_CUBE_SCREEN_BUILDS = 64` is the next power of two above that window:
1.52x the largest few-enormous row, 13.1x below the smallest winning one. Chosen
from a window, not fitted to a point. 51 of the 180 rows that spoke are at or
above it; 129 are below and run exactly as `off` does.

`cold_builds / lra_rounds` is 1.00 above 100 builds, so the screen trips after
~64 rounds — 4.1-7.6 % of the winning family's rounds run cold first. That is
what a screen costs instead of a clock, and **a clock is not available**:
determinism is a public promise, so a wall-clock screen would make the verdict
depend on the machine.

### 2. The finding: the discriminator does not discriminate

ADR-2125 could place only ONE of its three movers in its sizing table and
labelled the reading for the second loss a HYPOTHESIS in as many words. Counted
here:

| ADR-2125 verdict | builds | ms/build | atoms | cold_pivots | file |
|---|---:|---:|---:|---:|---|
| STABLE-LOSS | 28 | 283.5 | — | — | `latendresse/ecoliMILPglycerolYices3-50000` |
| **STABLE-GAIN** | **1,815** | 1.7 | 976 | 466,693 | `sc/sc-14.induction.cvc` |
| **STABLE-LOSS** | **1,598** | 1.0 | 1,272 | 252,412 | `uart/uart-8.induction.cvc` |

**The hypothesis is refuted.** `uart-8` is the many-small shape — the winning
shape — 14 % from the gain. No builds-per-file threshold separates them, so the
screen removes the pinned loss and cannot touch the held-out one. Measured
BEFORE the constant was written into the source.

**The threshold was not then moved to 1,700**, which would separate them: those
two rows ARE the held-out evaluation population, and a boundary drawn between
two of its members is fitted to the set it is scored on.

What separates them instead, offered as two points and explicitly NOT built:
pivots per build per atom, 0.263 on the gain against 0.124 on the loss — a 2.1x
separation that is clock-free. A successor should size it on the pinned 200
first, the way this lane sized builds-per-file.

### 3. What was built

* `AXEYUM_LRA_WARM_CUBE` is three-valued: `off` | `on` | `screened`. Every
  unrecognised spelling is `off`, so a launcher typo measures the shipped route
  rather than a third behaviour nobody named. `on` is KEPT as the A/B's
  reference arm — the screen's claim is comparative.
* The screen reads its OWN always-on counter (`simplex::cold_builds_so_far`),
  not `LazySmtCounters::simplex_cold_builds`, which is armed by `--trace` alone.
  A screen consulting the traced field would route one way in the measurement
  and the other way in production.
* Two additive schema-3 fields (`warm_cube_solve_ms`, `warm_cube_sync_ms`) make
  ADR-2125's un-attributed −9.2 % a split between fields that are both ON the
  line, with no counterfactual. A third (`warm_cube_fill_peak`) takes the
  fill-in measurement ADR-2111 recorded as untaken.
* The dense-cell cap in `Incremental::new` is **not** restated in nonzeros, and
  the reason is a property of the algorithm: a pivot creates nonzeros
  (`select_entering`'s fill-in-minimising rule exists for exactly that), so a
  construction-time count bounds the entry footprint and nothing after it.
* The lever's mode is a parameter of `check_with_lra_dpll_within_mode` with one
  production caller, so the transition fixture can run all three arms in ONE
  process and assert they AGREE rather than each matching a verdict written into
  its own source.

### 4. The attribution: three quarters LINEARIZATION, not the basis

ADR-2125 §8.5 said a successor must not credit its −9.2 % to the basis without
splitting it. Pooled over 67 rows where the decider was built, of 303,177 ms of
theory-layer saving in the `on` arm:

```
linearization   226,396 ms   74.7 %
basis           111,042 ms   36.6 %
Fourier-Motzkin   1,822 ms    0.6 %
residual        -36,083 ms  -11.9 %
```

**Roughly three quarters is the `Collector` rebuild an answered cube never pays
for.** The ratio is not the one the sizing predicted: ADR-2125 §1.3's 4.15 % /
24.21 % puts the linearization at about 4.8× the basis, and measured it is 2.0×.
A ceiling is an upper bound on one term, not a prediction of how two divide.

Getting there took catching my own split being wrong. A TWO-term formula
attributed 64 ms of a 1,906 ms saving on `clocksynchro_2clocks`, because that
file's COLD path decides its cubes by Fourier–Motzkin (`cube_fm_ms=1822` of
`theory_ms=1905`) — the warm decider there replaces a different ENGINE, not a
cold basis. The FM term is 0.6 % pooled and 96 % on that one file, which is
100 % of the pooled term. The residual is a printed column and is NEGATIVE:
folding it into the basis would have reported 25 % instead of 37 %.

Scope, stated because it is narrower than "the −9.2 %": the decomposed delta is
`theory_ms`, not total wall clock.

### 5. The screen's mechanism, on real rows

Over the complete 400 A/B rows: **0 of 244** rows below the threshold had the
screened arm answer a cube warm, and `cold_restarts` is **0 across both
treatment arms on all 400**. Above it, the screen opens on 117 of 123 and
answers fewer cubes than `on` on 112 of the 117.

The three it does not open on are a finding about the SIZING AXIS:
`simplex_cold_builds` counts every route that calls `feasible_within_sparse`,
not the lazy-SMT loops. `sc/sc-24.induction3` carries 2,264 builds with
`lra_entries=0`, `nra_entries=0` and `bound_by=lira-dpll` — no lazy-SMT loop ran
at all. The SCREEN is unaffected because it compares a DELTA from loop entry
(had it read the counter absolutely, that file would have tripped it on round
one); the SIZING over-counts, at 0 of 68 on the pinned 200 where the threshold
was derived and 6 of the 123 at or above it over the complete 400 — all six
on the held-out draw and all six `sc/*.induction3.cvc`, one subfamily.

### 6. The A/B — both `QF_LRA` draws complete at 200

Three arms, one binary (`axeyum.v1`, sha256 `91675258916e4aeb`), order rotating
three ways per file, 24 s / 8 GiB, s5 pairs `5,13` and `6,14`. The two draws are
verified disjoint (200 unique each, 0 overlap). Ship criteria were committed in
ADR §7.1 **before** either shard finished.

```
comparison            rows  off  arm  net  gain  LOSS  FLIP  rc!=0  cmp  DIS
pinned   off/screened  200  107  107   +0     0     0     0      0  194    0
pinned   off/on        200  107  107   +0     1     1     0      0  194    0
held-out off/screened  200   93   93   +0     1     1     0      0  174    0
held-out off/on        200   93   92   -1     0     1     0      0  173    0
```

After the 3×-per-arm recheck of all four movers:

```
                pinned              held-out            total
on              1 gain, 1 LOSS      0 gains, 1 LOSS     1 gain, 2 LOSSES
screened        0 gains, 0 LOSSES   1 gain,  1 LOSS     1 gain, 1 LOSS
```

**`on` reproduces ADR-2125's headline exactly** — 1 stable gain against 2 stable
losses — on a new binary, a new branch base and a complete 400 rows rather than
the two half-draws ADR-2125 could finish.

**The screen is strictly better than `on` on both draws**, and the trade is
legible: pinned it removes the stable loss and gives up `on`'s stable gain on
`sc-7.base.cvc` (1,695 builds — the screen admits it, and the 64 cold rounds
cost the decision inside 24 s, which is the threshold's clearest single price);
held-out it buys a stable gain `on` does not get and takes the same stable loss.

Mechanism: `cold_restarts = 0` throughout; the screen opened on **0** rows `on`
did not; 51 < 71 pinned and 66 < 79 held-out, all nonzero. Cost −13.9 % pinned
and −12.1 % held-out, against `on`'s −16.0 % and −12.4 %.

**The admitted set was predicted exactly.** §1.4 derived from ADR-2125's
committed sizing that 51 of the pinned 200 sit at or above 64 builds; the
screened arm built on exactly those 51 — same set, 0 missing, 0 extra.

### 7. Decision: ships `off`, on criterion 3

Criteria 1, 2 and 5 are met (0 disagreements at 194 and 174; 0 stable losses and
0 flips on pinned — the criterion `on` fails; 51 < 71 and 66 < 79). **Criterion
3 is not met**: `uart-8.induction.cvc` is a stable loss under `screened` too.

"Ships off" is the wrong summary, though. The screen works, it is strictly
better than the arm it screens, and **the axis it screens on is the wrong
axis** — that last is the finding, and it is a conclusion about builds-per-file
rather than about this threshold. The obvious next increment is therefore not a
different value on this counter.

### 8. Two defects found in this lane's own instruments

* **The fuzz runner called a FAILING suite an inert one.** Its count parser was
  anchored on `ok.`, so `FAILED. 3 passed; 1 failed` read as 0 tests and was
  announced as "compiled to nothing" — opposite remedies. It also deleted the
  failing log, the same defect ADR-2125 §5.8 had to fix in its own runner. Both
  fixed; the failure is bounded from the source as a load-sensitive coverage
  floor and **not** a soundness disagreement (`adjudicate` panics only on
  `(Sat, Unsat)`/`(Unsat, Sat)`; a timeout yields `Unknown`, which falls
  through). Which of the two floors fired is unrecovered, and that is stated.
* **Exposure shard 01 ran twice for a minute** because I read an ssh `exit 124`
  as "the launch did not happen" — 124 is the local wrapper, not the work. Every
  row either instance wrote was discarded and the shard relaunched once.

## Landed

| SHA | files | what |
|---|---:|---|
| `4cf519547` | 2 | the sizing: the builds-per-file distribution and a threshold chosen from a window |
| `d9a83d3e7` | 9 | the three-valued lever, the screen, the always-on counter, the attribution fields, the fixtures |
| `44956e4a2` | 5 | the ADR, the refutation of ADR-2125's hypothesis, the verified z3 citations |
| `71817e15b` | 3 | the two mutation suites and this status doc |
| `e3bdf9ac3` | 3 | a two-arm mode; an arm that did not run reports NOTHING, not zero |
| `2fdd1be22` | 7 | `below-screen`: a screened run that never crossed rendered `off` |
| `c7f017a4f` | 2 | the ship criteria, committed before the A/B finished |
| `183a3c346` | 1 | correction: those builds are `lira-dpll`, not the NRA loop |
| `5e0b635d4` | 2 | the THREE-term attribution, after the two-term one did not reconcile |
| `5b69933e7` | 1 | delete the superseded split rather than leave a wrong number in the tooling |
| `60de05922` | 1 | the pinned 200 complete — the screen removes ADR-2125's pinned stable loss |
| `56c2a8dff` | 1 | the held-out 200 complete — the screen cannot remove that draw's loss |
| `eea926282` | 2 | the decision, the mover recheck, and the shard-01 orchestration incident |
| `c0d6a6eb0` | 3 | the recheck's raw rows and the derived mover list |
| `76fe33037` | 3 | the fuzz runner called a failing suite inert, and deleted the evidence |

## Next

1. The five exposure divisions (running; `QF_LIA` first on both shards).
2. Size **pivots per build per atom** on the pinned 200 — the shape §2 observed
   on two held-out rows at 0.263 against 0.124 and deliberately did not build
   on, because both points are held-out rows.
3. Split `simplex_cold_builds` per route. It counts every caller of
   `feasible_within_sparse`, not the lazy-SMT loops; the screen is unaffected
   (it compares a delta from loop entry) but the SIZING over-counts, at 0 of 68
   on the pinned 200 and 6 of 123 over the complete 400, all one subfamily.
