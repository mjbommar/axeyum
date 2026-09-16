# Lane: `lra-warm-screen` — a builds-per-file screen for the warm simplex basis

<!-- plan-section: lane-status -->

**Lane LRA-WARM-SCREEN (`IN PROGRESS`, lra-warm-screen, 2026-09-16.)**
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

### 4. The A/B

IN PROGRESS — three arms (`off` / `on` / `screened`), one binary, order rotating
three ways per file, 24 s / 8 GiB, `QF_LRA` pinned 200 and ADR-2125's held-out
200 running first on disjoint core pairs.

## Landed

| SHA | files | what |
|---|---:|---|
| `4cf519547` | 2 | the sizing: the builds-per-file distribution and a threshold chosen from a window |
| `d9a83d3e7` | 9 | the three-valued lever, the screen, the always-on counter, the attribution fields, the fixtures |
| `44956e4a2` | 5 | the ADR, the refutation of ADR-2125's hypothesis, the verified z3 citations |

## Next

1. Finish the three-arm A/B on both `QF_LRA` draws at 200, recheck every mover
   3x per arm, then the five exposure divisions.
2. Report the −9.2 % split between the basis and the skipped linearization.
3. Size `pivots per build per atom` on the pinned 200 — the shape §2 observed on
   two held-out rows and deliberately did not build on.
