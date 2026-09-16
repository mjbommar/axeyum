# Lane: `lra-warm-basis` — a warm simplex basis across the offline loop's cubes

<!-- plan-section: lane-status -->

**Lane LRA-WARM-BASIS (`MEASURED, SHIPS OFF`, lra-warm-basis, 2026-09-16.)**
ADR: [ADR-2125](../../research/09-decisions/adr-2125-a-warm-simplex-basis-across-sat-decisions.md).
Artifacts: `bench-results/lra-warm-basis-20260916/`.
Compute: **s5, physical core pairs `5,13` and `6,14`**, and nothing else.

Measured. The lever `AXEYUM_LRA_WARM_CUBE` ships **`off`** -- a stable loss on
each `QF_LRA` draw. The result is a MIXED positive, not ADR-2122's clean
negative; see §4.

ADR-2111 named the per-cube cold re-solve as an unpulled lever and ADR-2122
named it again without taking it. This lane took it, sized it first, and found
two things worth more than the lever itself.

### 1. The ceiling was measured before the code, over the whole pinned 200

`simplex_cold_builds` / `_build_ms` / `_ms` / `_pivots` are four additive trail
fields counting the FROM-SCRATCH simplex path. A call is not a rebuild — the
cell cap can decline before allocating, and the same entry point is reachable
from the implied-bound checker — so the quantity a warm basis competes against
was not derivable from the counters that existed.

```
200 rows | 107 decided | 93 undecided
180 reached the lazy-SMT loop | 68 built >=1 from-scratch tableau
 20 never reached it (silent, NOT zero -- folded into no denominator)

share of wall clock over the 68 that re-solve   median     min      max
  tableau CONSTRUCTION only                      0.95 %   0.00 %   1.80 %
  the whole from-scratch call                    4.15 %   0.61 %  99.31 %
  ... plus per-cube linearization                24.21 %  0.93 %  99.58 %

THE LEVER'S CEILING (collect + simplex), 153 rows that reach the loop:
  median 0.00 %   61 rows at or above 10 %   37 at or above 25 %
  restricted to the 73 UNDECIDED rows: median 23.87 %   max 99.58 %

cube churn: median 1.79 flipped literals per round against 7,260 atoms
```

**The basis alone is worth 4 % of the clock at the median.** The lever is worth
more only because a cube it answers also skips the per-cube linearization. The
honest ceiling is 23.87 % on undecided rows, and 0.00 % over every row that
reaches the loop — a file the ladder already decides in 107 ms spends no
measurable time here.

### 2. The arm was INERT, and the cap that refused it is in the wrong currency

The first mechanism check read `warm_cube_checks=0` in **both** arms.
`Incremental::new` refuses at `MAX_TABLEAU_CELLS = 4_000_000` **dense cells**,
and since ADR-2111 this tableau stores nonzeros. On `sc-39.base.cvc.smt2`:
8,797,712 cells against **4,688 nonzeros** — 188 KB of real storage refused by a
cap sized for dense ones, while the cold path (which consults that constant only
under a default-off lever) built the identical system 797 times.

`MAX_TABLEAU_CELLS` is **not** changed — it governs the online engine too.
`with_nonzero_admission` is a second door for one call site, capped at
`MAX_WARM_CUBE_NONZEROS = 400_000` (ADR-2111's own `TableauReserve::Sparse`
figure, 11.6x ADR-2055's measured median and 2.7x its extreme).

`warm_cube_build` now renders `off | built | deadline | resource-limit |
memory-budget | no-tableau`, so a refusal names its screen.

### 3. The prefix reconciliation is the wrong shape for a cube

With the engine admitted, the arm worked and was **slower**: `lra_rounds` fell
798 -> 633, with 1,133,095 retractions over 632 checks — the whole cube, every
round. `SimplexEngine::sync` reconciles by SHARED PREFIX, right for a DPLL(T)
trail (the divergence is a suffix) and wrong for a cube (the flips are anywhere,
so the prefix ends at the first one). `sync_cube` diffs per row instead, which is
z3's `m_columns_with_changed_bounds` shape.

```
assertions per file   1,135,797 -> 4,238   (949 checks, ~4.5 per cube)
lra_rounds                  798 ->   950   (+19 %)
simplex_cold_builds         797 ->     0
warm_cube_cold_restarts               0    (the basis is genuinely kept)
```

### 4. The A/B: a MIXED positive, and it ships `off`

One binary, two env values, arms back to back per file with alternating order.
Both `QF_LRA` draws are PARTIALS and deliberately **not prefixes** -- the run was
stopped and the remainder seeded-shuffled, because `QF_LRA/` path order is
family-clustered on exactly the families the sizing found heaviest, so a prefix
would bias the number TOWARD this lane's own lever.

```
population          rows       A    B   net  gain  LOSS  FLIP  cmp  DIS
QF_LRA pinned       100/200   52   51    -1     0     1     0    97    0
QF_LRA held-out      95/200   49   49    +0     1     1     0    96    0
QF_LIA (partial)      7/200    4    4    +0     0     0     0     8    0
QF_UFLRA / QF_UFLIA / QF_IDL / QF_RDL      DID NOT RUN
```

Mechanism, over the 71 rows where the decider was built: **46,450 cubes
answered, 40,916 from-scratch tableaux -> 0, `cold_restarts = 0`.** Cost
**-9.2 %** (pinned) -- the OPPOSITE of ADR-2122's +12-35 %.

3x recheck: **2 STABLE-LOSS, 1 STABLE-GAIN, 0 UNSTABLE.** The gain
(`sc-14.induction.cvc`) is from the family at 850-1,050 builds -- many small
re-solves. The loss the sizing covers (`ecoliMILPglycerolYices3-50000`) is 28
builds -- few enormous solves, nothing to reuse. The second loss is not in the
sizing table and its builds are uncounted, so that reading is a hypothesis for
it, not a measurement.

**Criteria 2 and 3 both fail (a stable loss on each draw), so the lever ships
`off`.** But this is not ADR-2122's clean negative: it buys a real held-out
verdict, it is faster, and its loss has a named discriminator
(`simplex_cold_builds`) the decider could consult. That screen is the obvious
next increment and is NOT built here.

## Landed

| SHA | files | what |
|---|---:|---|
| `63d7b44e3` | 2 | the sizing instrument: four additive trail fields and a coverage test derived from the struct, no `..` rest |
| `e5728a151` | 11 | `cube_check`, the lever, the invariant and soundness-negative fixtures, the new z3 seed class |
| `47dfee015` | 10 | the inert-arm fix (nonzero admission), the per-row cube diff, the full sizing |
| `83d30e528` | 7 | the ADR, the verified reference citations, the mutation suite |
| `40edfdd64` | 3 | both mutation survivors turned into kills |
| `503bbe8ea` | 5 | the mover recheck and the shuffled-remainder tooling |
| `f6f3d5621` | 9 | clippy `-D warnings` clean (two extractions it forced), plus the A/B data |

## Next

1. Complete both `QF_LRA` draws to 200 (the runner refuses a non-empty output
   file, so a successor resumes rather than rebuilds) and run the five exposure
   divisions with their own denominators.
2. A builds-per-file screen on the decider, A/B'd rather than assumed.
3. Every gate now has a reading. The 22 dispatch/reason suites are green (every
   count nonzero); the lib sweep is **1,576 passed, 1 failed**, the one red being
   `auto::tests::pathological_overbound_stays_terminal_under_every_policy`, which
   passes ALONE in 4.26 s on the same tree (ADR-2111 §5a measured the same test
   at 6.28 s the same way); and `progress_frontier` is **12 passed, 0 failed, 0
   REGRESSION** on an idle pinned frame.

   The ratchet took THREE runs and the disagreement is the finding: on a
   contended box (load 8.98 -> 45.99, calibration 2.00x) it reported a
   `TIMING REGRESSION [nra_degree]` at 24.1 ms against a 23.0 ms ceiling; on an
   idle pinned frame (load 1.11, calibration 1.15x) the same binary on the same
   tree reads **7.2 ms** -- a 3.3x swing at fixed code, reproducing ADR-2122's
   21x lesson on a different family.

   Two families (`bv_reduction`, `lia_cuts`) are NOT COMPARABLE even on the idle
   run, so their ratchets are enforced on nothing; that is what remains. No
   baseline was raised from any run.
