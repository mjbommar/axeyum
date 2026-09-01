# ADR-1465: Draw 18 clears the dispatchable floor, and the plan ADR-1450 handed off was refused at R11 before it was authored

Date: 2026-09-01
Status: Accepted
Lane: `nursery-draw-18`

Index-summary: Authored the four-family draw ADR-1450 named the unblock for
(`Mathlib.Data.Nat.Factorization.LCM` held-out + two window fillers +
`Mathlib.Data.Nat.MaxPowDiv` held-out). The window filler ADR-1450's own
follow-on commit proposed -- `Factorization.PrimePow` + `Factors` +
`Factorization.Basic` + `Factorization.Induction` as development -- is
REFUSED at R11: every one of those three `Factorization.*` modules shares the
topic segment "Factorization" with `natural-factorization-lcm` itself, so
publishing it beside LCM held-out in the same draw is exactly the topical-
overlap shape R11 exists to catch. Measured against the real
`screen_family()`, not asserted. Repaired with a topic-clean filler
(`Factors` + `NumberTheory.FactorisationProperties`, 17 rows) reaching the
same row count without the collision. `check-dispatchable-frontier.py` now
reports 22 dispatchable against a floor of 10 (was 2).

Index-status: Accepted

## Context

`check-dispatchable-frontier.py` failed G7 at 2 dispatchable mirrors, floor
10. ADR-1430 declared `Nat.count`/`Nat.divMaxPow`; ADR-1450 (draw 17) refused
`Nat.count` as held-out (a definitional alias of `Nat.countRange`, 22 existing
lemmas cover 4-5 of its 10 drawn rows) and named the unblock: declare a
construction opening a module sorting lexicographically before
`Mathlib.Data.Nat.MaxPowDiv`, topic- and vocabulary-clean, leaving room for
two more families in the window between it and `Factorization.LCM`.

Before this lane started, a prior lane in the same session (commit
`36f85826f`) declared `Nat.factorizationLCMLeft`/`Right`, opening
`Mathlib.Data.Nat.Factorization.LCM` (pool 10), screened it clean as a fresh
held-out candidate, and recorded its R11 disclosure review. Its commit message
proposed the window filler and left the draw itself, plus `MaxPowDiv`'s own
disclosure review, to the next lane.

## Re-measurement, before anything

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=460 env=2838` |
| `check-autogenesis-nursery.py` | 0 | now green (was red per ADR-1450; the cross-population component was fixed since) |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=186 verdict=PASS` |
| `check-holdout-adjacency.py` | 0 | 18 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-dispatchable-frontier.py` | 1 | G7, 2 dispatchable, floor 10 |
| `validate-facts.py` | 0 | 2536 facts, 0 errors |

## The proposed filler fails R11 -- measured, not inherited

The commit message that opened `Factorization.LCM` proposed the second window
filler as `Factorization.PrimePow` + `Factors` + `Factorization.Basic` (5) +
`Factorization.Induction` (1) = 10 rows, development. Screened against the
REAL `select()`/`screen_family()`/`screen_draw()` machinery
(`docs/research/09-decisions/adr-1465-draw-18-screen.py`), with the four
families installed exactly as proposed:

```
R11 natural-factorization-lcm          refused  topic=1 vocab=2/10 env=[...]
      topic: its module topic segments are already a development/train
      family's -- Factorization (published by natural-prime-power-factorization)
```

`topics()` strips the leading library component and generic segments
(`Data`, `Basic`, `Nat`, …) but not `Factorization` -- so
`Mathlib.Data.Nat.Factorization.LCM` and
`Mathlib.Data.Nat.Factorization.{PrimePow,Basic,Induction}` share the segment
`Factorization`, and R11's shape-1 topical-overlap screen refuses exactly
this: a held-out family (LCM) sitting beside a development family
(the PrimePow bundle) that teaches the same Mathlib namespace. This holds
regardless of which module in the bundle is listed first (the sort-order
`primary`); the topic union is over every module the family draws, not just
the primary.

A window probe (strict range `Mathlib.Data.Nat.Factorization.LCM <
module < Mathlib.Data.Nat.MaxPowDiv`) confirms the window itself has only
three modules with a nonzero screened pool: `Factorization.PrimePow` (2),
`Factors` (2), `Log` (17) -- 21 rows, matching ADR-1450's own count. Every
combination reaching 10 rows without `Log` alone therefore needs
`Factorization.PrimePow`, which alone is enough to trigger the collision
(it shares the segment `Factorization` with LCM independent of `Basic`/
`Induction`).

## The repair

`Mathlib.Data.Nat.Factors` (2 rows, topic `Factors` -- a **different word**
from `Factorization`, no collision) bundled with
`Mathlib.NumberTheory.FactorisationProperties` (15 rows, topic
`FactorisationProperties` -- again a different word) reaches 17 rows, more
than the 10 the refill takes, with `Factors` as the sort-order primary (its
own path, `Mathlib.Data.Nat.Factors`, sorts strictly inside the LCM->MaxPowDiv
window; the secondary module's path does not need to). Topically coherent:
both are about the factors / factorisation-theoretic properties (`Abundant`,
`Deficient`, `Perfect`) of a natural number.

`FactorisationProperties` carries a `do-not-draw-held-out` verdict from
ADR-1115 in `holdout-adjacency-review-v1.json`'s `refused` list. That bar is
**held-out-scoped**: `assert_draw_lawful` (ADR-1450) checks `barred_modules`
only against families whose partition is `held-out`
(`scripts/check-holdout-adjacency.py:605-623`), so using the module in a
development family raises nothing. Verified live in the screen run --
`natural-factors-and-factorisation-properties` (development) draws it and
`R11 hard signals clean` reports no refusal from either the topic/vocabulary
screen or `assert_draw_lawful`'s bar check.

`Mathlib.Data.Nat.MaxPowDiv` alone yields 7 rows, short of `PER_FAMILY=10`
(reproducing a number the prior lane's own status document recorded, which
ADR-1450's table itself omitted). Bundled with `Mathlib.NumberTheory.Bertrand`
(4 rows: the postulate itself plus its induction-step lemma) it reaches 11.
Bertrand's own topic (`Bertrand`) collides with nothing published.

## The draw, screened against the real machinery

`docs/research/09-decisions/adr-1465-draw-18-screen.py` loads
`gen-autogenesis-nursery-refill.py` and `check-holdout-adjacency.py` by path
and runs the actual `select()` / `assign_partitions()` / `screen_draw()` /
`screen_family()` / `is_closed_evaluation`, exactly like
`adr-1240`/`adr-1245`/`adr-1255`'s screens. `propose-nursery-refill.py` is
deliberately not used (it has no fact-ledger screen, no `HELD_OUT_CONSTRUCTIONS`
check, no R5 analogue, and overcounts against the real generator).

```
cycle assignment over the four fresh families, in sort order:
  [0] natural-factorization-lcm                 held-out     Mathlib.Data.Nat.Factorization.LCM
  [1] natural-factors-and-factorisation-properties development  Mathlib.Data.Nat.Factors
  [2] natural-logarithm-base                    train        Mathlib.Data.Nat.Log
  [3] natural-max-power-dividing                held-out     Mathlib.Data.Nat.MaxPowDiv

ok  the draw adds 40 entries                got 40
ok  control: natural-factorization-lcm yields 0 without its constructions
ok  R12: no new held-out row is a closed evaluation                []
ok  R11 hard signals clean (disclosure off)
ok  R11+disclosure both families clean (after writing MaxPowDiv's review)
ok  no existing family's drawn ten churns                          []
ok  NEGATIVE CONTROL: a deliberately flipped partition in a copy IS detected
ok  no standing held-out family's recorded review goes stale        []

ADR_1465_DRAW_18_SCREEN|env=2838|new_entries=40|churn=0|stale_reviews=0|r12_violations=0|failures=0
```

The partition assignment is purely mechanical: each family's cycle position
comes from `FAMILY_MODULES[f][0]`'s lexicographic path, sorted, cycled
`held-out, development, train, held-out`. No target outcome was consulted --
`Factorization.LCM` was already fixed at index 0 by the prior lane, and this
lane's only choice was which real, topic-clean modules to combine for the two
fillers and for `MaxPowDiv`'s companion.

## The `natural-max-power-dividing` disclosure review

Written into `holdout-adjacency-review-v1.json`. Live sweep:
`[["prime", "Int.Coprime", 111], ["max", "CReal.evt_approx_max", 44],
["divmaxpow", "Nat.divMaxPow", 2]]`. Stem by stem:

- `prime` (111 kernel names): overwhelmingly the substring inside
  `Coprime`/primality-shaped names, plus the genuine `Nat.Prime` package
  (characterizations, divisibility, small-case evaluation). Grepped the tree
  for `bertrand` (case-insensitive) and for any lemma bounding a prime
  between `n` and `2*n`: zero hits. Nothing here entails Bertrand's postulate
  or its induction step.
- `max` (44): `CReal.evt_approx_max` and neighbours -- a different carrier
  (constructed reals, not `Nat`) and a different concept (an eventual
  Cauchy-sequence approximation bound, not a natural-number binary max). Pure
  word collision.
- `divmaxpow` (2): `Nat.divMaxPow`/`Nat.divMaxPowAux` themselves, the ADR-1430
  definitions, with zero `.theorem(` call sites naming either -- the
  ADR-0653 discipline visible directly in the sweep.

Verdict: our development settles nothing in the drawn ten, under any name.
Held-out-safe.

## The zero-diff invariant over already-drawn rows

No already-drawn row may change partition or membership. Comparing the
committed `nursery-v2-extension.json` before this lane's edit (460 entries)
against the regenerated one (500 entries), by `fact_id`:

```
old entries: 460  new entries: 500
old rows missing from new: 0
POSITIVE: rows present in both, byte-identical: 460 of 460
changed rows: 0
families whose partition moved: 0
```

**Negative control**, in the same run, over a mutated copy: flipping
`descent-and-well-ordering`'s partition is detected by the same
family-partition diff (`detected: True`); mutating one already-drawn entry's
`partition` field is detected by the same per-row diff (`detected: True`).
The instrument that reports zero is the same instrument that reports a
deliberately introduced nonzero, run in the same script.

## Gates, after authoring the draw

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=500 env=2838 development=180 held-out=190 train=130` |
| `check-autogenesis-nursery.py` | 0 | both checks OK |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=206 verdict=PASS` |
| `check-holdout-adjacency.py` | 0 | 20 held-out families, 0 refused, 4 undisclosed (unchanged, advisory) |
| `check-dispatchable-frontier.py` | **0** | G7 clears: **22 dispatchable**, floor 10 |
| `validate-facts.py` | 0 | 2576 facts, 0 errors |

The 22 dispatchable facts are exactly the two pre-existing ones plus all ten
rows each of `natural-factors-and-factorisation-properties` and
`natural-logarithm-base` -- neither new held-out family's rows appear,
confirming they are correctly excluded from dispatch.

## Decision

1. Author draw 18 with the layout above in `FAMILY_MODULES`/`FAMILY_ROUTES`.
2. Record `natural-max-power-dividing`'s R11 disclosure review.
3. Do NOT use the `Factorization.PrimePow`+`Factorization.Basic`+
   `Factorization.Induction` bundle proposed by the prior commit message as a
   development/train filler in any draw that also carries
   `Factorization.LCM` held-out -- it is topically adjacent by the segment
   `Factorization` and R11 refuses it. `Factorization.PrimePow` remains
   available as a filler in a draw that does NOT carry any
   `Factorization.*` held-out family.
4. `Mathlib.Data.Nat.Factorization.Basic`/`Induction` remain unowned and
   available for a future draw.

## Consequences

`check-dispatchable-frontier.py` clears its floor: 22 dispatchable against 10.
The generalisable finding: **a status document's stated plan for the "next
lane" is a hypothesis about ONE screen (pool size), not a guarantee across
all of them (R9/R11/R12).** The prior lane measured the pool correctly (10)
and never ran the topic screen against its own proposed layout, because
authoring the draw was explicitly out of its scope. Re-screening the handed-
off plan against the real machinery, rather than transcribing it, is what
caught this before it reached a commit.
