# ADR-0830: Draw 9 is authored from two below-floor held-out combinations, not the two new constructions ADR-0762 called for

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0762 (draw 8, declined) measured the un-owned floor at 7 modules, all R9-contaminated or topically adjacent to a published development/train family, and concluded draw 9 needed TWO NEW KERNEL CONSTRUCTIONS before any held-out-safe family could exist; re-measured here byte-identical (env=2383, same seven modules), but a route ADR-0762 never checked -- combining several modules BELOW the `PER_FAMILY` floor, each already admissible with zero new declarations, the way draws 3/4/5 built `integer-division-boundary-cases`/`range-induction`/`integer-absolute-value` -- yields two R9/R11-clean held-out pools (`integer-elementary-identities`, 11 rows; `natural-elementary-bounds`, 12 rows) with no construction at all; combined with two already-identified dispatchable modules (`Init.Data.Nat.Bitwise.Lemmas`, `Mathlib.Data.Nat.Dist`) the draw adds 40 rows across 4 families and the dispatchable frontier goes 1 -> 21 against a floor of 10

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per-cohort and a draw is incremental), ADR-0616
(the ceiling counts attestation, not membership), ADR-0620 (held-out supply
is the scarce half of a draw), ADR-0645 (draw 6 declined), ADR-0653 (an
unblocking lane declares the construction and nothing else), ADR-0654 (draw
7 authored, the lawful family set was forced), ADR-0762 (draw 8 declined --
one constant cannot open a draw, the guard has no adjacency screen), ADR-0768
(the adjacency rule becomes R11)

## Context

`check-dispatchable-frontier.py` failed: **1 dispatchable mirror against a
floor of 10**, unchanged since ADR-0762. Re-measuring ADR-0762's own probe on
this tree reproduces it exactly: `env=2383`, the same seven un-owned modules at
the `PER_FAMILY` floor, the same three contaminated (`Mathlib.Data.Nat.Dist`
R9 2/10, `Mathlib.Data.Nat.Factorial.Basic` R9 1/10, `Mathlib.Data.Int.GCD` R9
1/10) and the same four topically adjacent to a published development/train
family (`Init.Data.Nat.Bitwise.Lemmas`, `Batteries.Data.Nat.Bitwise.Lemmas` ->
`natural-bitwise`; `Mathlib.Data.Nat.GCD.Basic` -> `natural-gcd`;
`Mathlib.Data.Nat.Choose.Basic` -> `natural-binomial`). ADR-0762 concluded from
this that draw 9 needs two new construction-only declarations (`Nat.nthRoot`
identified as clean; a second candidate, `Squarefree`, measured and rejected at
vocabulary 6/10 against `Nat.Coprime`/`Nat.Prime`/`Nat.gcd`).

`python3 scripts/propose-nursery-refill.py` reports a different, larger set of
"ready" modules (`Mathlib.Data.Nat.GCD.Basic` 44, `Mathlib.Data.Nat.Log` 37,
...). This is NOT a live disagreement with ADR-0762's measurement: that tool
applies different screens and does not exclude `HELD_OUT_CONSTRUCTIONS` or
already-owned modules the way the real generator's `select()` does --
`docs/plan/notes/383-nursery-draw-8.md` already records that "the generator is
authoritative because the generator is what draws; `propose-nursery-refill.py`
... supplies no number here." Re-deriving via the generator's own `select()`
in memory reproduces ADR-0762's seven-module, zero-held-out-safe finding
exactly.

## What ADR-0762 did not check

ADR-0762's search was for a single module individually at or above the
`PER_FAMILY` floor of 10. It did not check whether several modules BELOW that
floor -- each already admissible today, no new kernel declaration required --
combine into a held-out-safe pool the way three earlier draws already did:
draw 3's `integer-division-boundary-cases` combined two modules (7+8), draw 4's
`range-induction` combined two (8+8), and draw 4's `integer-absolute-value`
combined four. This draw runs that same search over the remaining sub-floor
supply.

Every candidate below was checked with the real `select()` + `guard()` (R1
through R11) run in memory before being written into `FAMILY_MODULES`, not by
inspection -- the same method ADR-0762 and ADR-0768 used to reproduce and then
close the guard's own gap.

## Decision

Author draw 9 as four new families: two held-out, built entirely from
below-floor modules with zero new kernel declarations, and two
development/train, using supply ADR-0762 already identified as ready.

**`integer-elementary-identities` (held-out, 11 candidate rows, 10 drawn).**
`Init.Data.Int.Basic` (6: `Int.ofNat`/`natCast` identities),
`Init.Data.Int.Compare` (1: a strict-order trichotomy),
`Init.Data.Int.Linear` (2: `omega`-adjacent not-le/not-lt rewrites),
`Mathlib.Data.Int.DivMod` (2: `emod`/`ediv` identities). Every constant
`CONST_RE` extracts from these eleven statements is typeclass/operator
PLUMBING under `check-holdout-adjacency.py`'s own `is_syntax` filter
(`Int.ofNat`, `LE.le`, `HMod.hMod`, `HDiv.hDiv`, ... -- explicitly listed in
`SYNTAX_NAMES` or matched by a `SYNTAX_PATTERNS` regex), so `subject_constants`
is EMPTY for this family and both the `topic` and `vocabulary` R11 signals are
vacuously clean -- not narrowly clean, structurally unable to fire. It also
sits "blind beside blind": the natCast rows are the same mathematics as the
EXISTING held-out `integer-natcast` (draw 2), and the DivMod rows are the same
mathematics as the existing held-out `integer-division` /
`integer-division-boundary-cases` (draw 1/3) -- the precedent draw 2 and draw 5
both already used, not a new judgment call.

**`natural-elementary-bounds` (held-out, 12 candidate rows, 10 drawn).** Ten
small leftover Nat modules, none individually near the floor, each a basic
order/bound/successor/digit identity that no existing family's topic or
vocabulary reaches: `Mathlib.Data.Nat.SuccPred` (2),
`Batteries.Data.Nat.Lemmas` (2), `Mathlib.Data.Nat.Basic` (1),
`Mathlib.Data.Nat.Order.Lemmas` (1), `Init.SimpLemmas` (1),
`Init.Data.Nat.Simproc` (1), `Mathlib.Algebra.Order.Group.Nat` (1),
`Mathlib.Order.Monotone.Basic` (1), `Mathlib.Data.Nat.Sqrt` (1 -- the single
row `HELD_OUT_CONSTRUCTIONS` does not exclude, about squeezing a value between
consecutive squares rather than about `Nat.sqrt` itself), and
`Mathlib.Data.Nat.Digits.Defs` (1). `select()` keeps the alphabetically-first
ten of the twelve.

**This one is honestly a grab-bag, not one clean subject**, unlike
`integer-absolute-value`'s four modules (all about `natAbs`). The remaining
un-owned supply below the floor is this thin -- matching ADR-0762's own count
of the residual un-owned modules -- and no single coherent theme covers ten
rows without either reaching into a contaminated/adjacent module or a new
construction. `Init.Core`'s single survivor, `Nat.add_zero`, was deliberately
EXCLUDED from this pool: it is already `IN-ENV` (R9-contaminated), the one
leftover row this draw could not spend on held-out.

**`natural-bitwise-basics` (development, `Init.Data.Nat.Bitwise.Lemmas`, 33
candidate rows, R9 0/10)** and **`natural-distance` (train,
`Mathlib.Data.Nat.Dist`, 18 candidate rows, R9 2/10 on `dist_comm`/
`dist_self`, harmless outside held-out)** fill the two dispatchable slots.
Both duplicate an existing v1 development/train family's TOPIC
(`natural-bitwise`; Dist is `natural-distance`'s own namesake in ADR-0653's
prose) -- accepted for the reason draw 7 accepted `natural-prime-arithmetic`/
`natural-prime-characterizations` beside v1 `natural-primes`: contamination in
a PUBLISHED partition is a fast-closure feature, not the ADR-0542 leak, which
only threatens blind rows. `Mathlib.Data.Nat.Dist` is exactly the module
ADR-0653's closing line named as "real supply for development or train" once a
draw's cycle positions allow it -- this is the draw where they do.

## Verification, not inspection

Both held-out pools were run through the real `select()` + `guard()` in
memory before being written into `FAMILY_MODULES`:

    GUARD PASSED
    integer-elementary-identities   partition=held-out    n=10  (0 IN-ENV)
    natural-bitwise-basics          partition=development n=10
    natural-distance                partition=train        n=10  (2 IN-ENV, harmless -- not held-out)
    natural-elementary-bounds       partition=held-out     n=10  (0 IN-ENV)

`scripts/check-holdout-adjacency.py` (R11), which every guard call already
imports, additionally confirms both new held-out families standalone:

    clean   draw9  integer-elementary-identities   topic=0  vocab=0/10  env=[]  -
    clean   draw9  natural-elementary-bounds       topic=0  vocab=0/10  env=[]  -

Neither carries an `environment` sweep hit, so neither needs an entry in
`holdout-adjacency-review-v1.json` -- the disclosure requirement only fires
when the sweep is non-empty.

**PRIMARY-MODULE ORDERING IS CHOSEN, as in every prior draw.** The four
primaries sort `Init.Data.Int.Basic` < `Init.Data.Nat.Bitwise.Lemmas` <
`Mathlib.Data.Nat.Dist` < `Mathlib.Data.Nat.SuccPred`, so the mechanical
held-out/development/train/held-out cycle (`PARTITION_CYCLE`, restarting at
`held-out` for this draw's four new families) lands exactly the 2-held-out /
2-dispatchable split R4/R5 require. No target outcome was consulted; the SET
and each tuple's primary module are a lane's judgment under measured
scarcity, and the partition assignment itself is the mechanical rule the
generator already enforces (R6/R10).

## Gates

| check | result |
| --- | --- |
| `gen-autogenesis-nursery-refill.py --check` (post-regen) | exit 0, `entries=340\|development=130\|held-out=120\|train=90` |
| `check-dispatchable-frontier.py` | exit 0, dispatchable set non-empty, floor cleared (1 -> 21) |
| `check-autogenesis-holdout-isolation.py` | `held_out=136 files_scanned=1110 settled=0 references=0 PASS` |
| `check-holdout-adjacency.py` (standalone) | exit 0, 13 held-out families, 0 refused |
| `validate-facts.py` | `2314 facts checked, 0 errors` |
| `check-merge-hygiene.sh` | `PASS` |
| `check-autogenesis-nursery.py` | **exit 1, pre-existing, unrelated to this draw -- see below** |

`check-autogenesis-nursery.py`'s "declared dependency component crosses
evaluation partitions" failure was reproduced against `HEAD`'s own
`nursery-v2-extension.json` (this draw's file swapped out and back in the same
session, `git diff --stat` confirmed byte-identical to this draw's version
afterward): **exit 1, identical error, with none of this draw's entries
present.** The three leaking components (sizes 206, 4, 3) are entirely
pre-existing `F:ml430-int-modeq-*` / `F:ml430-nat-div-gcd-*` /
`F:ml430-int-add-*` facts whose `depends_on` edges were committed on
2026-08-29/30, well before this session, and none references any family this
draw touches. This draw's 40 new entries carry `depends_on: []` (the
generator's standing convention) and are graph-isolated, so they cannot
possibly join or create a leaking component; the failure is byte-for-byte the
same with or without this draw's rows. Recorded here rather than repaired,
because `artifacts/facts/` outside this draw's 40 new files is not this
lane's path, matching ADR-0762's own precedent for an unrelated red gate found
mid-draw.

## Consequences

- `check-dispatchable-frontier.py` clears its floor: **21 dispatchable rows**
  against a floor of 10 (`natural-bitwise-basics`'s 10 + `natural-distance`'s
  10 + the 1 pre-existing `fermat-numbers` survivor).
- Held-out breadth is restored to **13 families** (11 standing + the 2 new
  ones here), reversing three drawn-down draws' worth of held-out attrition.
- **The remaining un-owned, below-floor, non-adjacent supply is now close to
  exhausted.** `Init.Core`'s one contaminated row aside, essentially every
  small leftover module that was safe for held-out went into
  `natural-elementary-bounds` this draw. A future draw will very likely need
  either ADR-0762's original route (new construction-only declarations) or a
  genuinely new source of un-owned modules (a fresh Mathlib area this
  inventory has not screened at all).
- `check-autogenesis-nursery.py`'s pre-existing dependency-partition leak is
  logged, not fixed, and will still be red for the next lane that runs the
  full gate suite. It is unrelated to draw 9 and should be triaged
  separately, against the `F:ml430-int-modeq-*`/`F:ml430-nat-div-gcd-*`
  `depends_on` edges that created it on 2026-08-29/30.
