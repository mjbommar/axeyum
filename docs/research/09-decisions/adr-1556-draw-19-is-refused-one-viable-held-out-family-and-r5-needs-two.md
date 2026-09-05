# ADR-1556: Draw 19 is refused — exactly one viable held-out family exists, and R5 needs two

Status: accepted
Date: 2026-09-02
Lane: `nursery-draw-19b`

Index-summary: The retry of draw 19 (ADR-1546 refused it on red partition
gates; ADR-1550 and ADR-1551 have since settled those) is refused for a
different and structural reason, measured exhaustively against the real
screens. Over the 23 unowned Mathlib modules that still carry a screened
candidate (79 rows), **861,809 module subsets reach the ten-row floor, they
produce 40,668 DISTINCT drawn tens, and exactly 4 survive every held-out
screen** (3 after this ADR's own refusal row lands) — and all of them draw rows
from the same four modules
(`Mathlib.Data.Nat.Factorization.Basic`, `Mathlib.NumberTheory.PythagoreanTriples`,
`Mathlib.NumberTheory.SumTwoSquares`, `Mathlib.Tactic.IntervalCases`). A module
belongs to exactly one family, so **at most one held-out family can exist at a
time and R5 demands two: 0 disjoint pairs.** This reproduces ADR-1420's finding
for draw 17 on a tree four families later, with the blocking core grown from
one module to four. Two further measurements: the blindness screen draw 17
lacked (rebuilt `shape_search`, statement-shape queries, `git log -S`) finds
that `Int.gcd_eq_natAbs` — a row in one of the four viable tens — is **`rfl` in
this kernel**, because `Int.gcd` IS defined as `Nat.gcd (natAbs a) (natAbs b)`
(`int_prelude/gcd.rs:declare_gcd`); a `do-not-draw-held-out` row is recorded for
its module. And the draw-10 judgement that `Mathlib.NumberTheory.{SumTwoSquares,
PythagoreanTriples}` are "deliberately NOT taken" for held-out lives in a
generator COMMENT and is enforced by nothing — the ADR-1450 shape recurring, on
two modules that are in every viable ten today.

Index-status: accepted

## Context

Draw 19 was refused on 2026-09-02 by lane `nursery-draw-19` (ADR-1546) because
two partition gates were red. Since then:

- **ADR-1550** took option 2 — the crossing `depends_on` EDGE is the unit, 198
  baselined, the baseline may only shrink, wired into `hooks/pre-push` and merge
  hygiene.
- **ADR-1551** measured option 1 and REFUSED it: the family graph is one
  44-family / 520-row blob and `depends_on` is proof-derived, so partitioning on
  it makes a row's partition a function of whether we proved it.
- Lane `baseline-holdout-leak` digested the held-out endpoints out of ADR-1550's
  baseline artifact, returning `check-autogenesis-holdout-isolation.py` to
  green.

So the standing rule "no draw on a red partition gate" could not be applied as
written: ADR-1551 established that the two component gates' property cannot be
restored by re-partitioning, so waiting for them is waiting forever.

## Decision — the rule this draw applied, and why

**Every gate that measures something a draw can contaminate had to be green;
the two component gates are reported before and after and must not worsen.**

A draw writes new manifest rows with `partition` assigned by the module-path
cycle and `depends_on: []`. What it can contaminate is therefore: the isolation
of held-out ids (`check-autogenesis-holdout-isolation.py`), the adjacency of a
new held-out family to published mathematics (`check-holdout-adjacency.py`), the
frozen drawn-tens of earlier draws (`check-draw7-frozen-families.py`), the
partition-crossing edge set (`check-partition-edges.py --baseline`), and the
generator's own reproduction (`gen-autogenesis-nursery-refill.py --check`). All
five were green at start and are green at the end.

What a draw canNOT contaminate is the two component gates
(`check-autogenesis-nursery.py`, `check-development-partition.py`): both read
`depends_on` edges, a fresh row has none, and ADR-1551 measured that 204 of the
221 open drawn rows sit in no dependency component at all. Their counts are
recorded before and after and are identical, because nothing this lane did
touches what they read.

**Draw 19 is refused.** No family was added to `FAMILY_MODULES`, no manifest row
was written, no partition was assigned, no held-out outcome was named, nothing
was dispatched. `artifacts/autogenesis/nursery-v2-extension.json` is unchanged
at 500 entries.

## The measurement

`docs/research/09-decisions/adr-1556-draw-19-screen.py`, which loads
`gen-autogenesis-nursery-refill.py` and `check-holdout-adjacency.py` by path and
runs the ACTUAL `admissible()` / `blockers_for()` / `screen_family()` /
`barred_modules()` / `is_closed_evaluation`. `propose-nursery-refill.py` is not
used as a candidate space; it screens by module only and has neither the
fact-ledger nor the `HELD_OUT_CONSTRUCTIONS` nor the R5 screen.

```
# before this ADR's refusal row
ADR_1556_DRAW_19_SCREEN|env=2838|unowned_modules=23|unowned_rows=79
                       |distinct_tens=40668|viable=4|disjoint_pairs=0|failures=0
# after it (the `Int.gcd_eq_natAbs` ten is gone; the answer does not move)
ADR_1556_DRAW_19_SCREEN|env=2838|unowned_modules=23|unowned_rows=79
                       |distinct_tens=40668|viable=3|disjoint_pairs=0|failures=0
```

**The unowned pool, after draw 18 consumed four families.** 23 modules carry a
screened, unused candidate; 79 rows in total, and **22 of the 79 are
`Mathlib.Data.Nat.Count`**, barred for held-out by ADR-1450. `PER_FAMILY` is 10,
so a four-family draw needs 40 of those 79 rows in four module-disjoint,
topically coherent bundles.

**Dedup is by DRAWN TEN, and that correction is load-bearing.** The obvious
enumeration keeps only minimal covers — module sets from which no module can be
dropped while still reaching ten. That is wrong in general: a superset does not
draw the same ten, because an added module's names can sort earlier. Both passes
are run and both are reported (11,386 minimal-cover tens; 40,668 exact), and the
screen asserts they agree on the viable count. Here they do; the assertion is
there because next time they might not.

**The viable held-out tens.** Every one is vocabulary 5 of 10 — exactly at
`VOCABULARY_MAX_ROWS`, the allowance, not comfortably inside it — with an empty
environment sweep, and every one contains:

| module | rows it contributes |
| --- | ---: |
| `Mathlib.Data.Nat.Factorization.Basic` | 5 |
| `Mathlib.Tactic.IntervalCases` | 2 |
| `Mathlib.NumberTheory.PythagoreanTriples` | 1 |
| `Mathlib.NumberTheory.SumTwoSquares` | 1 |

They differ only in which single row fills the tenth slot: `Int.gcd_eq_natAbs`
(now barred, below), `Nat.prime_composite_induction`, `Nat.ModEq.pow_totient` or
`Nat.exists_prime_gt_modEq_one`. **A module belongs to exactly one family**
(`select()`'s `module_family` map is flat), so no two of them can be drawn in
the same draw: **0 disjoint pairs**, and R5 needs one.

**This is ADR-1420's finding, four families later and wider.** ADR-1420 measured
the same structure for draw 17 — "modules present in EVERY viable subset:
`['Mathlib.Tactic.IntervalCases']` … at most one viable held-out family can
exist at a time". The blocking core is now **four** modules rather than one, and
`Mathlib.Tactic.IntervalCases` is still in it: its
`Int.add_one_le_of_not_le` and `Int.le_sub_one_of_not_le` are vocabulary-clean
and sort alphabetically ahead of nearly everything else in the pool, so they
enter every drawn ten.

**What a SECOND held-out family would need, measured rather than guessed.** Over
the 19 modules disjoint from that core (70 rows), **11,030 distinct drawn tens
exist and zero are viable.** The refusal signatures:

| failing signals | tens |
| --- | ---: |
| topic + vocabulary | 2,872 |
| topic + vocabulary + R9 | 2,686 |
| barred + topic + vocabulary (± R9) | 4,542 |
| barred + topic (± R9) | 462 |
| topic + R9 | 211 |
| barred + vocabulary (± R9) | 89 |
| topic only | 64 |
| vocabulary + R9 | 57 |
| vocabulary only | 17 |
| barred + R9 | 15 |
| **barred only** | **15** |

The 15 that fail on `barred` ALONE are all `Mathlib.Data.Nat.Count` tens, and
the nearest ten failing on `topic` alone is bitwise + gcd
(`Bitwise` is `natural-bitwise-basics`', `Gcd` is `integer-gcd-algorithm`', both
development). So the unblock is exactly one of two things, and only one of them
is real:

1. **Overturn ADR-1450's `Mathlib.Data.Nat.Count` bar.** Not available: ADR-1450
   measured that `Nat.count` is a definitional alias of `Nat.countRange` and
   that four of the drawn ten are already proved here term-for-term. The bar is
   right.
2. **ADR-1420 Route 1 again** — declare a construction opening one new
   held-out-safe module, disjoint from the four above, and topic-, vocabulary-
   and R9-clean. This is what draw 18 did (`Nat.factorizationLCMLeft`/`Right`
   opened `Mathlib.Data.Nat.Factorization.LCM`), and it is what draw 19 needs.

**The control.** A search that finds no disjoint pair is worth nothing until it
is shown it can find one. Lifting ADR-1450's `Count` bar — the only signal that
refuses those 15 tens — takes the search from 3 viable tens / 0 pairs to **35
viable tens / 20 disjoint pairs** (before this ADR's own refusal row, 4 → 64
viable and 46 pairs). The first draft of the control cloned the
blocking modules into independent copies instead, and it did **not** fire: a
clone carries the same row names, the dedup key IS the drawn ten, so the clone's
ten collapses onto the original's and no pair can ever appear. It reported 418
viable tens and 0 pairs, which reads exactly like the real finding. That is
recorded because it is the failure mode this repository names as worse than no
check at all, and it was one line away from being the evidence.

## The blindness screen draw 17 lacked

Every candidate row was screened for a theorem of the same SHAPE already in this
kernel, under any name — the screen ADR-1450 was faulted for not running.
`shape_search` was rebuilt through `scripts/cargo-serialized.sh`
(`cargo build --release -p axeyum-lean-kernel --example shape_search`) and its
freshness confirmed against a control that landed the same day:
`--name Rat.rowEchelon --kind definition --expect 1` returns `FOUND 1`
(`Rat.rowEchelon` was declared at 10:50 by `cd8d1f4a7`). Index: 2,121
declarations over `logic,nat,axreal,integer,ipc,rat,characterization,string`.

**Finding: `Int.gcd_eq_natAbs` is not a blind proposition here — it is `rfl`.**
Mathlib's statement is `a.gcd b = a.natAbs.gcd b.natAbs`.
`crates/axeyum-lean-kernel/src/int_prelude/gcd.rs:declare_gcd` builds exactly
that term as `Int.gcd`'s VALUE — `NatOps::gcd(d, natAbs a, natAbs b)`,
`ReducibilityHint::Regular(6)` — and three separate in-tree proofs
(`dvd_gcd_mirrors.rs:228`, `gcd_scaled_mirrors.rs:35`, `:240`) already discharge
steps "by `Int.gcd`'s own definition". This is ADR-1450's `Nat.count` /
`Nat.countRange` failure mode on a new row, and neither R9 (which compares
names, and the names differ) nor R11's vocabulary map (which holds only nursery
family subjects, never kernel development) can see it. **A
`do-not-draw-held-out` row for `Mathlib.Algebra.GCDMonoid.Nat` is recorded in
`artifacts/autogenesis/holdout-adjacency-review-v1.json`**, where
`assert_draw_lawful` reads it.

**Every other candidate row screened clean, and three of the queries had to be
<!-- absent: Nat.Prime, Nat.Coprime -->
<!-- was-absent: Nat.ModEq -- spelling-normalizes to the kernel's lowercase `Nat.modEq`, cited two lines below as the existing spelling; not a landing event, a naming-convention mismatch -->
re-asked.** `--concl Nat.Prime`, `--concl Nat.Coprime`, `--concl Nat.ModEq` and
`--concl Ne` all returned **UNANSWERABLE (exit 3)**, not absent: this kernel has
no such declarations — primality is spelled as an `And`, coprimality as
`Nat.gcd a b = 1`, congruence as `Nat.modEq`, and `Ne` is not a declaration
here. Re-asked in the kernel's own vocabulary:

| candidate row | shape query | result |
| --- | --- | --- |
| `Nat.ModEq.pow_totient` (Euler) | `--concl Nat.modEq --const Nat.totient` | ABSENT, control `ns Nat=1066`; the 19 `Nat.totient` theorems are multiplicativity/parity/divisibility, none a congruence |
| `Nat.exists_eq_two_pow_mul_odd` | `--ns Nat --concl Exists --const Nat.Odd` | ABSENT, control `ns Exists=3 Nat=1066`; nearest is `Nat.dvd_two_pow_classify`, a different proposition |
| `Nat.exists_prime_gt_modEq_one` | `--concl Exists --const Nat.modEq` | ABSENT; `Nat.exists_prime_gt` (Euclid) exists and is strictly weaker |
| `Nat.dvd_iff_prime_pow_dvd_dvd` | `--ns Nat --concl Iff --const Nat.dvd` | 14 matches, none this statement; `--name-like dvd_iff_prime` ABSENT |
| `Nat.prime_composite_induction` | `--name-like composite`, `--name-like strong` | ABSENT both; `Nat.base_induction` and `Nat.exists_prime_factorization` are different |
| `Int.add_one_le_of_not_le`, `Int.le_sub_one_of_not_le` | `--ns Int --concl Int.le --hyp Not`, `--ns Int --name-contains not_le` | ABSENT; the kernel has `Int.le_of_lt` and `Int.lt_of_le_of_ne` but no `¬≤ → +1 ≤` bridge |
| `Int.sq_ne_two_mod_four`, `Nat.sq_add_sq_mul`, the three `exists_eq_pow_*` | shape and `--name-like` | ABSENT |

`git log -S` over `crates/`, with `--diff-merges=first-parent --no-patch`
because a plain pickaxe skips merge commits (lane `partition-edge-gate`, 198
edges, 7 unattributable without it): **no commit introduces any of the thirteen
Mathlib names into `crates/`**, and none appears in the tracked tree except in
prior refusal documents. So no theorem predates this draw under its Mathlib
name; the one predating theorem is `Int.gcd_eq_natAbs`, and it predates it as a
definition rather than as a theorem, which is why only a shape query finds it.

## The finding that outlasts the refusal

**A recorded do-not-draw-held-out judgement about two of the four blocking
modules is enforced by nothing.** `gen-autogenesis-nursery-refill.py`, in the
draw-10 block, states:

> `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` were available and
> are deliberately NOT taken: `Int.sq_ne_two_mod_four` is mod-4 arithmetic,
> adjacent to the TRAIN family `integer-modular-equivalence`, and it is not
> worth a mild leak to buy slack.

It is restated in ADR-0645 and in `docs/plan/status/325-nursery-draw.md`. It is
**not** a row in `holdout-adjacency-review-v1.json`, so `barred_modules` cannot
reach it, and both modules are in all four of today's viable held-out tens —
they are precisely what makes the one surviving family survive. This is the
ADR-1450 shape exactly: a verdict on record that no guard reads.

It is deliberately **not** converted into a bar by this lane. The generator's
wording is a preference ("not worth a mild leak"), not a finding of
non-blindness, and promoting one lane's judgement into an enforced invariant is
a different decision from recording it. The `Int.gcd_eq_natAbs` row above IS
recorded, because that one is a measured mirror rather than a preference. What
the next lane needs to decide, in its own ADR, is whether the draw-10 preference
binds — and it now matters, because those two modules are load-bearing for the
only held-out family the pool can build.

## Consequences

- `check-dispatchable-frontier.py` stays **red at 2 dispatchable against a floor
  of 10**. That red is the condition a draw repairs and is not a contamination;
  it cannot be repaired from today's pool.
- The next lane is a CONSTRUCTION lane, not a draw lane: ADR-1420 Route 1, one
  held-out-safe module disjoint from `{Factorization.Basic, PythagoreanTriples,
  SumTwoSquares, IntervalCases}`, topic-, vocabulary- and R9-clean.
- `adr-1556-draw-19-screen.py` exits **0 while the refusal holds and 1 when a
  disjoint pair appears**, so the refusal is checkable and expires by itself. It
  is not a registered gate: like the generator, it reads the pinned statement
  inventory under `/nas3`, which is not on every fleet host.
