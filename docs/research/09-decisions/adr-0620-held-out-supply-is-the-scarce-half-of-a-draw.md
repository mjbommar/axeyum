# ADR-0620: Held-out supply is the scarce half of a draw

Status: accepted
Date: 2026-08-30
Index-summary: A draw is gated by held-out-SAFE supply, not by pool size; 2,235 survivors buy unlimited dispatchable rows and only ~4 more blind ones, so R5's two-new-held-out-families rule is about to become unsatisfiable and must not be met by contaminating the blind set

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per-cohort and a draw is incremental), ADR-0616
(the ceiling counts attestation), ADR-0619 (the queue refills from the
kernel, not from the bridge)

## Context

Draw 5 (2026-08-30) added 60 rows across six families and took the
dispatchable queue from 23 to 63 against a floor of 10. Authoring it
surfaced a structural fact about the pool that none of the four previous
draws had to state, because none of them was close enough to the boundary
to see it.

The received framing, stated in ADR-0619 and in the proposer's own output,
is that the pool is large: **2,295 screened survivors across 94 modules, 19
ready families, a draw of all 19 would add 120 dispatchable rows.** Every
number there is correct. The framing it invites — that a draw is limited by
how much of the pool a lane is willing to take — is wrong.

A draw has two halves and they draw on completely different supplies.

## Decision

**Treat held-out-safe supply as the binding constraint on a draw, and
record it as a measured quantity rather than inferring it from the survivor
count.** When the two halves conflict, the draw shrinks. R5 is never
satisfied by placing a family over already-published mathematics into
held-out.

## What was measured

Three separate screens stand between "survivor" and "drawable into
held-out", and only the first is visible in the proposer's output.

**1. A module belongs to exactly one family.** `select`'s `module_family`
is a flat dict comprehension over `FAMILY_MODULES`, so a module an earlier
draw claimed cannot supply a new family; listing it twice silently
reassigns its candidates instead of adding any. `Init.Data.Int.DivMod.Lemmas`
alone still holds **193 unused screened survivors** and every one is
unreachable, because `integer-division` owns that module. Across the census,
a large majority of surviving supply sits in modules that are already owned.
So the survivor count is an upper bound on drawable rows and not a close one.

**2. The generator applies a screen the proposer does not.**
`HELD_OUT_CONSTRUCTIONS` drops any candidate mentioning `Nat.log`,
`Nat.clog`, `Nat.log2` or `Nat.sqrt`. `Mathlib.Data.Nat.Log` (34) and
`Mathlib.Data.Nat.Sqrt` (24) therefore appear in the proposer's ready list
and yield **zero** candidates in the generator. Post-draw-5 the ready set
reads 15 and the drawable set is 13. Anyone sizing a draw from the
proposer's list alone will over-count by two families.

**3. Every remaining large module is over already-published mathematics.**
This is the one that binds. Of the 17 drawable ready families before
draw 5, all 17 were gcd, ModEq, Prime, factorial, choose, bitwise, fib or
Int basics — each sitting over the same mathematics as an existing
development or train family. Draws 2, 3 and 4 each excluded exactly this
list from held-out, and the reason has not changed: a blind family over
published mathematics is the natural-division violation ADR-0615 records.
They remain perfectly good for development and train, where nothing is
blind, and draw 5 put all four of its dispatchable families there.

Consequently both held-out slots had to be built from **un-owned modules
below the 10-candidate floor with no development or train adjacency**,
combined the way draws 3 and 4 combined theirs. The entire supply meeting
that description is **24 propositions across eight modules**:

| module | n | adjacency |
| --- | --- | --- |
| `Mathlib.Algebra.Group.Int.Units` | 7 | none — no family names Int units |
| `Mathlib.Order.Interval.Finset.Nat` | 4 | `natural-induction-and-divisibility`, `range-induction` — both held-out |
| `Mathlib.NumberTheory.SumFourSquares` | 4 | none |
| `Init.Data.Int.Cooper` | 3 | `integer-division` and two siblings — all held-out |
| `Mathlib.Data.Int.LeastGreatest` | 2 | none |
| `Mathlib.Data.Int.DivMod` | 2 | `integer-division` — held-out |
| `Mathlib.NumberTheory.SumTwoSquares` | 1 | none |
| `Mathlib.NumberTheory.PythagoreanTriples` | 1 | `integer-modular-equivalence` — **train** |

Draw 5 took 20 of those 24. **About four remain, and one of them carries a
train adjacency.** R5 requires two new held-out families of ten rows each.
Draw 6 cannot satisfy it from un-owned modules at all.

## The consequence, stated so it is not worked around

R5 exists because blind breadth is the other half of a refill and it is
genuinely scarce. The correct response when it becomes unsatisfiable is
**not**:

- to lower R5 so a draw passes;
- to place a gcd/ModEq/Prime family into held-out because nothing else is
  left. That is the violation, and it is worse than a small queue: it
  manufactures an evaluation population whose answers are already
  published, which is the checker-that-cannot-fail defect relocated into
  the measurement the whole nursery exists to produce.

The honest routes, in order of preference:

1. **Declare the blocking constants.** ADR-0619's finding applies here
   verbatim and is now sharper: pool growth comes from declaring kernel
   constants, not from widening the screen. `instSubNat` alone is the sole
   blocker of 292 rows. New constants open new *modules*, and a module with
   no existing family is exactly what a held-out slot needs. This is
   ordinary proof work, which is the point.
2. **Free an owned module.** A family whose rows are all settled has spent
   its module's evaluation value; there is no rule today that releases the
   remaining survivors in it back to the pool, and there could be. That
   would reach the 193 rows in `Init.Data.Int.DivMod.Lemmas` and their
   equivalents — but only into held-out beside an already-held-out sibling,
   never into a partition that publishes them.
3. **Accept a draw with no new held-out family, deliberately and on the
   record.** If blind breadth genuinely cannot grow, a dispatchable-only
   draw is honest as long as it is labelled as one and R5 is amended by an
   ADR that says the blind population is frozen at its current size, rather
   than quietly relaxed to let a draw through.

What must not happen is the fourth route: a draw that meets R5 on paper by
choosing whichever family looked least obviously published. The adjacency
argument has to be made per module and written down, as draws 2 through 5
each did.

## Consequences

- `gen-autogenesis-nursery-refill.py` carries the census and the reasoning
  in the draw-5 block, including the two modules deliberately declined
  (`SumTwoSquares`, `PythagoreanTriples`) to avoid a mild train adjacency.
- `HELD_OUT_CONSTRUCTIONS` keeps `Nat.log`/`Nat.clog`/`Nat.log2` even
  though `natural-logarithm` was amended out of held-out on 2026-08-30.
  Dropping them unlocks 34 candidates and is a decision for a draw that
  wants them, not a side effect of an unrelated one. Keeping them
  over-excludes, which is the safe direction. `Nat.sqrt` is still live:
  `natural-square-root` is the only surviving v1 held-out family.
- The next lane to author a draw should read the drawable ready set (13),
  not the proposer's ready set (15), and should check the held-out-safe
  table above before sizing anything.
