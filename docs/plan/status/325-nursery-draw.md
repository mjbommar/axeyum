# 325 — nursery draw

<!-- plan-section: lane-status -->

## Status

LANDED. Draw 5: 60 rows across 6 families. Dispatchable **23 → 63**
against a floor of 10.

## The brief's premise was stale, and the correction matters

The task said the frontier gate was RED at 3 dispatchable. Measured on
arrival after merging local main, it was **green at 23**, exit 0,
`queue_below_floor: false`. The `321-queue-refill` handoff was written
before the ADR-0542 amendment lane landed (`6f4b1e62b`, `137451362`),
which moved `natural-logarithm` and `natural-divisibility` out of
held-out and returned their still-open siblings to the dispatchable set.

So this draw was not an emergency repair. It was still the right work:
draw 4 put rows into the population and **107 were settled within a
day**, so 23 is well under a day of headroom.

## What was drawn, and why six and not nineteen

Six is not a budget choice. The partition cycle assigns `ceil(n/3)` to
held-out, so **n=6 is the largest draw that opens only two held-out
slots**, and two is what R5 demands. n=7 opens a third, and there is not
enough held-out-safe supply for a third.

| primary module | family | partition |
| --- | --- | --- |
| `Init.Data.Int.Cooper` | integer-multiplicative-structure | held-out |
| `Init.Data.Int.Gcd` | integer-gcd-algorithm | development |
| `Init.Data.Nat.Gcd` | natural-gcd-algorithm | train |
| `Mathlib.Data.Int.LeastGreatest` | descent-and-well-ordering | held-out |
| `Mathlib.Data.Int.ModEq` | integer-congruence-lemmas | development |
| `Mathlib.Data.Nat.ModEq` | natural-congruence-lemmas | train |

## The partition assignment rule applied

Unchanged and mechanical: families sorted by the lexicographic path of
their **primary Mathlib module**, then cycled held-out / development /
train. `_with_cycle` freezes every earlier draw's family and runs the
cycle only over the new ones, so no existing family moved — asserted,
not assumed (`frozen unchanged: True`).

What a lane chooses is the family SET and each tuple's first element.
Both were chosen so the two held-out-**safe** families land at cycle
positions 0 and 3. Verified by running `assign_partitions()` before
generating anything.

On top of the mechanical rule, the discipline that decides which family
may be blind:

> A new family may go to held-out only if its mathematics is **not
> already published** by an existing development or train family. Beside
> another held-out family is fine (blind beside blind); beside a
> published one is the natural-division violation of ADR-0615.

Both held-out families were checked per module and are **R9-clean by
measurement**: 0 of the 10 selected rows in either has a declaration of
the same Mathlib name in the kernel environment.

Detail moved to [`../notes/325-nursery-draw.md`](../notes/325-nursery-draw.md).

