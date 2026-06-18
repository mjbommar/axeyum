# Cardinality

> Layer 0 · foundations · decidability: `bounded` · axeyum theory: Counting / enumeration · status: `lean-horizon`

## What it is

The measure of a set's "size" via **bijections**: two sets have the same
cardinality if a bijection exists between them. Finite cardinalities are the
counting numbers; the infinite ones (ℵ₀ for the naturals, the continuum for the
reals) are where Cantor's diagonal argument and the uncountability of ℝ live.

## Role in the tour

The capstone of the foundations layer and a gateway to the "limits of
automation" lesson: countable vs. uncountable is a profound, non-computational
distinction.

## Prerequisites

- [Relations & Functions](relations-and-functions.md) — cardinality is defined by bijections.

## Unlocks

(Terminal foundations node.)

## Testable in axeyum

Only the **finite** case: that two explicit finite sets have equal size is a
bijection-existence check on a finite domain (decidable by enumeration / BV).
The pigeonhole principle for fixed sizes (no injection from an `n+1`-set into an
`n`-set) is a finite, checkable statement and overlaps with
[Counting](../02-structures/counting.md).

## Lean-horizon

The heart of the subject — countability of ℚ, **uncountability of ℝ** (Cantor),
the Schröder–Bernstein theorem, cardinal arithmetic — is inherently about
infinite sets and is a proof-reconstruction (P3.6/P3.7) target, not a benchmark.
This node is the honest face of "what automation cannot decide".

## References

- Halmos, *Naive Set Theory* (cardinality).
- Cantor's diagonal argument (uncountability of ℝ).
