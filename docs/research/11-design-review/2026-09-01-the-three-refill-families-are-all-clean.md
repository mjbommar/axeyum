# All three refill candidate families screened clean — the draw is authorable

> **CORRECTED 2026-09-01, same day, by the tooling fix this document's own
> closing section called for.** The contamination screen below is right and
> unchanged. The AVAILABILITY table is wrong: once `propose-nursery-refill.py`
> applies both missing screens, **`Mathlib.Data.Nat.Bitwise` falls below the
> ten-survivor threshold and drops out of the ready list entirely.**
>
> | family | this note said | measured with both screens |
> | --- | --- | --- |
> | `Mathlib.Data.Nat.Log` | 17 | **17** |
> | `Mathlib.Data.Nat.Bitwise` | 18 | **below threshold — not ready** |
> | `Mathlib.NumberTheory.FactorisationProperties` | 15 | **15** |
>
> Re-run, both fixes applied: `already-drawn` screened out rises 380 -> 662, a
> new `held-out-construction` category appears at 14, survivors fall 2260 ->
> 2056, and **READY FAMILIES is 2, not 3.**
>
> **A draw needs two families and exactly two remain, yielding exactly 10
> against a floor of 10.** `dispatchable_yield(n) = 10·(n − ⌈n/3⌉)`, so one
> family yields **zero** — `Nat.Log` could never have cleared the floor alone,
> before or after the correction. There is no slack: anything that reduces
> either family below ten blocks the draw.
>
> `Mathlib.NumberTheory.FactorisationProperties` is still **unscreened for R9
> contamination and R11 adjacency**, which is the screen that has historically
> rejected most candidates (draw 10 was DECLINED against a shortlist of this
> kind, ADR-0900). Treat "two families available" as a shortlist, not a draw.
>
> One further correction to the section below: it states that dropping the
> three `log` constants from `HELD_OUT_CONSTRUCTIONS` is sound. **Dropping
> `Nat.log2` is NOT** — it displaces `Nat.not_exists_sq` from the already-drawn
> held-out family `natural-elementary-bounds`, a retroactive alteration of a
> blind population. Only `Nat.log` and `Nat.clog` were dropped, verified by a
> zero-diff over all 460 already-drawn rows.

Follow-on to
[`2026-09-01-the-ml430-queue-empties-this-round.md`](2026-09-01-the-ml430-queue-empties-this-round.md),
which recorded that two of the three candidates were **contamination-exposed**
by a lane still running, and that a draw had to wait for it. That lane
(`nat-size-squarefree`) has returned. **All three are clean.** Measured
2026-09-01.

| family | open | verdict |
| --- | --- | --- |
| `Mathlib.Data.Nat.Log` | 17 | clean; blocked on a separate code decision, below |
| `Mathlib.Data.Nat.Bitwise` | 18 | **clean** |
| `Mathlib.NumberTheory.FactorisationProperties` | 15 | **clean, deliberately** |

A draw needs two families. Three are available.

## Why Bitwise survived

The lane landed `Nat.size_bit` and `Nat.size_le_size` — both **exact Mathlib
mirror names**, which is the ADR-0653 contamination shape. They do not
contaminate `Bitwise`, because Mathlib declares both in
`Mathlib/Data/Nat/Size.lean`, not `Mathlib/Data/Nat/Bitwise.lean`:

```
/usr/bin/grep -rln "theorem size_bit\b|theorem size_le_size\b" $M/Mathlib/
  -> Mathlib/Data/Nat/Size.lean          (only)
/usr/bin/grep -cE "size_bit|size_le_size" $M/Mathlib/Data/Nat/Bitwise.lean
  -> 0
/usr/bin/grep -c "theorem" $M/Mathlib/Data/Nat/Bitwise.lean
  -> 27                                   (positive control)
```

The positive control matters: a `0` from the second query alone is
indistinguishable from a wrong query.

## Why FactorisationProperties survived — and it is the model

`crates/axeyum-lean-kernel/src/nat_prelude/abundant_deficient.rs` declares
`Nat.Abundant` and `Nat.Deficient`, squarely inside this Mathlib module's
subject. It does **not** contaminate the family, because it declares the two
definitions and their evaluation test and **nothing else**. Its module doc says
so, under a heading `## No theorems`, and cites ADR-0653 and the `Nat.dist`
incident by name.

That is the ADR-0653 rule followed correctly and *documented at the site where
the next lane will read it* — not in an ADR the next lane would have to know to
look for. It is the pattern to copy when unblocking any future family.

The same file also applies the mirror-flip criterion to itself: its
definitional body is *provably equivalent to* and **not definitionally
identical with** Mathlib's, so the corresponding mirror "therefore stays
`open`". A lane wrote that down rather than flipping something convenient.

## What still blocks `Nat.Log`, and it is not contamination

`gen-autogenesis-nursery-refill.py:158` carries
`HELD_OUT_CONSTRUCTIONS = {"Nat.log", "Nat.clog", "Nat.log2", "Nat.sqrt"}`,
applied at `:1318`. The comment above it is explicit that **the proposer does
not apply this screen and the generator does**, so `Mathlib.Data.Nat.Log`
appears in `propose-nursery-refill.py`'s ready families and yields ZERO
candidates in the generator.

Dropping the three `log` constants is sound — `natural-logarithm` was amended
out of held-out on 2026-08-30 under ADR-0542 — and the comment pre-authorises
it as "a decision for a draw that wants them and not a side effect of an
unrelated draw". **`Nat.sqrt` must stay**: `natural-square-root` is the only
surviving v1 held-out family.

## Two independent blind spots in the proposer

Both **overstate** headroom, which is the dangerous direction — a draw authored
from either can fail to clear the frontier floor after the fact.

1. `used_source_names()` never reads the fact ledger. Measured: it counted 37
   unused candidates for `Mathlib.Data.Nat.Log`, of which **20 are already
   `proved` facts** (verified independently: 20 `F-ml430-nat-{log,clog,log2}-*`
   files, 20 `proved`, 0 not-proved). True open: 17.
2. It never applies `HELD_OUT_CONSTRUCTIONS`, as the generator's own comment
   states.

A reader who learns about one will assume it was the only one.
