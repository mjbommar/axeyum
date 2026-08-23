# 239 — The training surface is 56 facts, and nothing was counting them

**Measured 2026-08-22** from `artifacts/autogenesis/nursery-v1.json` and
`artifacts/autogenesis/mathlib-nursery-split-policy-v1.json`.

## The number

The nursery holds 217 entries in 13 families. The split policy assigns a
partition per family — the unit is the whole family, deliberately, because a
family shares proof shape and splitting one leaks it. Counting only facts still
`open`:

| Partition | Open facts | Families |
|---|---:|---|
| `train` | **56** | integer-modular-equivalence 20, integer-gcd 11, natural-factorial 10, natural-fibonacci 9, integer-fibonacci 6 |
| `development` | 78 | natural-primes 21, natural-modular-equivalence 20, natural-bitwise 19, natural-gcd 18 |
| `held-out` | 57 | natural-logarithm 21, natural-binomial 20, natural-square-root 16 |

**56 is the entire surface we may build against.** The other 135 are the
measurement apparatus: development is where a producer's generalization is
checked with tuning still permitted, held-out is where it is checked once and
never again. Spending either destroys the evidence it exists to provide, which
is not a metaphor — the 2026-08-21 breach spent 19 held-out rows and cost a
whole-family amendment (ADR-0542) to repair, and `natural-gcd` had already been
moved held-out → development for the same reason.

## Why this needed writing down

Nothing in the program was tracking it. The split policy records the partitions
and `check-autogenesis-holdout-isolation.py` refuses a *breach*, but neither
answers "how much room is left", and no document in `docs/autogenesis/` had the
number until this one.

That matters because of how the 56 have been spent. From
`artifacts/autogenesis/operations.json`:

    25 registered operations
    24 cover exactly ONE fact
     1 covers a family (5 facts)

**A bespoke single-fact capsule consumes a scarce train row and yields no
transferable capability.** Twenty-four of them have consumed twenty-four rows to
produce twenty-four theorems and zero reusable producers. At that rate the
training surface supports about thirty more theorems and then the program has
nothing left to learn from — while 135 facts sit in partitions we are forbidden
to build against, and the wider Mathlib backlog behind them is unbounded.

The scarcity is not the fact count. It is that **generality can only be
*learned* on train and only *demonstrated* on development and held-out.** A
capsule learns nothing, so it converts an irreplaceable row into a single
theorem. A family producer converts one row into a schema that spends no
further rows at all.

## What follows

1. **Prefer a family producer to a capsule, and prefer widening an existing
   producer to writing a new one.** `natural-factorial` and `natural-fibonacci`
   still hold 19 open train facts between them in families where a producer
   already works — that is capability available at zero cost in new train rows.
2. **`integer-gcd` (11 open, 0 proved) is the largest untouched train block**
   after modular equivalence, and it shares the Int machinery.
3. **Every family producer should report a blind development number.** Building
   on `integer-modular-equivalence` (train) and evaluating once, untuned, on
   `natural-modular-equivalence` (development) is the paired design the split
   policy already makes available; it is the only evidence that distinguishes a
   producer from twenty capsules in a trench coat.
4. **The count belongs in a gate, not in this document.** A number in prose goes
   stale; that is the repository's most-repeated lesson. Until it is generated,
   treat the table above as measured-on-a-date, not as current.

## What this does not say

It does not say the 24 capsules were wrong. Several were the first time a shape
was closed at all, and the fib capsules established the imported-kernel route
that everything since depends on. It says the *ratio* is now the problem: the
route is established, and continuing to pay a train row per theorem is spending
the one input that cannot be replaced.
