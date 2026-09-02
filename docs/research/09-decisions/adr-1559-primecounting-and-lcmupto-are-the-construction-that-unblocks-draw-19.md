# ADR-1559: `Nat.primeCounting` and `Nat.lcmUpto` are the construction that unblocks draw 19

Status: accepted
Date: 2026-09-02
Lane: `heldout-construction-1`

Index-summary: ADR-1556 refused draw 19 on a measurement — 3 viable held-out
families over 40,668 distinct drawn tens, all drawing from the same four
modules, so R5's two module-disjoint held-out families are unsatisfiable — and
named ADR-1420 Route 1 as the unblock: a construction lane declaring one
held-out-safe module disjoint from those four. This lane screened every
declarable construction against the REAL screens and found the supply is far
thinner than the row counts suggest: of 196 topic-clean unowned modules, only
five reach `PER_FAMILY = 10` with three or fewer added constants, and every one
of those five needs a typeclass instance or a `List`/`Char` layer rather than a
mathematical construction. The one construction that moves the answer is
**`Nat.primeCounting`/`Nat.primeCounting'`**, which opens
`Mathlib.NumberTheory.PrimeCounting` (9 rows) and takes the module-disjoint
viable-ten count from **0 to 5**; adding `Nat.lcmUpto`
(`Mathlib.NumberTheory.Chebyshev`, 3 rows) takes it to **16**. The measured
reason the second construction is not optional: `Nat.primeCounting_eq_primeCounting'_succ`
is MATHLIB'S OWN DEFINING EQUATION (`Nat.primeCounting.eq_1` states it verbatim),
so it is `rfl` under ANY faithful definition of the pair — in Mathlib as much as
here — and it sits inside the alphabetically-first ten of every
PrimeCounting-only bundle. `Nat.lcmUpto`'s three rows sort ahead of it and
displace it: **8 of the 16 viable tens carry no definitional row at all**. Four
definitions are declared (`Nat.isPrime`, `Nat.primeCounting'`,
`Nat.primeCounting`, `Nat.lcmUpto`), with evaluation tests and nothing else —
no theorem about any of them, because every such theorem is a candidate
held-out row.

Index-status: accepted

## Context

[ADR-1556](adr-1556-draw-19-is-refused-one-viable-held-out-family-and-r5-needs-two.md)
refused draw 19 and named its unblock precisely:

> ADR-1420 Route 1, the same route draw 18 used: **a construction lane declaring
> one held-out-safe module disjoint from `{Factorization.Basic,
> PythagoreanTriples, SumTwoSquares, IntervalCases}`**, topic-, vocabulary- and
> R9-clean.

[ADR-1420](adr-1420-the-refill-draw-is-not-authorable-one-two-row-module-blocks-it.md)
Route 1 carries the rule this lane is bound by, and
`count_and_div_max_pow.rs` restates it in the kernel:

> The lane must declare the DEFINITION only — declaring theorems about it spends
> the family through R9.

## The re-measurement, before anything

The committed environment snapshot was **2838** declarations against a live
kernel of **3014**; it goes stale only in the fail-closed direction, but a
baseline that is 176 declarations behind cannot separate this lane's effect from
the rest of the tree's. So it was regenerated first, from its own producer
(`shape_search --include-constructed …` piped to
`gen-autogenesis-nursery-refill.py --snapshot-from`), and the refusal was
re-measured on it:

| gate | before this lane | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=500 env=3014 development=180 held-out=190 train=130 screen_drift=31` |
| `adr-1556-draw-19-screen.py` | **0** | `env=3014 unowned_modules=23 unowned_rows=79 distinct_tens=40668 viable=3 disjoint_pairs=0 failures=0` |

The refreshed environment does not move the refusal by one row: same 23 modules,
same 79 rows, same 40,668 distinct tens, same 3 viable, same 0 disjoint pairs,
same four modules in every viable ten. The screen's own control still fires
(lifting ADR-1450's `Nat.Count` bar takes the search to 35 viable / 20 pairs),
so the zero means what it says.

## The screen for a construction, and what it found

The candidate space is every constant that is MISSING from
`admissible(env, vocabulary)` and gates at least one row in a module that is
unowned, topic-clean against every published development/train family, not one
of the four blocking modules, and not `do-not-draw-held-out`. Measured with the
real `admissible()` / `blockers_for()` / `HYGIENE` / `topics()` /
`barred_modules()`:

- 248 unowned modules carry at least one screened-or-blocked row; **196** are
  topic-clean, non-blocking and non-barred.
- Exactly **five** of those 196 reach `PER_FAMILY = 10` on their own with three
  or fewer added constants: `Init.Data.Int.OfNat` (`NatCast.natCast`),
  `Init.Data.Int.Pow` (`instPowNat`, `Int.instNatPow`), `Init.Data.Nat.ToString`
  (`Char`, `Nat.digitChar`, `Char.ofNat`), `Mathlib.Data.Nat.BinaryRec`
  (`Bool.toNat`, `Nat.bitCasesOn`) and `Mathlib.Data.Nat.Digits.Lemmas`
  (`List.length`, `Nat.digits`). **Not one of them is a mathematical
  construction** — four are typeclass instances or a `Char`/`List` layer, and
  the fifth is a binary recursor. This is the finding that makes the supply
  problem sharper than ADR-1420's row counts suggest.
- `Mathlib.Data.Nat.Choose.Central` is the largest single-construction opening
  in the whole pool — `Nat.centralBinom` alone unlocks **14** rows and is a
  one-line definition over the `Nat.choose` this kernel already has. It is
  **refused**, measured against the real `screen_family`: its topic segment
  `Choose` is published by `natural-binomial` AND by
  `natural-factorial-choose-and-squarefree`. A one-line construction that would
  open fourteen rows is unusable because of a path segment, and that is worth
  recording rather than rediscovering.

A family is a BUNDLE, so the decisive question is not "does one module reach
ten" but "does a module-disjoint viable TEN exist". That was run against the
real `ADJ.screen_family` / R9 / R12 over every bundle of at most five
non-blocking modules, for each candidate declaration set:

| declared | pool (non-blocking) | viable module-disjoint tens |
| --- | --- | ---: |
| nothing (today) | 17 modules, 47 rows | **0** |
| `Nat.centralBinom` | 18 modules, 61 rows | 0 (topic-refused) |
| `Nat.lcmUpto`, `primorial` | 19 modules, 53 rows | 0 |
| `Nat.isPowerOfTwo`, `Nat.nextPowerOfTwo` | 19 modules, 51 rows | 0 |
| `Nat.FermatPsp`, `Nat.ProbablePrime` | 18 modules, 51 rows | 0 |
| `Nat.isPrime`, `Nat.primeCounting` | 18 modules, 52 rows | 0 |
| `Nat.isPrime`, `Nat.primeCounting'` | 18 modules, 50 rows | 0 |
| **`Nat.isPrime`, `Nat.primeCounting`, `Nat.primeCounting'`** | 18 modules, 56 rows | **5** |
| **+ `Nat.lcmUpto`** | 19 modules, 59 rows | **16** |

Either half of the `primeCounting` pair on its own yields nothing; the pair is
the unit. A ten built only from modules disjoint from the four blockers is, by
construction, module-disjoint from all three tens viable today, so its existence
is exactly the `disjoint_pairs > 0` that R5 needs.

## Why `Nat.lcmUpto` is part of the construction and not scope creep

`Mathlib.NumberTheory.PrimeCounting`'s pool contains
`Nat.primeCounting_eq_primeCounting'_succ : ∀ n, n.primeCounting = (n + 1).primeCounting'`.

That is **Mathlib's own defining equation** — the same inventory carries
`Nat.primeCounting.eq_1` stating it verbatim, and Mathlib's `def primeCounting
(n : ℕ) := primeCounting' (n + 1)` makes it `rfl` there. It is therefore `rfl`
under any faithful definition of the pair in this kernel too: both sides
delta-unfold to the same `Nat.count Nat.isPrime (succ n)` with `n` still a free
variable, so no numeral is needed and `Nat.refl` closes it.

This is the `Int.gcd_eq_natAbs` shape ADR-1556 found, with one difference that
matters and is stated rather than glossed: there, a Mathlib THEOREM coincided
with OUR definitional choice; here the row is the SOURCE library's own
unfolding, trivial wherever it is formalized. Either way it is not a blind row,
and it sorts inside the alphabetically-first ten of every PrimeCounting-only
bundle, so every one of the 5 tens above carries it.

The available responses were: (1) declare the pair with a deliberately
non-definitional body for `primeCounting` so the row becomes a genuine theorem —
rejected, because choosing a construction to make a held-out row harder is
tuning the blind population, which is the thing the split policy exists to
prevent; (2) declare faithfully and disclose, leaving every viable ten with one
free row; or (3) declare faithfully AND open a second topic-clean module whose
rows sort AHEAD of it, so that tens without the row exist and the draw lane can
choose one.

Route 3 was taken. `Nat.lcmUpto` (`Mathlib.NumberTheory.Chebyshev`, 3 rows:
`lcmUpto_dvd_factorial`, `lcmUpto_ne_zero`, `lcmUpto_pos`) is a two-line
`Nat.rec` fold over the `Nat.lcm` this kernel already has, and `Nat.lcmUpto_*`
sorts before `Nat.monotone_*` and `Nat.primeCounting_*`. Measured: with it,
**16** viable module-disjoint tens exist and **8 of them do not contain
`Nat.primeCounting_eq_primeCounting'_succ`**. Both numbers, and the row's
definitional status, are published here so the draw lane picks with its eyes
open rather than inheriting a claim.

## The construction

Four definitions, in `crates/axeyum-lean-kernel/src/nat_prelude/prime_counting.rs`.
Definitions, their evaluation tests, and nothing else.

```text
Nat.isPrime (n : Nat) : Bool :=
  Nat.beq (Nat.countRange (fun d => Nat.beq (Nat.mod n (Nat.succ d)) 0) n) 2
Nat.primeCounting' (n : Nat) : Nat := Nat.count Nat.isPrime n
Nat.primeCounting  (n : Nat) : Nat := Nat.primeCounting' (Nat.succ n)
Nat.lcmUpto (n : Nat) : Nat := Nat.rec 1 (fun j ih => Nat.lcm ih (Nat.succ j)) n
```

**`Nat.isPrime` is a divisor COUNT, not a trial division, and that is what makes
it cheap here.** `countRange p n` folds over `j < n`; taking `p j := (n % (j+1) = 0)`
counts the divisors of `n` in `[1, n]`, and `n` is prime exactly when that count
is `2`. So the predicate needs no fuel recursion, no `Bool` conjunction and no
new recursion principle — only `countRange`, `mod`, `succ` and `beq`, all
already declared. The two degenerate rows fall out rather than being conventions:
`n = 0` counts nothing (`0 ≠ 2`, not prime) and `n = 1` counts only `1`
(`1 ≠ 2`, not prime).

`Nat.isPrime` is NOT Mathlib's `Nat.Prime`: this kernel declares no `Nat.Prime`
and no `DecidablePred`, and spells primality as an `And`. It is a `Bool`
predicate with a different construction, so — by the mirror-flip criterion in
`CLAUDE.md`, the `Nat.count`/`Nat.nth` case and not the
`Nat.descFactorial_of_lt` case — no `ml430` mirror stated against `Nat.Prime`
may be flipped on account of it. No row in the pinned inventory is NAMED
`Nat.isPrime` and no row's type mentions it (measured: 0 and 0), so declaring it
opens nothing by itself and collides with nothing at R9.

`Nat.primeCounting'` counts primes strictly below `n` and `Nat.primeCounting`
counts primes up to and including `n`, which are Mathlib's conventions
(`primeCounting' = Nat.count Nat.Prime`, `primeCounting n = primeCounting' (n+1)`).

`Nat.lcmUpto n` is `lcm(1, …, n)` with `lcmUpto 0 = 1`, matching
`(Finset.Icc 1 n).lcm id` on the empty range.

## Blindness, before and after

`shape_search` rebuilt through `scripts/cargo-serialized.sh`; freshness
confirmed against a control that landed the same day —
`--name Rat.rank --kind definition --expect 1` returns `FOUND 1` over an index
of 3,014 declarations.

The three new NAMES are absent (`--expect-absent`, each with its own
`any-kind=3014` positive control): `Nat.isPrime`, `Nat.primeCounting`,
`Nat.primeCounting'`, `Nat.lcmUpto`, and the case-and-separator-insensitive
`--name-like primecounting` / `--name-like lcmupto`.

Ten of the nineteen candidate rows across the viable tens are statements ABOUT
`Nat.primeCounting`, `Nat.primeCounting'` or `Nat.lcmUpto`. Those constants do
not exist in this kernel before this lane, so no declaration in it can state
those rows — the name query is the complete argument for all ten, not a proxy
for it. The remaining nine were screened by SHAPE in the kernel's own
vocabulary, since this kernel declares no `Nat.Prime`, no `Ne` and no
`Nat.Coprime`; see the lane status document for the query-by-query record.

## Decision

Declare `Nat.isPrime`, `Nat.primeCounting'`, `Nat.primeCounting` and
`Nat.lcmUpto` as Definitions with evaluation tests, register them in the
prelude's checked-and-axiom-free inventory at footprint 0, and declare **no
theorem about any of them**. Record the `Nat.primeCounting_eq_primeCounting'_succ`
finding here rather than acting on it: converting it into a bar is a draw-lane
decision, and the eight definitional-row-free tens mean the draw does not need
one.

## The measured result

```
# before, on the refreshed 3014 snapshot
ADR_1556_DRAW_19_SCREEN|env=3014|unowned_modules=23|unowned_rows=79
                       |distinct_tens=40668|viable=3|disjoint_pairs=0|failures=0   exit 0
# after
ADR_1556_DRAW_19_SCREEN|env=3018|unowned_modules=25|unowned_rows=91
                       |distinct_tens=64142|viable=196|disjoint_pairs=219|failures=2 exit 1
```

`modules contributing a row to EVERY viable ten` goes from
`['Mathlib.Data.Nat.Factorization.Basic', 'Mathlib.NumberTheory.PythagoreanTriples',
'Mathlib.NumberTheory.SumTwoSquares', 'Mathlib.Tactic.IntervalCases']` to `[]`.
The chokepoint is what ended, not merely the count.

**`failures=2`, and what each is.** One is the deliverable: the assertion named
`the refusal still holds` fails with `a disjoint pair EXISTS -- author draw 19`,
the script's own documented success signal. The other is a finding about the
screen: its minimal-cover pruning now **undercounts** — 37 viable against the
exact pass's 196. ADR-1556 predicted that direction ("a superset does not draw
the same ten, because an added module's names can sort earlier") but asserted
the two passes agreed, which they did at 3 vs 3 and no longer do on a richer
pool. The EXACT pass is the authority and is where `disjoint_pairs=219` comes
from; the control still fires (228 viable / 1,913 pairs with ADR-1450's
`Nat.Count` bar lifted), so the search is sound and it is the pruning shortcut
that has expired. The next lane to touch that script should drop the pruned pass
or weaken its assertion to `pruned <= exact`.

## A second finding: a stale snapshot silently suspends R11

`check-holdout-adjacency.py` reads the COMMITTED environment snapshot. With that
snapshot 176 declarations behind, refreshing it — which any lane must do for its
own declarations to be visible to the autogenesis screens — turns the gate red,
**with none of this lane's declarations present**:

| snapshot | exit | refused |
| --- | ---: | --- |
| 2838 (the state on `main`) | 0 | none |
| 3014 (refreshed, without this lane's four) | **1** | `natural-factorization-lcm`, `natural-max-power-dividing` |
| 3018 (with them) | **1** | the same two |
| 3018, after the re-sweep below | **0** | none |

Both are `disclosure` refusals: the recorded sweeps predate six
`Nat.factorization*` declarations and eight other `prime`-stem ones from other
lanes. So R11's environment signal had been comparing today's families against
a two-day-old kernel and reporting `clean`. **A disclosure review is only as
fresh as the snapshot it is scored against, and nothing was gating that
freshness.**

Repaired by an actual re-sweep of both reviews rather than a number bump, each
with a decisive query rather than an argument:

- `natural-factorization-lcm` (`lcm` 20 → 21, `factorization` 3 → 9): the six new
  `factorization` names are the prime-factorization MULTISET construction and its
  product, a different function from the per-prime max split
  `factorizationLCMLeft`/`Right` compute; the one new `lcm` name is this lane's
  `Nat.lcmUpto`, a fold over a RANGE rather than a statement about a PAIR.
  `--const Nat.factorizationLCMLeft --kind theorem --expect-absent` and the same
  for `…Right` are both ABSENT with a live positive control.
- `natural-max-power-dividing` (`prime` 111 → 122, `max` and `divmaxpow`
  unchanged at 44 and 2): none of the twelve new `prime`-stem names is a
  prime-INTERVAL statement, which is the Bertrand shape that family turns on,
  and the primeCounting pair counts primes below a bound without asserting one
  exists there. `--const Nat.divMaxPow --kind theorem --expect-absent` is ABSENT.
  `divmaxpow` staying at 2 is the load-bearing number: those two are the
  definitions themselves.

Neither verdict changed — only the recorded sweep and the narrative. The
checker's guard is shown non-vacuous by the sequence itself: it refused twice
before the re-sweep and refuses nothing after it.

## Consequences

- `adr-1556-draw-19-screen.py` exits **1** after this lane — its documented
  success signal, "a disjoint pair EXISTS, the refusal has expired, author the
  draw".
- A draw lane taking `Mathlib.NumberTheory.PrimeCounting` or
  `Mathlib.NumberTheory.Chebyshev` as held-out owes R11 a disclosure review in
  `holdout-adjacency-review-v1.json`: the live environment sweep is non-empty
  (`prime`, `counting`, `primecounting`, `lcm`, `lcmupto` all hit after this
  lane), which is R11 working rather than R11 complaining.
- The environment snapshot should be refreshed as part of any lane that declares
  into a prelude, not left to accumulate. This lane found it 176 declarations
  behind; the cost of that drift is not a stale count but a suspended R11.
- Nothing in this lane touches `FAMILY_MODULES`, `FAMILY_ROUTES`, the manifest,
  any partition, or the fact ledger. No fact is registered for the
  construction's theorems, because there are none.
