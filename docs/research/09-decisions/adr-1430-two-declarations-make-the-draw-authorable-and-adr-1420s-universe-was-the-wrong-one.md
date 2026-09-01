# ADR-1430: Two declarations make the draw authorable, and ADR-1420's exhaustive answer was about the wrong universe

Date: 2026-09-01
Status: Accepted
Lane: `queue-unblock-four-families`

Index-summary: ADR-1420 proved exhaustively that at most one held-out-safe
family existed and no two disjoint ones did. That is correct for the modules
statable at the time and NOT a statement about the tree: enlarging the universe
by the 63 plain `Nat.*`/`Int.*` names a lane can honestly declare takes the
topic-clean unowned modules from 18 to 33, and the same exhaustive search then
finds 1,132 viable held-out subsets and two disjoint families for one
declaration. `Nat.count` and `Nat.divMaxPow` are declared; a four-family draw
now passes R5/R9/R11-topic/R11-vocabulary/R12 with only the two disclosure
reviews outstanding. Separately: `gen-autogenesis-nursery-refill.py --check`
is RED on `main` and three already-drawn families yield zero candidates.

Index-status: Accepted

## Context

`check-dispatchable-frontier.py` is below its floor at 3 dispatchable `ml430`
mirrors. ADR-1420 established why a refill draw could not fix it:

- R5 requires two NEW held-out families; `_with_cycle` restarts the
  `held-out, development, train` cycle per draw, so `n` fresh families give
  `ceil(n/3)` held-out and `n >= 4`.
- Screened over all `2^18` subsets of the 18 topic-clean unowned modules,
  every viable held-out subset contained `Mathlib.Tactic.IntervalCases`, which
  holds two rows, so at most one such family could exist at a time.

Its Consequences named Route 1 as the remedy: *declare a construction that
opens a topic-clean, vocabulary-clean module*. This lane took that route.

## The correction

**ADR-1420's exhaustive result is about the modules statable at the time, not
about the tree, and the difference is decisive.** Its universe was the
topic-clean unowned modules whose rows are statable **today** -- 18 modules, 57
survivors, 19 of them vocabulary-clean. That is the right universe for the
question "can a draw be authored *without writing any code*", which is the
question that lane was sent to answer.

It is the wrong universe for "what does the unblock cost". A row is
`not-statable-here` when its `type_repr` mentions a Lean constant absent from
`kernel.environment()` and from the derived bridge. Some of those constants are
carriers this kernel does not have and will not soon (`Finset`, `List`, `Set`,
`Prod`) or typeclass instances nobody can honestly declare
(`instPowNat`, `NatCast.natCast`, `Int.instMonoid`). But **63** of them are
plain `Nat.*` / `Int.*` function names -- exactly the shape a lane declares as a
kernel `Definition`.

Adding those 63 to the admissible set takes the topic-clean unowned universe
from **18 modules to 33**. Re-running the same exhaustive screen over that
universe -- real `select()` row screen, real `screen_family` (R11), real
`is_closed_evaluation` (R12), R9 against the environment snapshot -- gives:

```
declaration universe: 63 plain Nat./Int. names
topic-clean unowned modules with >=1 row: 33
VIABLE HELD-OUT SUBSETS (<= 3 decls, <= 3 modules): 1132
EXACT: two disjoint viable held-out families exist, cheapest total 1 declarations
```

Two of those subsets are single modules, which makes them coherent families
rather than bundles assembled to clear a screen:

| family | modules | declarations | pool | R9 | R12 | R11 |
| --- | --- | --- | ---: | ---: | ---: | --- |
| `natural-counting-predicate` | `Mathlib.Data.Nat.Count` | `Nat.count` | 22 | 0 | 0 | clean, vocabulary 0/10 |
| `natural-factorization-lcm` | `Mathlib.Data.Nat.Factorization.LCM` | `Nat.factorizationLCMLeft`, `…Right` | 10 | 0 | 0 | clean |

`Mathlib.Tactic.IntervalCases` appears in none of them. It was in every viable
subset of the smaller universe because it supplied two of the five
vocabulary-clean rows a family needed when only 19 existed; at 33 modules it is
not needed.

## What was declared

Two constructions, in `crates/axeyum-lean-kernel/src/nat_prelude/count_and_div_max_pow.rs`.
**The definitions and their evaluation tests, and no theorems about either**
(ADR-0653).

- **`Nat.count (dec : Nat → Bool) (n : Nat) : Nat := Nat.countRange dec n`.**
  Definitionally the `countRange` this kernel already has. Mathlib's is
  `(List.range n).countP p` over a `DecidablePred`, and this kernel has neither
  `List` nor `DecidablePred`, so under the mirror-flip criterion this is the
  `Nat.minFac`/`Nat.nth` case: every `ml430` mirror stated against Mathlib's
  `Nat.count` stays `open` and must be proved.
- **`Nat.divMaxPow n base`** -- `n` with every factor of `base` divided out.
  Genuinely new: `maxPow`, `divMaxPow`, `padic`, `ordCompl` and `multiplicity`
  return **zero** declarations from the environment. Fuel recursion in
  `Nat.nthAux`'s style; the fuel-exhaustion row returns `n`, the pass-through
  shape, because the recursion stops at the first non-multiple and returns
  exactly that value.

The kernel cannot tell a `Definition` is wrong, so both carry evaluation tests
and every control was checked to SEPARATE the two sides before anything was
written: the fuel recursion was simulated against an independent Python
reference over all `n < 60`, `base < 8` (480 pairs, zero mismatches), and
`divMaxPow`'s asymmetry gives the transposition control free --
`divMaxPow 12 2 = 3` against `divMaxPow 2 12 = 2`, asserted NOT `def_eq`.
`cargo test -p axeyum-lean-kernel --lib nat_prelude::` is **324 passed, 0
failed**, and `every_nat_declaration_is_checked_and_axiom_free` fired on the
first run naming all three new definitions, which is the environment-derived
coverage assertion doing its job.

## Is a draw authorable now?

**Yes, up to two disclosure reviews.** Run against the REAL `select()` and
`guard()` with the environment read from the kernel (2,829 declarations), for
this four-family draw:

```
  Mathlib.Data.Nat.Count                natural-counting-predicate   -> held-out
  Mathlib.Data.Nat.Factorization.Basic  natural-prime-factorization  -> development
  Mathlib.Data.Nat.Log                  natural-logarithm-base       -> train
  Mathlib.Data.Nat.MaxPowDiv            natural-max-power-dividing   -> held-out
```

R5 (two held-out), R9, R11-topic, R11-vocabulary and R12 all pass. The only
refusal left is R11's **disclosure**, which ADR-1420 itself classes as "fixable
by writing the review; not a structural block":

```
natural-counting-predicate: … declares 3 stem(s) … [('count', …, 46), …]
                            and no review is recorded
natural-max-power-dividing: … [('prime', …, 110), ('max', …, 44),
                            ('divmaxpow', 'Nat.divMaxPow', 2)]
```

Both reviews are the draw author's, and `natural-counting-predicate`'s is
**substantive rather than a formality**: `Nat.count` is definitionally
`Nat.countRange`, about which this kernel already carries 19 lemmas. The
reviewer should compare those against the drawn ten and decide whether the
family is blind enough to be held-out, or whether it belongs in `development`
with a different family taking the index-0 slot.

**The cycle index is the constraint the draw author will actually fight, and it
is worth stating.** Fresh families are sorted by `FAMILY_MODULES[f][0]`, so the
held-out slots are sorted indices 0 and 3. `Mathlib.Data.Nat.Count` is index 0
only if no fresh family's first module sorts before it, and the second held-out
family must have exactly two families between it and Count. Measured: the
lexicographic window between `Mathlib.Data.Nat.Count` and
`Mathlib.Data.Nat.Factorization.LCM` holds **12 rows across 5 modules** -- room
for one family of ten, not two -- so the Count/LCM pair cannot occupy indices 0
and 3 at `n = 4..6`. The Count/MaxPowDiv pair can, because `Mathlib.Data.Nat.Log`
(17 rows) and the `Factorization`/`Factors`/`Multiplicity` bundle (12 rows) fit
between them. That is why `Nat.divMaxPow` was declared rather than the
`factorizationLCM` pair, whose family remains a measured spare.

## The pre-existing red this lane did not cause

`python3 scripts/gen-autogenesis-nursery-refill.py --check` **exits 1 on `main`
at `46bc65cc4`**:

```
autogenesis-nursery-refill: family 'natural-find-greatest' yields 0 screened
candidates, fewer than the 10 the refill takes
```

Three already-drawn families yield **zero** candidates: `natural-find-greatest`,
`natural-integer-root` and `natural-nth-selector`. For `Mathlib.Data.Nat.Find`
the screen is 17 rows blocked on `Nat.find` and **15 blocked by the divergence
registry**, which commit `a3da5621c` (ADR-1415's module-doc sweep) widened.
ADR-1420 recorded this same command exiting 0 with `entries=460` on
`a6c531eab`, so it went red between those two commits.

It blocks every draw regardless of what families exist, and it also blocks using
`--check` as the zero-diff instrument. It needs its own lane: either the
divergence entries are wrong for those rows, or the three families need
ADR-0542 amendments.

## The zero-diff invariant

No already-drawn row may change partition or membership. Re-deriving
`select()`'s output for the committed `FAMILY_MODULES` twice -- once against the
committed environment snapshot (2,711) and once against the freshly read
environment (2,829, which contains this lane's three declarations and 115 others
that landed since) -- and diffing field by field:

```
committed snapshot 2711 declarations; freshly read 2829; new 118, gone 0
re-derived entries: before 430, after 430
  added 0  removed 0  changed 0
committed nursery-v2-extension.json publishes 460 rows
  partitions: {'held-out': 170, 'development': 170, 'train': 120}
```

**Zero rows move.** The 31 published rows absent from the re-derivation are the
`ceilRoot` / `findGreatest` / `floorRoot` rows of the three families above, and
they are absent from the BEFORE derivation as well -- the before and after lists
being identical settles that -- so they are the `a3da5621c` red, not this lane's
change.

## Decision

1. Declare `Nat.count` and `Nat.divMaxPow`, definitions and evaluation tests
   only. Landed.
2. Refresh `artifacts/autogenesis/kernel-environment-snapshot-v1.json` to the
   2,829-declaration read. Landed; proved above to move zero drawn rows.
3. Do NOT author the draw here. It needs the two disclosure reviews and a
   decision on `natural-counting-predicate`'s blindness, both of which belong
   to whoever writes it.
4. Do not treat ADR-1420's exhaustive answer as a claim about the tree. It is
   exactly right about its own universe and says nothing about what one
   declaration buys.

## Consequences

`natural-factorization-lcm` (`Mathlib.Data.Nat.Factorization.LCM`, 10 rows,
R9/R11/R12 clean behind `Nat.factorizationLCMLeft`/`…Right`) is a measured
third held-out-safe family, unspent, if a later draw needs a different
lexicographic position.

The generalisable rule, which cost this lane most of its screening time: **an
exhaustive search is only as strong as the universe it enumerates, and a
universe defined by "what is statable today" silently prices the answer at zero
declarations.** State the universe alongside the result, or the next reader
takes the refusal as permanent.
