# ADR-0645: Draw 6 is declined — there is no held-out-safe family left

Status: accepted
Date: 2026-08-30
Index-summary: ADR-0620 predicted draw 6 could not satisfy R5 from un-owned modules; measured, it is worse — zero coherent held-out-safe families exist, not one, so draw 6 is declined rather than authored, and the two cheapest unblocks are named and sized (`Nat.dist`, `Nat.nth`), while `instSubNat` — the lever ADR-0620 recommends — is measured to open nothing

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0615
(the evaluation envelope is per-cohort and a draw is incremental), ADR-0616
(the ceiling counts attestation), ADR-0619 (the queue refills from the
kernel, not from the bridge), ADR-0620 (held-out supply is the scarce half
of a draw)

## Context

ADR-0620 closed with a prediction: "About four [held-out-safe propositions]
remain, and one of them carries a train adjacency. R5 requires two new
held-out families of ten rows each. **Draw 6 cannot satisfy it from un-owned
modules at all.**"

This ADR is the measurement of that prediction, taken while attempting to
author draw 6. **The prediction holds, and the true condition is worse than
it states.** No draw was authored. `FAMILY_MODULES` and `FAMILY_ROUTES` are
unchanged, the manifest is untouched, and no row moved partition.

## Decision

**Decline draw 6.** Record the measured supply so the next lane does not
re-derive it, and name the specific unblocks with their measured yield.

Do not lower R5, and do not place a family over already-published
mathematics into held-out. Which of ADR-0620's three routes to take is a
policy decision this ADR deliberately does not make; it only establishes
which of them are actually cheap, and one of them is not the one ADR-0620
recommends.

## What was measured

Every number below is re-derived for this draw against the same pinned
inventory (`4285e551…`, 9,729 records) and the current environment snapshot
(2,207 declarations, bridge 72). Numbers are not carried over from draw 5.

### The pool is abundant and almost entirely unreachable

| quantity | value |
| --- | --- |
| survivors, proposer screens | 2,215 |
| drawable (generator screens applied) | 2,155 across 88 modules |
| in modules an existing family already OWNS — unreachable | **1,716** |
| in UN-OWNED modules | 439 across 58 modules |
| un-owned modules at or above the `PER_FAMILY = 10` floor | **11** |

### All eleven ready modules are over published mathematics

Un-owned, at or above the floor, each with the development or train family
that already publishes the same mathematics:

| module | n | published by | partition |
| --- | --- | --- | --- |
| `Mathlib.Data.Nat.Prime.Basic` | 48 | natural-primes | development |
| `Mathlib.Data.Nat.GCD.Basic` | 44 | natural-gcd | development |
| `Mathlib.Data.Nat.Factorial.Basic` | 40 | natural-factorial | train |
| `Mathlib.Data.Nat.Choose.Basic` | 34 | natural-binomial | development |
| `Init.Data.Nat.Bitwise.Lemmas` | 33 | natural-bitwise | development |
| `Mathlib.Data.Nat.Prime.Defs` | 29 | natural-primes | development |
| `Mathlib.Data.Nat.Fib.Basic` | 22 | natural-fibonacci | train |
| `Batteries.Data.Nat.Bitwise.Lemmas` | 21 | natural-bitwise | development |
| `Mathlib.Data.Int.Fib.Basic` | 21 | integer-fibonacci | train |
| `Mathlib.Data.Int.GCD` | 20 | integer-gcd | train |
| `Mathlib.Data.Nat.Bitwise` | 18 | natural-bitwise | development |

This is draws 2 through 5's exclusion list, unchanged and now complete:
there is nothing else at the floor. All eleven remain perfectly good for
development and train, where nothing is blind.

### The held-out-safe remainder is 7 rows, and they are not one question

Un-owned, below the floor, adjacent only to a held-out family or to nothing:

| module | n | nearest adjacency | partition |
| --- | --- | --- | --- |
| `Mathlib.Data.Int.DivMod` | 2 | integer-division | held-out |
| `Mathlib.NumberTheory.SumTwoSquares` | 1 | descent-and-well-ordering | held-out |
| `Mathlib.Analysis.…Pow.NthRootLemmas` | 1 | natural-square-root | held-out |
| `Mathlib.Data.Nat.Sqrt` | 1 | natural-square-root | held-out |
| `Mathlib.Order.Monotone.Basic` | 1 | none | — |
| `Mathlib.Data.Nat.Order.Lemmas` | 1 | descent/induction | held-out |

Seven rows against a hard `PER_FAMILY = 10`, and they are Int `emod`
boundary behaviour, sums of two squares, an nth-root bound, non-existence of
a square, monotone stabilisation, and a `Nat` existence lemma. Every draw
from 2 onward required a family to be *one coherent question*; this is six.
`Mathlib.NumberTheory.PythagoreanTriples` (1) is excluded for the reason
draw 5 gave, unchanged: `Int.sq_ne_two_mod_four` is mod-4 arithmetic beside
the TRAIN family `integer-modular-equivalence`.

**So zero held-out families can be formed, not the one ADR-0620's arithmetic
implies.** R5 needs two.

## Three corrections to ADR-0620, each re-derived here

**1. The drawable ready set is 11, not 13 — and the cause is a THIRD
proposer/generator divergence, not the two already recorded.** ADR-0620
records that `HELD_OUT_CONSTRUCTIONS` is applied by the generator and not by
the proposer, and puts the drawable set at 13 against a reported 15. That
screen is real and still fires. But the two generators also carry
**different hygiene regexes**, which ADR-0620 does not mention:

    proposer   \._|\bmatch_\d|_proof_\d|\.eq_\d|\.sizeOf_spec
    generator  … |\.inj$|\.injEq$|\.noConfusion|^Int\.Linear\.|^Nat\.Linear\. …

The generator additionally drops compiler-generated constructor lemmas and
`omega`'s internal certificate vocabulary. That collapses the two smallest
"ready" modules below the floor:

| module | proposer | generator |
| --- | --- | --- |
| `Init.Data.Int.Basic` | 10 | **6** (four `.inj`/`.injEq`) |
| `Init.Data.Int.Linear` | 10 | **2** (eight `Int.Linear.*`) |

This matters beyond bookkeeping. `Init.Data.Int.Basic` is the *only*
un-owned module at the floor whose mathematics is not already published —
natCast bridging and Int constructor injectivity, adjacent to the held-out
`integer-natcast`. Under the proposer's screen it looks like exactly the
held-out family this draw needed. Under the generator's, which is the
authoritative one because the generator is what draws, it does not exist.
**Anyone sizing a draw from the proposer's output alone will find a
held-out family that the generator cannot build.**

`Mathlib.Data.Nat.Sqrt` also yields **1** here, not the zero ADR-0620
reports: `Nat.not_exists_sq` mentions no screened construction.

**2. `instSubNat` — ADR-0620's recommended cheapest route — opens NOTHING
for held-out breadth.** ADR-0620 argues that "new constants open new
*modules*, and a module with no existing family is exactly what a held-out
slot needs", and names `instSubNat` (292 sole-blocked rows; 290 on this
run) as the cheapest lever. Measured by re-running the screens with each
constant treated as admissible and counting un-owned modules that CROSS the
floor:

| declared constant | drawable | un-owned ready modules | newly opened |
| --- | --- | --- | --- |
| *(baseline)* | 2,155 | 11 | — |
| `instSubNat` | 2,440 | 11 | **0** |
| `Int.lcm` | 2,232 | 11 | 0 |
| `Int.bmod` | 2,228 | 11 | 0 |
| `Int.fdiv`+`Int.fmod` | 2,272 | 11 | 0 |
| `Int.tdiv`+`Int.tmod` | 2,245 | 11 | 0 |
| `Int.sign` | 2,189 | 11 | 0 |
| **`Nat.dist`** | 2,173 | 12 | **`Mathlib.Data.Nat.Dist` (18)** |
| **`Nat.nth`** | 2,173 | 12 | **`Mathlib.Data.Nat.Nth` (11)** |

`instSubNat` adds 285 drawable rows and every one lands in a module that is
already owned or already ready. It is the largest lever on *dispatchable*
supply and worth nothing to the blind population. The argument in ADR-0620
is sound in form and wrong in fact, because it was never run.

**3. The two constants that DO unblock a draw are small and specific.**

- **`Nat.dist`** opens `Mathlib.Data.Nat.Dist` at **18** drawable rows:
  `dist_comm`, `dist_self`, `dist_eq_zero`, `dist.triangle_inequality`,
  `dist_tri_left/right(')`, `dist_mul_left/right`, `dist_add_add_left/right`,
  `dist_succ_succ`, `dist_zero_left/right`, `dist_pos_of_ne`,
  `eq_of_dist_eq_zero`, `dist_eq_intro`. One coherent question — the
  natural-number distance function as a metric. **No existing family names
  `dist` at all**; the nearest adjacency is `integer-absolute-value`, which
  is held-out. R9 name screen 0 of 18.
- **`Nat.nth`** opens `Mathlib.Data.Nat.Nth` at **11**: `nth_true`,
  `nth_false`, `nth_add`, `nth_add_one`, `nth_zero_of_zero`,
  `nth_of_forall`, `nth_mem_of_ne_zero`, `nth_mem_anti`, `nth_ne_zero_anti`,
  `nth_eq_zero_mono`, `le_nth_of_lt_nth_succ`. One coherent question — the
  selector for the k-th natural satisfying a predicate. No family names it,
  and none of the eleven mentions `Prime`, so the famous consumer (the nth
  prime, `natural-primes`, development) is not what these rows are about.
  R9 name screen 0 of 11.

Together they are exactly the two held-out families R5 demands, with 8 and 1
spare respectively. `Nat.dist a b = (a - b) + (b - a)` is close to free given
`Nat.sub`; `Nat.nth` is a genuine well-founded construction and this kernel
has `WellFounded.fix`. That is ordinary proof work, which is ADR-0620's own
stated point about route 1 — the correction is only about *which* constant.

## A separate live defect found while measuring: two generators write one file

`gen-autogenesis-nursery-refill.py --check` is **RED on `main`** and has been
since 2026-08-30T04:23:

    autogenesis-nursery-refill: 1 generated file(s) are stale, first
    artifacts/autogenesis/mathlib-statable-vocabulary-v1.json;
    regenerate without --check

`artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` has **two
writers**: `gen-autogenesis-statable-vocabulary.py` and the refill
generator's own `build_vocabulary`. They agree on the substance and disagree
on the schema — verified in-process, `bridge` (72 constants) and `settled`
are byte-identical, and only the newer generator emits `bridge_provenance`
(the per-constant "why it was promoted" labels landed in `edd775b19`) and
`row_digest`, plus a richer `coverage`.

The ordering explains why nobody saw it: draw 5 landed 01:49 and its status
doc correctly records this check as green; `edd775b19` landed **2h34m
later** at 04:23 and made the refill generator's copy stale.

**The dangerous part is the remedy the error message gives.** Running the
refill generator without `--check` — which is exactly what authoring a draw
does — would rewrite that file from `build_vocabulary` and **silently delete
`bridge_provenance` and `row_digest`**, reverting `edd775b19` inside a commit
that looks like a draw. `gen-autogenesis-statable-vocabulary.py --write`
reports `UNCHANGED`, so the routine repair named in the frontier gate's
failure text does not fix it and gives no hint that anything is wrong.

This is the repository's own shared-append-point failure — two writers, one
file — arriving in an artifact rather than in `PLAN.md`. **Draw 6 could not
have been authored safely today even if the supply existed**, without first
deciding which generator owns this file. This ADR does not decide that; it
records it, because the next lane to author a draw will be told by a tool to
destroy work.

## Consequences

- Draw 6 is not authored. `FAMILY_MODULES`, `FAMILY_ROUTES` and
  `nursery-v2-extension.json` are unchanged; no row moved partition; no
  attestation count was raised.
- The dispatchable frontier stays at **12** against a floor of 10. It is
  green but has one row of headroom, and roughly 30 mirrors closed in the
  preceding day, so this is not a condition that keeps.
- The next lane to size a draw should read **11** as the drawable ready set,
  not the proposer's 15 and not ADR-0620's 13, and should apply the
  generator's `HYGIENE` rather than the proposer's before believing any
  module is at the floor.
- Whoever owns the vocabulary artifact must decide which generator writes it
  before any draw is authored.
- The cheapest path to a lawful draw 6 is `Nat.dist` plus `Nat.nth`, in that
  order of difficulty. Neither is a screen change and neither touches the
  blind population.
