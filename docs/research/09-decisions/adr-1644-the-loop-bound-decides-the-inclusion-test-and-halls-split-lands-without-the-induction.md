# ADR-1644 — The loop bound decides the inclusion test, and Hall's split lands without the induction

Index-summary: A `Bool`-valued inclusion test is congruent in an argument only if
its loop bound does not depend on that argument; `subsetFixed` takes the bound
from the fixed set, `allBelow_congr` is the missing law that makes it work, and
both branches of Hall's critical-subset split are now proved — the strong
induction that composes them is not.
Index-status: Accepted

Date: 2026-09-05
Lane: `hall-theorem`
Supersedes nothing. Continues ADR-1608, ADR-1614, ADR-1623, ADR-1630.

## Context

Hall's marriage theorem has been landing in slices. Necessity
(`Nat.Hall.hallCondition_of_isMatching`) has been proved since ADR-1608.
ADR-1614 gave the sufficiency direction a subset-search primitive and
`Nat.strongInduction`. ADR-1623 discharged the counting obstructions
(`memB_unionOver_elim`, `card_unionOver_congr`, `card_unionOver_sdiff`,
`card_le_card_unionOver_sdiff_add`, the matching `glue`). ADR-1630 gave the
induction a bottom: the empty and singleton index sets.

What ADR-1630 left was a sizing, not a proof: the inductive step has to DECIDE
"is some proper nonempty `t ⊆ s` critical?", and the previous lane measured the
remainder as exactly one missing lemma plus bookkeeping.

## Decision 1 — a decidable inclusion test takes its loop bound from the set it
is congruent in, not from the set on the left of the inclusion

`Nat.Finset.anySubset` is the kernel's only decision procedure over subsets, and
its exhaustion rule `Nat.Finset.forallSubset_of_search` carries a congruence
premise:

```text
(∀ u v, (∀ i, memB u i = memB v i) → P u = P v)
```

That premise, and not the mathematics, fixes the shape of the inclusion test.
`Nat.Finset.subsetB s t` loops `allBelow` to `bound s`, so the natural spelling
of `t ⊆ s` is `subsetB t s`, whose loop runs to `bound t`. Two sets with the
same members and different stored bounds then get different loop lengths, and
the congruence premise is not provable for a predicate that mentions it. This is
not a proof-engineering annoyance that a cleverer term would avoid: the two
loops genuinely compute different things, because `allBelow` is a bounded
search and the bound is an argument.

So the test is spelled with the bound taken from the FIXED set:

```text
Nat.Finset.subsetFixed s t := allBelow (fun i => if memB t i then memB s i
                                                 else true) (bound s)
```

Congruence in `t` then reduces to `allBelow`'s congruence in its PREDICATE.

**This is a general rule, not a Hall detail.** Any `Bool`-valued predicate that
is going to be handed to `forallSubset_of_search` must have every loop bound in
it independent of the quantified set. Reading it off the other argument is the
cheapest way to arrange that, and it costs a bound hypothesis on the
elimination rule (below), never on the introduction rule.

### The price, stated

`Nat.Finset.mem_of_subsetFixed` needs `Lt i (bound s)` and
`Nat.Finset.subsetFixed_of_mem` does not. That asymmetry is `allBelow`'s: a loop
that ran to `bound s` answers only indices below `bound s`, while a hypothesis
holding at every index in particular holds at those. It is not a defect of the
statement. Above `bound s`, `memB s i` is `false` by `memB_of_bound_le`, so the
missing direction is genuinely FALSE for a `t` wider than `s` —
`subsetFixed empty (singleton 0)` is `true`, not `false`, because `bound empty`
is `0` and the loop answers no index at all. The committed test
`the_loop_bound_comes_from_the_first_argument` asserts that value rather than
papering over it, and uses it as the discriminator that pins the bound: it is
paired with `subsetFixed (singleton 2) (singleton 0) = false`, which shares its
`t`, so a definition that looped to `bound t` could not separate the two.

## Decision 2 — `allBelow_congr` is a THIRD kind of law and it was missing

`allBelow` carried three laws before this lane: `allBelow_of_all_true`,
`allBelow_true_at` and `allBelow_false_witness`. Every one of them relates a
loop to its PREDICATE'S VALUES. None relates two loops to each other. Measured
at 3,222 declarations with a freshly built `shape_search` (positive control
`--name-like allBelow` → FOUND 4), `--const Nat.Finset.allBelow_congr` was
UNANSWERABLE, i.e. no declaration of that name existed.

```text
Nat.Finset.allBelow_congr : ∀ f g n, (∀ i, f i = g i) →
                            allBelow f n = allBelow g n
```

An ordinary induction on the bound, and — unlike all three existing laws — with
NO case split on the predicate's value. At the successor the goal is

```text
(if f j then allBelow f j else false) = (if g j then allBelow g j else false)
```

and two congruences close it: one moves the induction hypothesis through the
`then` branch, the other moves `f j = g j` through the scrutinee. Deciding
`f j` works too and costs a `Bool.rec` plus two branches for nothing.

## Decision 3 — the split's counting chain runs through a DEFINITIONAL identity,
not a new counting lemma

The critical branch needs `card (w ∪ t) = card w + card t` for disjoint `w, t`.
The obvious route is `Nat.Finset.card_union_add_card_inter` plus
`card (inter w t) = 0`, which needs a `memB_inter` lemma this tree does not have
and which would have to be written.

It is not needed. `card s` is `countRange (memB s) (bound s)` and `sum s f` is
`sumRangeIf (memB s) f (bound s)`; unfolding both, `sum s (fun _ => 1)` and
`card s` are the SAME `Nat.rec` term — the accumulator is
`ih + (if memB s j then 1 else 0)` on each side. So
`Nat.Finset.sum_union_disjoint` at the constant weight `1` already IS the
statement, and `Nat.Finset.card_union_of_disjoint` is that lemma with only its
hypothesis translated, from the pointwise implication every caller has to the
`setInter … = false` spelling `sum_union_disjoint` asks for.

**The general lesson is about where to look.** Two existing declarations were
definitionally the same function at a specialised argument, and neither's name,
type, nor doc comment says so. The way this was found was reading the two
`Nat.rec` bodies, not searching for a name. A `--const` search for
`Nat.Finset.card` would never have surfaced `sum_union_disjoint`.

The same pattern pays again in the non-critical branch: `Nat.add` recurses on
its right argument, so `add x 1` IS `succ x` by iota, and the step from
`card (unionOver nb' w) + card {v}` to `succ (card (unionOver nb' w))` is one
`card_singleton` rewrite followed by nothing at all.

## Decision 4 — both branches of the split are proved; the induction that
composes them is not

Landed and admitted axiom-free:

```text
Nat.Finset.allBelow_congr
Nat.Finset.subsetFixed                          (Definition)
Nat.Finset.subsetFixed_of_mem
Nat.Finset.mem_of_subsetFixed
Nat.Finset.subsetFixed_congr
Nat.Finset.card_union_of_disjoint
Nat.Hall.hallCondition_subset
Nat.Hall.memB_unionOver_union_of_vanishing
Nat.Hall.hallCondition_sdiff_of_critical        the CRITICAL branch
Nat.Hall.hallCondition_sdiff_singleton_of_strict the NON-CRITICAL branch
```

The critical branch's chain, at an arbitrary `w ⊆ s \ t`, writing `u` for
`unionOver nb t` and `nb'` for the deleted family:

```text
  card w + card t
= card (w ∪ t)                            disjoint union
≤ card (unionOver nb (w ∪ t))             Hall's condition at s
≤ card (unionOver nb' (w ∪ t)) + card u   the deficiency inequality (ADR-1623)
= card (unionOver nb' w) + card u         nb' VANISHES on t
≤ card (unionOver nb' w) + card t         criticality
```

Only the fourth line is new: `memB_unionOver_union_of_vanishing` says indices
whose family member is empty at a value may be dropped from a union, and
`card_congr_of_memB` turns that into the count identity. It is where the two
unions' differing stored bounds would otherwise stop the chain.

**Only one direction of criticality is a hypothesis.** `Le (card u) (card t)` is
the half that does not follow from Hall's condition; `Le (card t) (card u)` is
Hall's condition at `t` and is never used. Taking the weaker hypothesis is what
lets the caller decide the branch with a `Le` test rather than an equality test,
which matters because the search predicate has to be `Bool`-valued.

The non-critical branch takes STRICT slack on every nonempty subset and deletes
one value from every member of the family. Its hypothesis is guarded by
`Lt zero (card w)` and that guard is not cosmetic: at the empty subset the
strict inequality would read `0 < card (unionOver nb empty)`, which is false.
The empty case is discharged by `zero_le`, decided with `lt_or_ge` rather than
assumed. Hall's condition at `s` is deliberately NOT a hypothesis — it would be
redundant, since the strict hypothesis is stronger wherever it applies and the
conclusion is free where it does not.

## What did NOT land, and what it is blocked on

`Nat.Hall.sufficient` and `Nat.Hall.marriage_iff` are NOT proved. This is a
sizing, not a claim of impossibility, and the obstruction is not any of the
lemmas above.

1. **The search predicate has to be assembled and shown congruent.** Deciding
   "some proper nonempty `t ⊆ s` is critical" as a single `Bool` needs a
   conjunction of four tests — `subsetFixed s t`, nonemptiness of `t`,
   `card t < card s`, and `card (unionOver nb t) ≤ card t` — and the congruence
   premise must be discharged for the WHOLE conjunction. `subsetFixed_congr`
   (this lane) and `card_unionOver_congr`/`card_congr_of_memB` (ADR-1623) supply
   the pieces, but the three arithmetic comparisons need `Bool`-valued forms
   with congruence, and this tree has no `Nat.ble`/`Nat.blt` reflection pair
   that was checked for. That is the first thing the next lane should measure,
   not assume.

2. **`forallSubset_of_search` concludes only for sets with `Le (bound t) n`.**
   The enumeration runs over `[0, bound s)`, so a caller's `w ⊆ s` whose STORED
   bound exceeds `bound s` is not covered by the verdict, even though its
   members are. Closing that needs a normalisation step — replacing `w` by a set
   with the same members and bound at most `bound s` — which does not exist and
   is not large.

3. **Composing the critical branch back onto `s`.** `isMatching_union` produces
   a matching on `union t (sdiff s t)`, and `isMatching_congr` moves it to `s`
   given `∀ i, memB (union t (sdiff s t)) i = memB s i`. That pointwise identity
   needs `t ⊆ s` and is a small lemma nobody has written.

None of these is the counting or the congruence problem the previous three ADRs
were about. The mathematics of the step is now proved on both sides; what
remains is plumbing the DECISION into it.

## Consequences

- A new general constraint on search predicates is recorded (Decision 1): every
  loop bound inside a predicate handed to `forallSubset_of_search` must be
  independent of the quantified set.
- `allBelow` has a congruence law, which any future bounded-search reflection
  can use; it is not Hall-specific.
- `card_union_of_disjoint` exists without a `memB_inter` lemma, and the reason
  it does is worth reusing: check whether an existing declaration is your
  statement at a specialised argument before writing a new one.
- Hall's theorem remains OPEN. The fact ledger records the two branches as
  proved and the theorem itself as open, with the three obstructions above
  named, so the next lane inherits a measured remainder rather than a mood.
