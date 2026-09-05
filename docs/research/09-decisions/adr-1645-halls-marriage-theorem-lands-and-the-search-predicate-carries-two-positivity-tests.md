# ADR-1645: Hall's marriage theorem lands, and the search predicate carries two positivity tests

Status: accepted
Date: 2026-09-05
Lane: `hall-assembly`

Index-summary: Hall's marriage theorem is proved in the kernel, axiom-free, by
strong induction on `card s`; the decision predicate needs TWO positivity
conjuncts because the two recursive calls descend on opposite sides of the
split, the descent measure needs an equation the tree did not have, and
`criticalB s nb t = true` does NOT imply `t ⊆ s` — the search's bound equation
is what upgrades it.

Supersedes nothing. Completes ADR-1608, ADR-1614, ADR-1623, ADR-1630, ADR-1644.

## Context

Hall's marriage theorem has been landing in slices since ADR-1608. Necessity
(`Nat.Hall.hallCondition_of_isMatching`) was proved there. ADR-1614 added a
subset-search primitive and `Nat.strongInduction`; ADR-1623 the counting shelf
and the matching glue; ADR-1630 the empty and singleton base cases; ADR-1644
both branches of the critical-subset split, plus `subsetFixed` and its four
laws.

ADR-1644 closed with a remainder it called "assembly, and nothing that has been
shown to need a new idea", and named exactly one place a surprise was still
possible: "the arithmetic of the two descent steps — showing `card t < card s`
and `card (sdiff s t) < card s` from `t` proper and nonempty. Neither was
attempted here, and neither should be assumed free."

This ADR records what the assembly actually needed. The descent was cheap. Three
other things were not, and none of them appears in any prior slice's sizing.

## Decision 1 — the descent needs an EQUATION, and the inequality the tree already had is in the useless direction

`Nat.Finset.card_le_card_sdiff_add` existed: `card s ≤ card (sdiff s t) + card t`,
for arbitrary `s` and `t`. It bounds `card s` from ABOVE, and a strict decrease
needs the other direction. For a genuine subset the two sides are equal, and the
equation is one line of composition from ADR-1644's own shelf:

```text
  card s
= card (union t (sdiff s t))       memB_union_sdiff_self + card_congr_of_memB
= card t + card (sdiff s t)        card_union_of_disjoint
```

`Nat.Finset.card_add_card_sdiff` is that equation. Both descent inequalities are
then `Nat.add_lt_add_left` at the summand `zero` — whose left side IS the bare
summand by iota, because `Nat.add` recurses on its right argument — with one
`Nat.add_comm` separating the two.

**The general point is the one ADR-1644 already made about
`card_union_of_disjoint`, and it paid again:** the nearest existing name was the
wrong statement, and the right one was a composition of two lemmas neither of
whose names mentions counting a complement.

## Decision 2 — `subsetFixed s t = true` does not imply `t ⊆ s`, and the SEARCH's bound equation is what makes the branch sound

ADR-1644 stated the truncation asymmetry and gave the counterexample:
`subsetFixed empty (singleton 0)` is `true`, because `bound empty` is `0` and the
loop answers no index at all. What it did not say is that this makes the search
predicate's verdict, on its own, useless to the branch that consumes it.

`Nat.Hall.criticalB (range 3) nb (singleton 5)` is `true`, and `5 ∉ range 3`.
A reader who assumed the predicate implies inclusion would be wrong.

The proof never assumes it. `Nat.Finset.existsSubset_of_search` returns
`Eq Nat (bound t) n` ALONGSIDE the verdict, and it is that equation — fed to the
new `Nat.Finset.memB_of_subsetFixed_of_bound_le` — which upgrades the decision to
a real inclusion:

```text
Nat.Finset.memB_of_subsetFixed_of_bound_le
  : ∀ s t, Le (bound t) (bound s) → subsetFixed s t = true →
    ∀ i, memB t i = true → memB s i = true
```

Above `bound s` the index is also above `bound t`, so `memB_of_bound_le` says
`t` has no member there and the premise is REFUTED rather than used. That is the
whole content, and without it the critical branch is unsound in the literal
sense: it would recurse on a `t` that is not a subset.

The committed test
`the_predicate_alone_does_not_imply_inclusion_and_the_search_bound_is_why`
asserts both halves — the predicate accepts `singleton 5`, and
`bound (singleton 5) ≠ bound (range 3)` so the search cannot return it. It is
written that way deliberately: choosing an instance where the predicate happened
to say `false` would have hidden the hazard behind a green test.

## Decision 3 — the search predicate carries TWO positivity conjuncts, and neither implies the other

```text
criticalB s nb t := andB (andB (subsetFixed s t)  (ble 1 (card t)))
                         (andB (ble 1 (card (sdiff s t)))
                               (ble (card (unionOver nb t)) (card t)))
```

| conjunct                               | what consumes it                                   |
|----------------------------------------|----------------------------------------------------|
| `subsetFixed s t`                      | `t ⊆ s`, via Decision 2                            |
| `ble 1 (card t)`                       | `card (sdiff s t) < card s` — the SECOND descent    |
| `ble 1 (card (sdiff s t))`             | `card t < card s` — the FIRST descent               |
| `ble (card (unionOver nb t)) (card t)` | criticality, `hallCondition_sdiff_of_critical`     |

The two `ble 1 …` tests are the two nonemptiness facts the two recursive calls
need, and they sit on OPPOSITE sides of the split. Each is exactly the
hypothesis of one descent lemma, and each rejects an instance the other accepts:

- drop `ble 1 (card t)` and `t = empty` is accepted — its COMPLEMENT is
  nonempty — so the branch recurses on `sdiff s empty`, whose count is `card s`,
  and the induction does not descend;
- drop `ble 1 (card (sdiff s t))` and `t = s` is accepted — `s` IS nonempty — so
  the branch recurses on `t` at the same count.

`neither_positivity_conjunct_subsumes_the_other` asserts the four counts that
make that so, rather than asserting it in prose. Collapsing the pair is the third
registered mutant.

**Properness is spelled by the two counts, not by `t ≠ s`.** There is no
decidable set equality in play and none is needed: what the induction wants is a
strictly smaller measure on both sides, and that is what the two descent lemmas
deliver from the two positivity facts.

## Decision 4 — the exhaustion rule's `false` is turned around, not reflected

The non-critical branch has `criticalB s nb w' = false` and needs
`card w < card (unionOver nb w)`. Going directly needs
`ble a b = false → Lt b a`; this tree carries `ble_eq_false_of_lt`, the other
way, and ADR-1644's corrected blocker list did not notice the asymmetry because
it only checked that a reflection PAIR existed.

No new lemma was written. The branch decides with `Nat.lt_or_ge`: on the strict
side it is done, and on the `≥` side it BUILDS `criticalB s nb w' = true` from
the four conjuncts with `Nat.Graph.andB_intro` and clashes it against the
search's `false`. The `andB` tree is assembled, never unfolded, so the argument
does not depend on `criticalB`'s reduction shape.

The same branch has to normalise its subset first: `forallSubset_of_search`
concludes only for sets with `Le (bound w) n`, and the `w` handed to
`hallCondition_sdiff_singleton_of_strict`'s hypothesis is an arbitrary `Finset`
whose stored bound is unconstrained. `Nat.Finset.restrict` (ADR-1644) is that
normalisation, and every fact is pulled back to `w` through
`card_congr_of_memB` and `card_unionOver_congr`.

## Decision 5 — `exists_isMatching_singleton` is not used, and that is not waste

ADR-1630 landed `Nat.Hall.exists_isMatching_singleton` as a base case. The
induction does not call it. The lemma is stated at a LITERAL
`Nat.Finset.singleton a`, and an arbitrary `s` with `card s = 1` is not
definitionally one; there is no route from the count to the spelling without a
set-extensionality argument this kernel does not have.

It is not needed either. The non-critical branch commits one index and recurses
on `sdiff s (singleton x)`, and the empty case answers that. So the only base
case the induction consumes is `exists_isMatching_of_card_le_zero`.

This is recorded rather than quietly dropped because the singleton lemma remains
a correct standalone statement, and a later reader finding it unreferenced
should know it was measured as unusable HERE, not forgotten.

## What landed

Admitted and axiom-free, `declarations` 3,236 → 3,247 (theorems 2,150 → 2,160,
definitions 866 → 867):

```text
Nat.Finset.memB_of_subsetFixed_of_bound_le
Nat.Finset.card_add_card_sdiff
Nat.Finset.card_lt_card_of_subsetFixed
Nat.Finset.card_sdiff_lt_card_of_subsetFixed
Nat.Finset.memB_sdiff_congr
Nat.Hall.isMatching_of_family_sdiff
Nat.Hall.memB_false_of_family_sdiff
Nat.Hall.criticalB                              (Definition)
Nat.Hall.criticalB_congr
Nat.Hall.sufficient
Nat.Hall.marriage_iff
```

```text
Nat.Hall.sufficient   : ∀ s nb, HallCondition s nb → ∃ f, IsMatching s nb f
Nat.Hall.marriage_iff : ∀ s nb, HallCondition s nb ↔ ∃ f, IsMatching s nb f
```

`Nat.Finset.memB_sdiff_congr` is proved through
`memB_sdiff_elim`/`memB_sdiff_intro`, NOT by unfolding `Nat.setDiff`. The
unfolding route needs the exact `Bool.rec` shape that definition reduces to —
including whether the inner negation is spelled as `Nat.Graph.notB` or as a raw
selector — and a lemma resting on that is one refactor away from a
`TypeMismatch` naming nothing.

## The mutation table

Registered as `SUITES["hall-marriage-in-kernel"]` in
`scripts/tests/mutation_controls.py`, so it is re-runnable rather than a claim
in prose. Baseline green, 44 tests. All three RUN:

| mutant                                           | outcome    |
|--------------------------------------------------|------------|
| the subset descent measure weakened `<` → `≤`    | killed 44  |
| the critical and non-critical branches exchanged | killed 44  |
| the two positivity conjuncts collapsed into one  | killed 44  |

**Read that number honestly.** It is ONE kill mechanism, not 44 independent
guards: each mutant is type-correct Rust that produces a declaration the trusted
gate rejects, so `build_nat_prelude` fails and every test in the filter dies
together. What the table shows is that none of the three survives, not that the
suite has 44-fold coverage of them.

The first mutant has a second, independent killer that does NOT go through the
prelude build: `hall_descent_tests::the_subset_measure_conclusion_is_strict`
applies the lemma at a closed instance, infers the resulting type with the
kernel's own `infer`, and requires it to be `Lt 1 3` and NOT def-eq to `Le 1 3`.
A rendered-string check could not separate them, because `Nat.lt a b` unfolds to
`Nat.le (succ a) b` — which is why the test is written on types the kernel
compares rather than on the pretty-printed statement.

## Consequences

- **Hall's marriage theorem is a kernel theorem with an empty axiom footprint.**
  The `epistemic_status` and `external_status` of the fact agree; what moved is
  the trusted base, not mathematics.
- A `Bool`-valued decision handed to `anySubset` may be strictly weaker than the
  proposition it is named for, and the SEARCH's own output is what closes the
  gap. ADR-1644's Decision 1 said where the loop bound must come from; this adds
  that the caller must also consume the bound EQUATION, not just the verdict.
- A descent measure is the one place in an induction where `≤` type-checks
  everywhere it is built and fails only where it is used. The two measure lemmas
  therefore carry tests that infer an APPLIED type, not tests that read a
  rendered statement.
- A base case can be landed correct and still be unusable by the induction it was
  landed for, when it is stated at a literal constructor rather than at a numeric
  characterisation. Worth checking at sizing time, not at assembly time.
