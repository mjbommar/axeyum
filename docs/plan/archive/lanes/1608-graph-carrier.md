# Lane: graph-carrier — a finite graph carrier over `Nat.Finset`, R(3,3) = 6, Hall's necessity

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, graph-carrier, 2026-09-04).** Roadmap **W1-6**,
**W2-11**, **W2-12**; **ADR-1608**. The combinatorics reviewer's largest gap is
closed: `Nat.Graph` exists, `R(3,3) = 6` is a kernel theorem with both halves
axiom-free, and Hall's marriage theorem lands in its necessity direction with
the sufficiency direction's blocker named and sized.

**What landed.** `nat_prelude/graph.rs` declares `Nat.Graph` as a decidable
adjacency relation plus a vertex bound — the exact sibling of `Nat.Finset`
(ADR-1577) — with **symmetry and irreflexivity forced inside `adjB`** rather
than carried as side conditions. That is the design decision the rest of the
lane is paid for by: `Nat.Graph.HasClique3` quantifies over three bare naturals
with **no** range and **no** distinctness conjuncts, because
`lt_order_of_adjB` and `ne_of_adjB` recover both from an edge. Neighbourhoods
are `Nat.Finset`s with no conversion, so `degree_le_order` is one application of
`Nat.countRange_le`. Symmetrization is by **conjunction**, so a one-sided entry
in a transcribed adjacency table yields fewer edges, never more.

`nat_prelude/ramsey.rs` proves `Nat.Graph.ramsey_three_three :
IsRamseyNumber33 6`. The upper bound is the textbook argument as a 32-leaf case
tree over the five edges at vertex 0, each leaf one application of a shared
four-leaf lemma; it had to be a proof rather than an enumeration because a graph
is a *function* stored in the carrier, so the kernel cannot case over "all
graphs" the way `Nat.Rado.schur_arrows_five` cases over 2⁵ colourings. The lower
bound is a search over the 2¹⁰ graphs on five vertices, returning the
five-cycle, re-checked by the kernel through a `Nat.Finset.allBelow` triple loop
— and if the search returned `None` nothing is declared and the whole prelude
fails to build.

`nat_prelude/hall.rs` declares `anyBelow`, `unionBound`, `unionOver`,
`IsMatching` and `HallCondition`, and proves
`hallCondition_of_isMatching` — one application of
`Nat.Finset.card_le_of_injOn` and **no new counting machinery**, which is the
test the reviewer set.

**Where it stops, precisely.** Two named gaps, neither of them a missing lemma:

1. **Hall's sufficiency direction is not proved.** The blocker is *choosing the
   critical subfamily*: the induction splits on whether some proper non-empty
   `t ⊂ s` has `card t = card (unionOver nb t)`, and with no classical choice
   that subset must be COMPUTED by a bounded search over the `2^(bound s)`
   subsets, with its own reflection lemma. Nothing of that shape exists;
   `Nat.Finset.allBelow_false_witness` is the one-dimensional analogue and is
   the model to copy. The other two pieces — strong induction on `card s` with
   the family varying, and a lemma relating `unionOver` of a deleted family to
   `unionOver` of the original — are bookkeeping over machinery that exists. A
   lane should size the search primitive first. `Nat.Hall.anyBelow` carries only
   its introduction rule for the same reason: its elimination rule is a
   one-dimensional instance of exactly that primitive.
2. **Walks and connectivity did not land**, and this is a scoping judgement
   rather than an obstacle. The plan is an inductive
   `Nat.Graph.Reachable (g) (u) : Nat → Prop` with `refl`/`step`, a
   `Bool`-decidable `walkB` over `Nat.Finset.allBelow`, and a bridge by
   induction on the length; symmetry and transitivity are two further inductions
   (symmetry needs a "prepend an edge" lemma first). `add_inductive` admits
   indexed `Prop` families here and the two `allBelow` laws the bridge needs
   already exist, so this is a second lane's worth of proof terms and nothing
   more. `R(3,3)` was the higher-value half of the same roadmap item.

**One hazard entered deliberately, recorded so the next lane finds it.** `Nat`
had no named `Bool` algebra; `adjB`'s symmetry proof needs commutativity as a
lemma rather than eight inline cases, so `Nat.Graph.andB`/`orB`/`notB`/`neB` and
five `andB` laws are filed under `Nat.Graph`. `hall.rs` already imports
`Nat.Graph.andB_intro`, which is the first evidence the names want to move to a
`Nat.Bool` namespace. They were not moved because the move is a rename across
two preludes; a lane that needs a third `Bool` combinator should do it.

**What it costs.** The `Nat` prelude's own sweep went from roughly 18 s to 55 s
wall (`--release`, `--test-threads=4`, on a box under load ~20), essentially all
of it the Ramsey proof terms. An `R(3,4)` attempt by the same method would
multiply the case tree; the right response there is the Ramsey recurrence
`R(s,t) ≤ R(s−1,t) + R(s,t−1)`, which consumes the degree and neighbourhood
counting this lane landed.

<!-- plan-section: landed-changes -->

| 2026-09-04 | graph-carrier | `Nat.Graph` (ADR-1608): a decidable adjacency relation plus a vertex bound, sibling of `Nat.Finset`, with symmetry and irreflexivity forced inside `adjB`; neighbourhoods as `Nat.Finset`s and degrees through `countRange_le` |
| 2026-09-04 | graph-carrier | `R(3,3) = 6` in the kernel, both halves axiom-free: a 32-leaf case tree for the upper bound and a reflected five-vertex search certificate for the lower (`F:ramsey-r33-six`) |
| 2026-09-04 | graph-carrier | Hall's marriage theorem, necessity direction, over `Nat.Finset` through `card_le_of_injOn`; sufficiency NOT proved and its blocker named — computing a critical subfamily needs a bounded subset search with its own reflection lemma |
