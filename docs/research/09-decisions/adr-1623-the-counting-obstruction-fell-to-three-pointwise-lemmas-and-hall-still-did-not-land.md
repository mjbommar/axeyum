# ADR-1623: The counting obstruction fell to three pointwise lemmas, and Hall still did not land

Status: accepted
Date: 2026-09-05
Index-summary: ADR-1614 named three things Hall's sufficiency needed and told the next lane to size the COUNTING one. All three are now closed — `unionOver`'s congruence in its index set, `unionOver` under family modification, and the glue of two matchings with disjoint images — and none of them turned out to be a counting argument in the shape ADR-1614 predicted. Deleting commutes with the union POINTWISE, so the only real counting is one `Nat.Finset` law (`card_le_card_sdiff_add`). Hall's sufficiency STILL did not land; the obstruction has moved a third time, and it is now the EMPTY SET — `Nat.Finset.singleton` has no lemmas at all (`--const` ABSENT at 3,017 declarations) and nothing turns a positive `card` into a member.
Index-status: accepted

## Context

[ADR-1608](adr-1608-the-graph-carrier-forces-symmetry-and-irreflexivity.md)
landed Hall's marriage theorem in its **necessity** direction and named three
missing pieces, calling the subset search the real one.
[ADR-1614](adr-1614-searching-over-subsets-is-a-reflection-primitive-not-a-hall-detail.md)
built that search, closed the choice problem, and moved the obstruction. Its §4
is explicit about what it handed on:

> **`unionOver` has no congruence lemma** […] That one is bookkeeping.
> **Transporting Hall's condition across a deleted family is not.** […] a
> genuine counting argument — `card (unionOver nb' t') ≥ card (unionOver nb
> (t ∪ t')) − card (unionOver nb t)` — over a union whose bound changes at
> every step […]
> **Gluing two matchings into one `f : Nat → Nat`** needs the two images to be
> disjoint […] nothing relates the two images yet.
>
> So the honest statement of where Hall stands: **the choice problem is solved,
> the counting problem is not.** A lane taking the next slice should not size
> the search again — it should size `unionOver` under family modification, and
> should expect that to be the whole of the remaining work.

This ADR takes that slice. **All three pieces are closed.** It does not land
Hall's sufficiency, and the last section says what now stands in the way —
which is again a different obstruction from the ones this lane removed, and the
third time in three lanes that the named blocker was not where the work was.

## Decision

### 1. The prediction was wrong in an instructive way: deleting commutes with the union POINTWISE

ADR-1614 expected the family-modification step to be a counting argument over a
union "whose bound changes at every step". It is not a counting argument at all.
`crates/axeyum-lean-kernel/src/nat_prelude/hall.rs`:

```text
Nat.Hall.memB_unionOver_sdiff : ∀ nb u t v,
  Eq Bool (memB (unionOver (fun i => sdiff (nb i) u) t) v)
          (memB (sdiff (unionOver nb t) u) v)
```

Throwing `u` out of every member and then unioning gives the same set as
unioning and then throwing `u` out. The reason is that the deleted set does not
depend on the index: the statement is `(∃ i ∈ t. P i ∧ ¬Q) ↔ (∃ i ∈ t. P i) ∧ ¬Q`,
where `Q` is outside the quantifier's scope. Once that is available, `card`
follows in ONE step through `Nat.Finset.card_congr_of_memB` (ADR-1614's own
lemma), and the deficiency inequality Hall's induction actually needs,

```text
Nat.Hall.card_le_card_unionOver_sdiff_add : ∀ nb u t,
  Le (card (unionOver nb t))
     (add (card (unionOver (fun i => sdiff (nb i) u) t)) (card u))
```

is that plus a single `Nat.Finset` law about ONE deletion. The union's changing
bound never enters: the transport is pointwise, and `bound (sdiff s u)` is
`bound s` by ι, so the modified family has the *same* `unionBound` anyway.

**What the lane should take from this.** ADR-1614's sizing was a prediction from
the textbook's shape, where the step is written as a subtraction over unions.
Reading the same step through this carrier's *definitions* — where `unionOver`
is a bounded existential and `sdiff` is a pointwise selector — turns the
quantifier commutation into the whole content and leaves one small counting
lemma behind. The general form: **before pricing a step as counting, check
whether the quantifier it ranges over is the only thing moving.**

### 2. The one genuine counting law, and it is a `Nat.Finset` law

`crates/axeyum-lean-kernel/src/nat_prelude/finset.rs`:

```text
Nat.Finset.card_le_card_sdiff_add : ∀ s t,
  Le (card s) (add (card (sdiff s t)) (card t))
```

Additive, like every other inequality in that file, because `Nat.sub` is
truncated — `card s − card t ≤ card (sdiff s t)` is the same statement and the
truncation makes it vacuously weaker exactly when `card t` is large, which is
the case the Hall step cares about.

The proof is the file's workhorse pattern. Fold all three counts over the common
bound `bound s + bound t`, where `card_eq_countRange_add` collapses each back to
its own `card`; `sdiff s t` is free there because its stored bound IS `bound s`.
Between the folds sit two loose `countRange` facts that already existed:
`Nat.countRange_le_of_subset` applied to `p ⊆ (p \ q) ∪ q` (pointwise, one
`Bool` decision on `q k`), and `Nat.countRange_union_add_inter` read as an
inequality by discarding the intersection through `Nat.le_add_right`.

It is filed in `finset.rs`, not `hall.rs` — the same call ADR-1614 made for
`card_congr_of_memB`, and for the same reason ADR-1608 recorded as a hazard it
entered knowingly. Nothing about it is a Hall detail.

### 3. `unionOver` gets a two-sided characterisation, and the congruence falls out

ADR-1608 declared `Nat.Hall.anyBelow` with its INTRODUCTION rule only and named
the elimination rule as what sufficiency would need; ADR-1614 observed it is a
one-dimensional instance of `allBelow_false_witness` and called it bookkeeping.
It is, and it is now proved:

```text
Nat.Hall.anyBelow_witness : ∀ f n, Eq Bool (anyBelow f n) true →
  Exists (fun i => And (Lt i n) (Eq Bool (f i) true))

Nat.Hall.memB_unionOver_elim : ∀ nb t v,
  Eq Bool (memB (unionOver nb t) v) true →
  Exists (fun i => And (Eq Bool (memB t i) true)
                       (Eq Bool (memB (nb i) v) true))
```

`memB_unionOver_elim` is the converse of ADR-1608's `memB_unionOver`, and with
it `unionOver` has a two-sided characterisation for the first time: `v` is in
the union exactly when SOME index of `t` supplies it. **Everything else in this
lane is that characterisation used twice**, once per direction of an equation.

The congruence ADR-1614 asked for follows:

```text
Nat.Hall.memB_unionOver_congr : ∀ nb t t',
  (∀ i, Eq Bool (memB t i) (memB t' i)) →
  ∀ v, Eq Bool (memB (unionOver nb t) v) (memB (unionOver nb t') v)

Nat.Hall.card_unionOver_congr   -- the same, through card_congr_of_memB
```

Membership in the union never mentions the index set's stored bound, which is
the whole reason the congruence holds while the two unions are not `Eq` and
their bounds genuinely differ.

Two design notes worth recording. **The witness predicate drops the index
bound.** `memB_unionOver_elim` yields `memB t i = true` and not
`Lt i (bound t) ∧ …`, because `Nat.Finset.lt_bound_of_memB` recovers the bound
from the membership and every consumer would otherwise discard it — the same
call `finset.rs` made when it dropped the `Lt i (bound s)` premises from
`card_le_of_injOn`. **A two-way implication becomes an equation by three nested
`Bool` decisions** (`bool_eq_of_iff` in `hall.rs`), not by `propext`, which this
kernel does not have. That helper is used by both equations in this lane and is
the shape any future `memB`-level equation will need.

### 4. Gluing needs disjoint IMAGES and not disjoint index sets

```text
Nat.Hall.glue f g s := fun i => bool_select_nat (memB s i) (f i) (g i)

Nat.Hall.isMatching_union : ∀ s1 s2 nb f g,
  IsMatching s1 nb f → IsMatching s2 nb g →
  (∀ a b, memB s1 a = true → memB s2 b = true → Eq Nat (f a) (g b) → False) →
  IsMatching (union s1 s2) nb (glue f g s1)
```

`Nat.Finset.card_le_of_injOn` (ADR-1593) is *not* what proves this, contrary to
ADR-1614's expectation: `card_le_of_injOn` counts an injection, and what is
needed here is that the glued function IS one. The content is four branches, one
per pair of decisions on `memB s1 i` and `memB s1 j`; the two diagonal ones are
each matching's own injectivity, and the two mixed ones are refuted by the
disjointness hypothesis at exactly that pair.

**The index sets need not be disjoint, and that is stronger than the textbook's
statement.** `glue` reads `s1` first, so a shared index takes `f`'s value and
the definition is unambiguous with no side condition; the mixed branch still
closes, because `j ∈ union` together with `j ∉ s1` gives `j ∈ s2` through
`Nat.Finset.memB_union_elim` and the hypothesis applies at `(i, j)`. Requiring
disjoint index sets would have cost every consumer a proof obligation that the
argument never uses.

`finset.rs` gains the union's membership laws to support this — the intro/elim
pair `sdiff` gets in §2:

```text
Nat.Finset.memB_union       memB (union s t) i = setUnion (memB s) (memB t) i
Nat.Finset.memB_union_left / memB_union_right
Nat.Finset.memB_union_elim  → Or, not a computed index
```

`memB_union_elim` produces an `Or` rather than a computed index deliberately:
the two sides may overlap, and `setUnion` reads the left one first, so the
decision on `memB s i` IS the disjunction. `memB_union`'s tail costs one step
more than `memB_sdiff`'s, because `union` stores `bound s + bound t` and putting
an index above it means putting it above EACH — `Nat.le_add_right` on the left,
the same lemma plus one `add_comm` on the right. `memB_union_right` needs a
decision on `memB s i` where its `_left` twin needs none, for the same
left-first reason.

## Consequences

**What this costs.** Seventeen new declarations (one definition, sixteen
theorems), of which seven sit in `finset.rs` as plain `Nat.Finset` laws with no
Hall content. `declarations` went from 3,000 to 3,017 on a `shape_search` binary
rebuilt at this lane's HEAD, which is exactly the seventeen. The `nat_prelude::`
sweep goes from 580 to 595 tests and its wall time is unchanged in shape: every
new statement is over free variables, and only the tests instantiate.

**What it enables, beyond Hall.** `memB_sdiff`/`memB_union` and their intro/elim
pairs are the membership calculus `Nat.Finset` did not have — before this lane
NOTHING in the tree had a type mentioning `Nat.Finset.sdiff` (`--const` ABSENT
at 3,000 declarations). `card_le_card_sdiff_add` is the deletion bound every
extremal argument uses. `isMatching_union` is the combining step for any
"assemble a global object from two partial ones" argument, of which the
combinatorics file's remaining items are mostly instances.

**What must not be inferred.** Hall's sufficiency is NOT proved, and
`hall_tests::hall_necessity_is_admitted_and_sufficiency_is_not` pins that in
both directions with the same proof term, unchanged from ADR-1608. Nothing here
is a matching-existence result; every statement is about `unionOver`, `sdiff`,
`union` or the glue of matchings that are *given*.

## Where Hall stands now, and it is not where ADR-1614 said

**All three of ADR-1614 §4's obstructions are closed and sufficiency still did
not land.** That is the finding, and it is worth stating plainly because it is
the third lane in a row where the named blocker was not the work. The remaining
gap is smaller than either previous one but it is in a place nobody has looked:
the kernel can now say a great deal about non-empty finite sets and almost
nothing about empty ones.

Measured on a `shape_search` binary rebuilt at this lane's HEAD,
`declarations=3017`, freshness control
`--name Nat.Hall.card_le_card_unionOver_sdiff_add --expect 1` FOUND (it
postdates every commit in this lane, so a stale index cannot pass):

- **`Nat.Finset.singleton` has no lemmas whatsoever.** `--const
  Nat.Finset.singleton` is ABSENT (positive control `ns Nat=1258`): not one
  declaration in the tree has a type mentioning it. Hall's base case is a
  singleton index set, its inductive step deletes a singleton, and the
  one-element matching that the glue combines with is a singleton. Missing:
  `memB (singleton a) i = beq i a` and `card (singleton a) = 1`.
- **Nothing turns a positive `card` into a member.** `Nat.countRange_eq_zero_of_all_false`
  exists and is the WRONG direction; `card_pos`, `card_eq_zero` and
  `exists_memB` are all ABSENT. Hall needs `Lt 0 (card u) → Exists (fun v =>
  memB u v = true)` to extract the representative that `HallCondition` at a
  singleton guarantees. This is the one remaining piece with real content, and
  its shape is known: a decision on
  `allBelow (fun i => notB (memB s i)) (bound s)`, `allBelow_false_witness` in
  the `false` branch and `countRange_eq_zero_of_all_false` refuting the `true`
  one. It is the same search-plus-reflection move ADR-1614 made, one dimension
  down.
- **No cardinality arithmetic for the recursion measure.**
  `card_union_disjoint` and `card_sdiff_lt` are ABSENT. The strong induction
  recurses on `card s` and needs `card (sdiff s (singleton a)) < card s` for
  `a ∈ s`, and the critical-subfamily branch needs
  `card (union t t') = card t + card t'` under pointwise disjointness — which
  reduces to `card (inter t t') = 0`, and so to the same empty-set bridge above.
- **`unionOver` over a UNION of index sets** is not related to the union of the
  two `unionOver`s. The critical-subfamily branch needs it; it is the same
  pointwise argument as §1 and should be cheap.

The skeleton itself is now unobstructed. `Nat.strongInduction` (ADR-1614) takes
the motive
`fun k => ∀ s nb, HallCondition s nb → Le (card s) k → Exists (fun f : Nat → Nat => IsMatching s nb f)`;
the two-branch split is `Nat.Finset.existsSubset_of_search` /
`forallSubset_of_search` over the critical-subfamily property, whose
membership-congruence premise `card_unionOver_congr` (this lane) discharges for
the `card (unionOver nb t)` conjunct that ADR-1614 §4 said was the undischarged
half; the deleted family's Hall condition is
`card_le_card_unionOver_sdiff_add` (this lane); and the two sub-matchings
combine through `isMatching_union` (this lane). **A lane taking the next slice
should build the empty-set bridge first and expect the rest to be assembly.**

## Mutation table

**Two mutations were RUN. Every other row is a test that runs on every green
build, and is labelled as such.** A mutation whose outcome was reasoned about
rather than measured supports no coverage claim.

| mutant | outcome | measured? |
|---|---|---|
| `memB_sdiff`'s `on_ge` branch reads `memB_of_bound_le` at `t` instead of `s` | **killed 18 of 18** — `0 passed; 18 failed`. Not one test at a time: the whole `Nat` prelude fails to build, `Kernel::add_declaration` returning `TypeMismatch`, and every test in the module dies at `build_nat_prelude(…).expect(…)` — including `any_below_is_the_bounded_existential`, which does not touch the difference at all | **RUN**, `--release --test-threads=4`, restored byte-for-byte afterwards and the clean tree verified |
| `Nat.Hall.glue` selects `g` on the set and `f` off it (the two branches exchanged) | **killed 18 of 18** — `0 passed; 18 failed`, same mechanism, `TypeMismatch { expected: ExprId(1769714), got: ExprId(1769740) }` at the prelude build. **This outcome refuted the prediction that motivated running it.** The row was written expecting a kill of exactly ONE test — the evaluation test — on the reasoning that the exchanged glue is symmetric under exchanging the two matchings and `isMatching_union`'s four branches are symmetric too. It is not: the proof term names `select_nat_true (memB s1 i) (f i) (g i)`, whose conclusion no longer matches the mutated `glue`'s reduct, so the theorem is rejected and the prelude never builds | **RUN**, restored and verified |
| any of the sixteen theorems' STATEMENTS slid by one small term | **caught by sixteen accept/reject pairs that run on every green build**: each offers the SAME proof term at the slid statement and requires the trusted gate to REJECT it. `memB_sdiff` with its two sets exchanged; `memB_sdiff_intro`/`_elim` with the deleted set's polarity flipped; `card_le_card_sdiff_add` and `card_le_card_unionOver_sdiff_add` with the deleted size dropped from the right; `anyBelow_witness` at a `false` verdict; `memB_unionOver_elim` at a `false` hypothesis; both congruences with the membership hypothesis dropped; both `sdiff` transports with the family left UNDELETED; `memB_union` with `setInter` for `setUnion`; both union intros with the conclusion flipped to `false`; `memB_union_elim` with `And` for `Or`; `isMatching_union` with the disjoint-images hypothesis dropped | RUN on every build (18 passing tests) |
| a new declaration added and left unwatched | **caught, observed:** `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free` derives its subject from the live environment and FAILED on its first honest run against this diff, naming all eleven declarations of the first commit. That is a real observed failure and the way the registration list was built | RUN |

**Every negative control here is a FALSE statement, not merely one the offered
term does not happen to prove.** That distinction is the repository's own rule
and it changed three controls during this lane: offering `memB_union_left` at
`memB_union_right`'s statement is a rejection of a TRUE proposition and proves
nothing about coverage, so both controls flip the conclusion to `false` instead.

**The finding both measured rows support, and the honest limit of it.** In this
module the kernel is the mutation detector for every definition and for every
theorem proof: a wrong step does not make one test red, it makes the shared
prelude unbuildable and every test red at once. ADR-1608 and ADR-1614 both
recorded this and it is confirmed here at two independent sites.

**The second row is a correction, and it is the more useful half of this
table.** ADR-1614 wrote that "a mutation that the kernel does not catch would be
the interesting one to construct; none was found". This lane predicted it had
found one — `glue` is a `Definition` whose two branches looked symmetric in the
only theorem consuming them — and RAN the mutation specifically to measure that.
The prediction was wrong: proof terms name the selector's branches positionally
through `select_nat_true`/`select_nat_false`, so branch symmetry at the level of
the *statement* does not survive into the *proof*. **No mutation the kernel
fails to catch has been found in this module yet, across three lanes.** That
absence is stated rather than glossed, and it is the reason this lane's
evaluation test for `glue` is the readable pin on the convention rather than a
load-bearing guard — exactly the status ADR-1614 claimed for its own, and which
this lane tried and failed to upgrade.

## Verification

- `nat_prelude::hall_tests` — 18 passed, 0 failed (`--release`,
  `--test-threads=4`). Nonzero count confirmed.
- `nat_prelude::` — 595 passed, 0 failed (was 580 at this lane's base commit).
  Nonzero count confirmed.
- Every new `Definition` (`Nat.Hall.glue`, the only one) has an evaluation test
  at concrete small arguments with a named wrong formula, and every new theorem
  an accept/reject pair; see the mutation table.
- All seventeen declarations have an EMPTY `Kernel::axiom_footprint`, asserted
  by two tests that check `Environment::contains` FIRST — `axiom_footprint`
  returns an empty vector for a name that was never declared, so the footprint
  assertion alone would pass vacuously on a typo.
- The `shape_search` sweeps this ADR quotes were run against a binary rebuilt at
  this lane's HEAD: `declarations=3017`, freshness control
  `--name Nat.Hall.card_le_card_unionOver_sdiff_add --expect 1` FOUND, exit 0.
  The pre-state rows quote the same binary rebuilt at the lane's BASE commit,
  `declarations=3000`, positive control
  `--name Nat.Finset.forallSubset_of_search --expect 1` FOUND.
