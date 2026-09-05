# ADR-1630: The empty set fell and Hall got a base case; the obstruction is now spelling inclusion as a `Bool`

Status: accepted
Date: 2026-09-05
Index-summary: ADR-1623 moved Hall's obstruction to the empty set and the singleton — `Nat.Finset.singleton` was defined with ZERO lemmas and nothing turned a positive `card` into a member. Both are now closed: a nine-declaration shelf in `finset_singleton.rs` (including `Nat.Finset.empty`, which did not exist) and the search-based `exists_memB_of_card_pos`, plus Hall's base case and empty case in a new `hall_sufficiency.rs`. Sufficiency STILL did not land, and the obstruction has moved a fourth time to a place ADR-1614's own machinery creates: the critical-subset split must be a bounded search, `forallSubset_of_search` demands its predicate be congruent under pointwise membership, and `subsetB` carries exactly ONE lemma in the whole tree, `inter` exactly one, `allBelow` exactly its three original laws and no congruence. Measured at 3,106 declarations.
Index-status: accepted

## Context

[ADR-1608](adr-1608-the-graph-carrier-forces-symmetry-and-irreflexivity.md)
landed Hall's marriage theorem in its **necessity** direction and named three
missing pieces.
[ADR-1614](adr-1614-searching-over-subsets-is-a-reflection-primitive-not-a-hall-detail.md)
built the subset search and closed the choice problem.
[ADR-1623](adr-1623-the-counting-obstruction-fell-to-three-pointwise-lemmas-and-hall-still-did-not-land.md)
closed all three of ADR-1614 §4's obstructions and was explicit that Hall still
did not land, naming what was left:

> the obstruction has moved a third time, and it is now the EMPTY SET —
> `Nat.Finset.singleton` has no lemmas at all (`--const` ABSENT at 3,017
> declarations) and nothing turns a positive `card` into a member.

That reading was checked rather than inherited. At **3,093** declarations, with
a `shape_search` binary rebuilt at this lane's base commit:

| query | verdict |
| --- | --- |
| `--const Nat.Finset.singleton` | **ABSENT** |
| `--const Nat.Finset.sdiff` (same-kind positive control) | FOUND 7 |
| `--name-like Finset.empty` | **ABSENT** (the hint's `Nat.Subsets.empty` is a `Nat -> Bool`, not a carrier value) |
| `--const Nat.countRange --concl Exists` | **ABSENT** |
| `--const Nat.Finset.card --concl Exists` | FOUND 1 (`exists_collision`, the pigeonhole's colliding pair — not this direction) |

So the carrier could count its members and could not name one, and the only
one-element set it had was defined and unusable.

## Decision

### 1. `Nat.Finset.empty` is a CONSTANT, and is deliberately not `range 0`

`memB` truncates at the stored bound in its own definition, so
`mk (fun _ => false) b` has the same members for every `b`; there is nothing to
parameterise over and `empty` is a `Nat.Finset`, not a function of one.

`Nat.Finset.range 0` is extensionally the same set and is **not** definitionally
this one — its stored predicate is `fun _ => true`. That distinction is pinned
by an assertion in the evaluation test rather than left implicit, because it is
the whole reason the `false` predicate was chosen: with it, `memB_empty` is one
application of `memB_of_bound_le` against `Nat.zero_le`, with no case split and
no appeal to how `Nat.ble` reduces at a variable index.

### 2. The singleton gets the FULL membership equation, not two one-way rules

`memB_singleton : ∀ a i, memB (singleton a) i = beq i a` costs a case split
(`Nat.lt_or_ge` at `(i, succ a)`) that the intro and elim forms do not:
`memB_singleton_self` gets its bound side from `lt_succ_self` and
`eq_of_memB_singleton` gets it from `lt_bound_of_memB`, both free.

The equation is still what is proved first, because `card_singleton` needs
`memB (singleton a) k = false` at every `k < a` and no one-way rule can produce
a `false`. The prelude has no `Nat.ne_of_lt`, so the disequality that
`Nat.beq_eq_false_of_ne` consumes is built in place from `Nat.lt_irrefl`.

### 3. `exists_memB_of_card_pos` is a search, and its converse ships with it

There is no choice principle here, so the witness is computed: decide
`allBelow (fun k => notB (memB s k)) (bound s)`. A `false` verdict goes to
`Nat.Finset.allBelow_false_witness`, whose index is re-introduced unchanged
after `notB (memB s k) = false` is read back as membership. A `true` verdict
says every index below the bound is a non-member, so
`Nat.countRange_eq_zero_of_all_false` collapses `card s` to `zero` and the
positivity hypothesis becomes `Lt zero zero`.

The bound is the carrier's own `bound s`, which is the sharp one:
`lt_bound_of_memB` already says nothing outside it can be a member.

`Nat.Finset.card_pos_of_memB` is landed beside it, and is much cheaper — the
witness is handed in, so there is no search at all. **Hall's induction needs
both directions**: this one to refute membership in the `card s = 0` branch,
the search to produce an index in every other branch. Shipping one without the
other would have looked complete and been half a shelf.

### 4. Hall's base case is stated in necessity's vocabulary

`Nat.Hall.exists_isMatching_singleton` takes `HallCondition (singleton a) nb`
and returns `Exists (fun f => IsMatching (singleton a) nb f)` — the same three
constants `Nat.Hall.hallCondition_of_isMatching` uses, so the eventual `Iff` is
a composition and not a restatement. A test asserts that against the **rendered
types read out of the kernel**, and asserts the base case does *not* mention
`Nat.Finset.range`: a base case phrased over `range 1` would be equally
axiom-free, equally green under the footprint sweep, and useless for an
induction on an arbitrary `Nat.Finset`.

The content of the base case is not the combinatorics. `HallCondition` is a
COUNTING statement — at `t := singleton a` it says only
`1 ≤ card (unionOver nb (singleton a))` — and the whole proof is turning that
count back into a value. `Nat.lt x y` is `Nat.le (succ x) y` by δ and
`card_singleton` lands on `succ zero` exactly, so the count IS a positivity
statement with no bridging lemma; then `exists_memB_of_card_pos` produces the
value, `memB_unionOver_elim` produces an index of the singleton at which it is
a member, and `eq_of_memB_singleton` identifies that index as `a`. The matching
is the constant function; injectivity needs no hypothesis about the value at
all, because every index of a singleton is `a`.

### 5. `isMatching_congr` is landed now, before its consumer

A matching depends only on the index set's MEMBERS, never on its stored bound.
This is the index-set twin of `memB_unionOver_congr` and it is needed for the
same reason: Hall's inductive step builds its matching on
`union t (sdiff s t)`, which has the same members as `s` and a different stored
bound. Unlike `card_unionOver_congr` it needs no counting at all — both
`IsMatching` conjuncts mention the index set only in hypothesis position, so
the proof composes the pointwise equation with each incoming membership proof.

## What landed

Thirteen declarations, all axiom-free, `3,093 → 3,106`:

| name | kind |
| --- | --- |
| `Nat.Finset.empty` | Definition |
| `Nat.Finset.memB_empty` | Theorem |
| `Nat.Finset.card_empty` | Theorem |
| `Nat.Finset.memB_singleton` | Theorem |
| `Nat.Finset.memB_singleton_self` | Theorem |
| `Nat.Finset.eq_of_memB_singleton` | Theorem |
| `Nat.Finset.card_singleton` | Theorem |
| `Nat.Finset.card_eq_zero_of_no_memB` | Theorem |
| `Nat.Finset.card_pos_of_memB` | Theorem |
| `Nat.Finset.exists_memB_of_card_pos` | Theorem |
| `Nat.Hall.isMatching_congr` | Theorem |
| `Nat.Hall.exists_isMatching_of_card_le_zero` | Theorem |
| `Nat.Hall.exists_isMatching_singleton` | Theorem |

## What did NOT land, and the obstruction, sized

**Hall's sufficiency for an arbitrary index set is NOT proved.** No
`Nat.Hall.exists_isMatching_of_hallCondition` and no marriage `Iff` exists.

The textbook induction is on `card s`, and its step splits on whether some
proper non-empty `t ⊆ s` is *critical* (`card (unionOver nb t) ≤ card t`).
`Nat.strongInduction` (ADR-1614) supplies the recursion and
`Nat.Finset.existsSubset_of_search` / `forallSubset_of_search` supply the
split. The obstruction is **inside the search's own contract**:

```
Nat.Finset.forallSubset_of_search : ∀ P n,
  (∀ u v, (∀ i, memB u i = memB v i) → P u = P v) →     ← this premise
  allBelow-style search exhausted → ∀ t, bound t ≤ n → P t = false
```

The searched predicate must be **congruent under pointwise membership**. Every
other conjunct of the critical test is fine — `card` is congruent by
`card_congr_of_memB`, `card (unionOver nb ·)` by `card_unionOver_congr`. What
is not congruent is the conjunct spelling `t ⊆ s`, and every way of writing it
is missing its lemma. Measured with a `shape_search` binary rebuilt at this
lane's HEAD (3,106 declarations):

| operator | every lemma about it in the tree |
| --- | --- |
| `Nat.Finset.subsetB` | `card_le_of_subsetB` — **that is all**: no intro rule, no reflection to pointwise membership, no congruence |
| `Nat.Finset.inter` | `card_union_add_card_inter` — **that is all**: no `memB_inter` |
| `Nat.Finset.allBelow` | `allBelow_of_all_true`, `allBelow_true_at`, `allBelow_false_witness` — its three original laws, no congruence |

`subsetB` is doubly bad here: it loops over `bound t`, so its value depends on
the searched set's stored bound, which is exactly what the congruence premise
forbids.

The route out that this lane sized but did not build is to spell inclusion over
a **fixed** bound — `allBelow (fun i => notB (memB t i) || memB s i) (bound s)`
— which is congruent in `t` because the loop bound does not depend on `t`, and
which is a genuine inclusion for the sets the search actually produces
(`existsSubset_of_search` returns `t` with `bound t = bound s`, so nothing can
be a member above `bound s`). That needs **one** new lemma:

```
Nat.Finset.allBelow_congr : ∀ f g n, (∀ i, f i = g i) →
  Eq Bool (allBelow f n) (allBelow g n)
```

which is a decision on `allBelow f n` with `allBelow_true_at` /
`allBelow_of_all_true` on the `true` side and `allBelow_false_witness` plus a
refutation of the other loop on the `false` side. Everything else in the step
(the two `HallCondition` transports, the disjointness of the two matchings'
images, `card (sdiff s t) < card s`) is bookkeeping over lemmas that exist —
`card_le_card_unionOver_sdiff_add`, `card_le_card_sdiff_add`,
`memB_sdiff_elim`, `isMatching_union`, and now `isMatching_congr` — but it is
several hundred lines of kernel term per branch, and it is not sized as one
lemma.

**So: the single missing statement is `Nat.Finset.allBelow_congr`, and after it
the step is bounded work rather than a blocked one.** That is a materially
different position from the previous three ADRs, each of which named an
obstruction that was a new primitive.

## Mutation table

Every row RUN, none predicted. Restored byte-for-byte after each; `git status`
clean.

| # | mutant | kernel verdict | tests killed (of 7 selected) |
| --- | --- | --- | --- |
| 1 | `memB_singleton`'s statement: `beq i a` → `beq a i` (a wrong singleton predicate) | **REJECTED**, `TypeMismatch` | **7** — the shared prelude no longer builds, so the whole selected set dies |
| 2 | `Nat.Finset.empty`'s stored predicate: `fun _ => false` → `fun _ => true` | **ADMITTED**; the axiom-footprint sweep stays green | **1** — `finset_singleton_tests::empty_has_no_members_and_bound_zero`, on the `range 0` assertion |
| 3 | the base case's `And` split: `and_left`/`and_right` exchanged (one branch swap in the sufficiency proof's split) | **REJECTED**, `TypeMismatch` | **7** — same mechanism as row 1 |

The selected set was
`nat_prelude::finset_singleton_tests:: + nat_prelude::hall_sufficiency_tests:: + nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`,
7 tests.

Row 2 is the one worth reading. It is the case the module doc predicts and the
one CLAUDE.md warns about: **the trusted gate cannot tell you a `Definition` is
wrong.** `mk (fun _ => true) 0` has the type `Nat.Finset`, is admitted, has an
empty axiom footprint, and passes every sweep in this repository — because
`memB` truncates at the bound, it even has the same members. Exactly one test
notices, and it notices through the assertion that `empty` is *not* def-eq to
`Nat.Finset.range 0`, which was written for that reason and not as decoration.

Rows 1 and 3 say the opposite thing about the theorems: for those the kernel IS
the mutation detector, and the kill count is uninformative because a rejected
declaration takes the shared prelude build down with it. That is the expected
shape in this module and it is recorded, not dressed up as coverage.

## Consequences

- `Nat.Finset` has an empty set, a usable singleton, and can travel from a
  count back to a member. Anything doing induction over a `Nat.Finset` — not
  just Hall — was previously stuck at the same place.
- Hall's sufficiency has a base case and an empty case, in necessity's
  vocabulary. What is missing is the step, and the next lane should land
  `Nat.Finset.allBelow_congr` first and then build the critical-set predicate
  over the fixed bound `bound s`.
- `Nat.Finset.empty` is now a name a future lane can collide with. It is a
  `Nat.Finset`-valued constant; `Nat.Subsets.empty` (a `Nat -> Bool`) is a
  different thing in a different namespace.
- The claim "Hall's marriage theorem is proved" remains FALSE and the ledger
  says so in both new facts.
