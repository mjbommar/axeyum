# ADR-1635: incidence geometry needs apartness in exactly one axiom, and the ℚ ring normalizer could not cancel

Status: proposed
Date: 2026-09-05
Lane: `incidence-geometry`
Roadmap: W3-8 (synthetic incidence geometry with the coordinate plane as a model)

Index-summary: `Geo.Incidence` lands Hilbert's three incidence axioms as a
21-field record over **two** carriers, through the ADR-1578 `declare_record`
spine at `Sort 2` with the ADR-1595 setoid discipline — each carrier its own
equivalence, the incidence relation a congruence field for each, no `funext`
and no `Quot.sound`. The design decision the brief asked to be measured is
whether "distinct" can be `pEq P Q → False`, and the answer is **no, but only
one axiom cares**: `joinUnique` is the sole axiom that CONSUMES distinctness
(`joinExists`, `twoPoints` and `triangle` only produce it), and over `CReal` a
consumer has to divide by `distSq P Q`, which is `CReal.inv`, which is
`PosBound`-indexed rather than negation-indexed — the same wall
`CPoint.collinear_of_area_zero` already documents. So `apart` is a **field**
with three laws, and each model supplies its own notion; over ℚ that notion is
the negation, and it is usable there because ℚ's equality is the kernel's own
`Eq` and its order is decidable. Five theorems are derived once over an
arbitrary `I : Geo.Incidence`, including `distinct_lines_meet_once`, which IS
"two distinct lines meet in at most one point". The **unbudgeted** finding is
in the ℚ model: `ring::rat` could not prove a single one of the coordinate
identities, because it had neither `cancel_pairs` (ported from `ring::int`;
every determinant identity is an assertion that opposite monomials annihilate)
nor any way to drop the `Item::Num(0)` that `scale_item` emits for `x * 0`
(so `a*0 + b*0 + c` normalized to three items against `c`'s one). Both passes
are now in `ring::rat::Problem::cancel_pairs`, with three matched tests, one of
them a negative control that dies if the pass stops comparing factor lists.
Index-status: proposed

## Context

Roadmap W3-8 asks for synthetic incidence geometry as a record, with the
rational coordinate plane and the real plane `CPoint` as models. Before this
lane the search index had **zero** declarations named incidence, line or
through — measured with a freshly built `shape_search`
(`declarations=4379`, positive control `--name-like collinear` FOUND 5,
`--name-like incidence --expect-absent` ABSENT with the positive control
printing 4379).

What did exist is the ℝ-plane module `creal_point.rs`, which the search index
does not cover: `CPoint.Collinear` (an existential through `lerp`),
`CPoint.cross`/`crossV`, `CPoint.NonCollinear` (a **witnessed** predicate,
`PosBound (cross²) k`), and `CPoint.collinear_of_area_zero`, whose hypothesis
is `PosBound (distSq A B) k` and whose own doc explains at length why the
negation will not do.

## Decision

### 1. `apart` is a field, not `¬ pEq`

Hilbert I.1 is "two **distinct** points lie on exactly one line". Spelling
"distinct" as `pEq P Q → False` works over ℚ and fails over ℝ, and the failure
is asymmetric in a way worth stating precisely, because it decides where the
abstraction goes:

| axiom | uses distinctness how | negation enough? |
| --- | --- | --- |
| `joinExists` (I.1a) | produces a line from it | yes — the join is computed from coordinates and never divides |
| `joinUnique` (I.1b) | **consumes** it | **no** over ℝ — the consumption is a division by `distSq P Q` |
| `twoPoints` (I.2) | produces it | yes |
| `triangle` (I.3) | produces it | yes |

Only the ℚ row of that table is **measured**: every entry in it is a
declaration this lane admitted. The ℝ column is **analysis, not measurement**
— no ℝ² instance is built — and it rests on two things that are measured, both
in `creal_point.rs`: `CPoint.collinear_of_area_zero` takes
`PosBound (distSq A B) k` and its own doc explains at length why the negation
will not do, and `CReal.inv` consumes a `PosBound` rather than an `Apart` (its
doc gives the reason: an `Apart`-indexed inverse would have to eliminate a
disjunction into a `Type`, which `Or.rec` does not permit). A later lane
building the ℝ instance should re-derive the "yes" entries rather than inherit
them from this table.

So exactly one axiom forces the choice. `Geo.Incidence` therefore carries

```text
apart      : point → point → Prop
apartNe    : ∀ P Q, apart P Q → pEq P Q → False
apartSymm  : ∀ P Q, apart P Q → apart Q P
apartCongr : ∀ P' P Q, pEq P P' → apart P Q → apart P' Q
```

and each model supplies its own. Over ℚ: `Apart P Q := (P = Q) → False`, and
`apartNe` is literally the identity function because `Apart` unfolds to its
statement. An ℝ² model would supply `∃ k, CReal.PosBound (CPoint.distSq P Q) k`.
`apartNe` is what keeps the field honest: without it `apart` could be `True`
and every axiom would hold vacuously.

### 2. Line equality is extensional, and that is what makes the model cheap

`Geo.QLine.Equiv l m := ∀ P, (on P l → on P m) ∧ (on P m → on P l)` makes
reflexivity, symmetry and transitivity free and `onLine` an `And.left`. The
alternative — proportionality of coefficient triples — needs a case split on
which coefficient is nonzero *three times* (once per conjunct) just to prove
transitivity. With the extensional relation the entire cost of the model
collapses into `joinUnique`, and `joinUnique` factors through **one** lemma.

### 3. The rational model factors through one pivot lemma and one join

```text
Geo.QPlane.onPivot : ∀ u v w U V W s t,
    (u = 0 → False) → u*V = v*U → u*W = w*U →
    u*s + v*t + w = 0 → U*s + V*t + W = 0
```

proved from the unconditional ring identity

```text
u*(U*s + V*t + W) = U*(u*s + v*t + w) + ((u*V)*t + u*W) + -(((v*U)*t) + w*U)
```

by substituting the two proportionality hypotheses into the right-hand side
(which turns the last two summands into a term and its negation) and the
incidence hypothesis into the first, then `Rat.mul_eq_zero` against `u ≠ 0`.
`Geo.QPlane.onOfProp` wraps it in the `a ≠ 0 ∨ b ≠ 0` case split and **uses
the same lemma in both branches** — the `b` branch is `onPivot` with
`(u,v,s,t)` and `(U,V)` swapped, so the second case costs three `ring`
rearrangements rather than a second proof.

The proportionality itself is `Geo.QPlane.joinProp`: *any* line through `P` and
`Q` is proportional to the explicit join

```text
join P Q := ⟨y Q - y P,  x P - x Q,  y P * x Q - x P * y Q⟩
```

with **no non-degeneracy hypothesis at all**. Its three relations are three
unconditional ring identities with the two incidence left-hand sides `e₁`, `e₂`
added as summands on either side:

```text
a*B + e₂ = b*A + e₁      a*C + qy*e₁ = c*A + py*e₂      b*C + px*e₂ = c*B + qx*e₁
```

`joinUnique` then routes both lines through `join P Q` in both directions —
four `onOfProp` applications, one of which is where distinctness is spent
(`Geo.QPlane.joinNondeg` turns `P ≠ Q` into the join's non-degeneracy, through
`Geo.QPoint.ext`).

`twoPoints` costs a case split only for the FIRST point: the second is the
first plus the direction `(-b, a)` (`Geo.QPlane.shift`), whose incidence is one
ring identity (the `a*b` terms cancel) and whose apartness needs `Nondeg`
alone. `Rat.inv` and `Rat.mul_inv_cancel_of_ne_zero` appear exactly once, in
`Geo.QPlane.basePoint`.

## The unbudgeted finding: `ring::rat` could prove none of these

Every ℚ identity above was declined by the producer, for two independent
reasons, and neither was visible from its documentation until the goals were
put to it:

1. **No `cancel_pairs`.** `Item::key` sorts by `(is_num, factors, sign)`, so a
   monomial and its negation are adjacent after `sort_items` — and then nothing
   merged them. The module doc said, verbatim, "None of the five ℚ targets
   produce an `x + (-x)` summand pair, so it was not built." Every identity in
   this lane produces nothing else: each one asserts that a determinant
   expansion collapses.
2. **No way to drop a `Num(0)`.** `scale_item` emits `Item::Num(0)` for every
   `x * 0`, and the additive normalizer never merges two `Num`s. So
   `a*0 + b*0 + c` normalized to three items and `c` to one, and the producer
   declined `NotAnIdentity` on a ring identity. Every `Geo.QPlane` statement at
   a point with a zero coordinate — which is every statement about the triangle
   `(0,0), (1,0), (0,1)` and about `basePoint` — has that shape.

Both passes now live in `ring::rat::Problem::cancel_pairs`, the first ported
from `ring::int::Problem::cancel_pairs` with the same adjacent-pairs-only
completeness bound, the second new. Three matched tests were added to
`ring/rat/tests.rs`: two positives (the bare `x*y + -(y*x) = 0`, and
`joinOnLeft`'s four-atom determinant identity written out with no geometry in
it) and one **negative control**, `x*y + -(x*x) = 0`, which must still decline
`NotAnIdentity` — it dies if the pass ever stops comparing factor lists.

This is the ADR-0601 producer discipline working as designed: the geometry did
not get a bespoke proof, the producer got a capability, and the capability is
guarded by a control that can fail.

## Consequences

- One record now serves both planes, so an ℝ² model is an instance rather than
  a parallel development, and the five derived theorems come free with it.
- `ring::rat` is stronger for every future ℚ consumer, not just this one.
- The ℝ² instance is **not** landed by this lane; the obstruction is sized in
  the lane status file rather than guessed at here.

## Alternatives considered

- **`distinct := pEq P Q → False` in the record.** Rejected: it makes the
  record unusable at `CReal` for `joinUnique` alone, and there is no way to
  weaken one axiom of a record without weakening the record.
- **Proportional line equality.** Rejected: transitivity needs the nonzero
  case split three times, and the extensional relation needs it zero times.
- **A bespoke ℚ algebra module instead of extending `ring::rat`.** Rejected by
  ADR-0601: a producer that declines a goal in its own fragment is a producer
  to fix, not to work around.
