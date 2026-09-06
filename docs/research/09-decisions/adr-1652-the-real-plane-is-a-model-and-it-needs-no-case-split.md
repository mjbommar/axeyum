# ADR-1652: the real plane IS a model of `Geo.Incidence`, and it costs less than the rational one because it never decides which coefficient is nonzero

Status: proposed
Date: 2026-09-06
Lane: `real-incidence`
Roadmap: W3-8 (synthetic incidence geometry with the coordinate plane as a model), second slice

Index-summary: `Geo.rplane : Geo.Incidence` lands — the ℝ² model ADR-1635
predicted, shaped `apart` for, and did not build. Point apartness is
`∃ k, CReal.PosBound (CPoint.distSq P Q) k` and line non-degeneracy is
`∃ k, CReal.PosBound (a*a + b*b) k`; both are witnessed, neither is a negation.
The finding ADR-1635 did not predict is that the ℝ model is **cheaper** than the
ℚ one, not dearer: `Geo.qplane` needs ℚ's decidable equality twice
(`Geo.QLine0.nondeg_or` for the pivot, and again to produce a line's first
point), and the ℝ model needs **no case split anywhere**, because both of its
divisions are by a sum of two squares that the hypothesis already witnesses as
positive — `distSq P Q` from `Apart`, `a*a + b*b` from `Nondeg`. The pivot never
has to know which of `a`, `b` is large. `joinUnique` routes through one new
six-variable identity (`Geo.RPlane.pivotAB`) whose second factor is
**definitionally** `CPoint.distSq P Q`, so `Apart`'s own witness cancels it with
no transport at all. Playfair did **not** land, and the obstruction is sized and
recorded: uniqueness over ℝ needs `Not (Apart x 0) → Equiv x 0` (tightness),
which `creal.rs` documents as absent by design.
Index-status: proposed

## Context

ADR-1635 built `Geo.Incidence` as a 21-field record and `Geo.qplane` as its
first model. It carried `apart` as a field of its own rather than deriving
distinctness from `pEq`, on an argument about a model it did not build:

> Only the ℚ row of that table is **measured** … The ℝ column is **analysis,
> not measurement** — no ℝ² instance is built.

This lane builds the ℝ² instance. The argument survives contact; one of its
side-conclusions does not.

The brief predicted the shape of the work: `joinUnique` "must route through
`CPoint.collinear_of_area_zero`, which takes `PosBound (distSq A B) k`, so
`apart` must be `∃ k, PosBound (distSq P Q) k` and the pivot cancels through
`CReal.inv` rather than `Rat.mul_eq_zero`". The first half is right and is what
landed. The second half — routing through `collinear_of_area_zero` — turned out
to be unnecessary: that theorem's job is to produce a `lerp` witness, and
`joinUnique`'s conclusion (extensional line equality) is a `Prop` that needs no
witness, so a direct polynomial route is both shorter and avoids the `Exists`
elimination `collinear_of_area_zero` pays for.

## Decision

### 1. The two witnessed predicates, and why they are the same idiom

```text
Geo.RPlane.Apart  P Q := ∃ (k : Nat), CReal.PosBound (CPoint.distSq P Q) k
Geo.RLine0.Nondeg l   := ∃ (k : Nat), CReal.PosBound (a l * a l + b l * b l) k
```

Both are `Prop`-valued existentials over a `Nat`, so neither can hand a
`CReal`-valued function its modulus directly — but neither has to. Every place
this model divides, the conclusion is itself a `Prop`, so `Exists.rec`
eliminates into it and the `k` is in scope exactly where `CReal.inv` needs it.
`Geo.RPlane.twoPointsRaw` is the shape that makes this explicit: it takes the
`k` as an ordinary argument and `Geo.RPlane.twoPoints` does the elimination, so
the construction of the two points is written once against a bound `k` rather
than inside a nested eliminator.

The negation form is not merely inconvenient here, it is inert:
`(Equiv (a*a + b*b) 0) → False` type-checks perfectly well as a non-degeneracy
predicate and constructs no modulus, so `CReal.inv` cannot consume it. That is
mutation 1 below, and it is pinned by
`real_nondegeneracy_is_a_positive_bound_witness_not_a_negation`.

### 2. **The finding: no case split, and that is why ℝ is cheaper than ℚ**

`Geo.qplane` uses ℚ's decidable equality in exactly two places, and both are
case splits on *which* of a line's two leading coefficients is nonzero:
`Geo.QLine0.nondeg_or` (feeding `Geo.QPlane.onOfProp`'s pivot) and
`Geo.QPlane.basePoint` (producing a line's first point). Neither is available
over ℝ — `a² + b² > 0` does not constructively say which summand is large, and
`Or.rec` could not eliminate into a `CPoint` if it did.

The ℝ model does not need either, because it divides by a different thing:

| divided by | supplied by | consumed at |
| --- | --- | --- |
| `distSq P Q` | `Apart P Q` | `Geo.RPlane.joinUnique`, once |
| `a*a + b*b` | `Nondeg l` | `Geo.RPlane.onOfDefects`, `Geo.RPlane.twoPointsRaw` |

Both are sums of two squares that the *hypothesis itself* witnesses as positive.
A line's first point is `(−a*c/N, −b*c/N)` with `N := a*a + b*b` — one formula,
no branch — and its second is that plus the direction `(−b, a)`, whose squared
distance from the first is `N` again, so the two points are apart **by the
line's own non-degeneracy witness with nothing new to prove**.

This inverts the expectation the brief carried in ("the other three axioms are
cheaper over ℝ than ℚ" — in fact all four are, and `twoPoints` most of all).
It is the general lesson worth exporting: **a witnessed positivity hypothesis on
a sum of squares is strictly more usable than a decidable disequality on each
summand**, because it divides without branching. Where a ℚ development reaches
for `eqOrNe`, ask first whether the quantity actually divided by is the sum.

### 3. `joinUnique`: three defects, one division

Writing `l = (a,b,c)`, `m = (A,B,C)` and the three *defects*

```text
dAB := a*B − b*A     dAC := a*C − c*A     dBC := b*C − c*B
```

two lines are the same line exactly when all three vanish. They are established
in order, and only the first costs a division:

1. `Geo.RPlane.pivotAB`, over six bare reals — from `a*u + b*v ~ 0` and
   `A*u + B*v ~ 0`, conclude `(u*u + v*v) * dAB ~ 0`, by the unconditional
   identity
   `(u² + v²)(a*B − b*A) = (B*u − A*v)(a*u + b*v) + (a*v − b*u)(A*u + B*v)`.
   At `u := x P − x Q`, `v := y P − y Q` the left factor is **definitionally**
   `CPoint.distSq P Q` — `distSq` is `dot` of `sub` with itself and both unfold
   — so `Apart P Q`'s witness is passed to `Geo.RPlane.cancelPosBound`
   verbatim, with no `Equiv` transport in between. That defeq is load-bearing
   enough to be pinned on its own
   (`dist_sq_unfolds_to_the_coordinate_difference_squares`).
2. `Geo.RPlane.defectAC` / `defectBC` — the other two follow from `dAB ~ 0` and
   the incidence at **one** point, no further division:
   `a*C − c*A = a*E₁ − A*e₁ − q*dAB` and `b*C − c*B = b*E₁ − B*e₁ + p*dAB`.
3. `Geo.RPlane.onOfDefects` — with all three zero and `l` non-degenerate,
   `(a² + b²)(A*x + B*y + C) = (a*A + b*B)(a*x + b*y + c) + (a*y − b*x)*dAB +
   a*dAC + b*dBC`, and `Nondeg l` cancels the left factor.

The two directions of extensional line equality are the same lemma twice:
`Geo.RPlane.defectSwap` turns a defect into its opposite by multiplying through
by `−1`, so nothing is proved twice.

Every polynomial identity above is emitted by `creal_point.rs`'s `rn_ring_proof`
and none is written by hand. The largest has 14 monomials on the right, which is
why no staging was needed.

### 4. `CPoint.Equiv`'s setoid laws were missing

`creal_point.rs` defines `CPoint.Equiv` and never states its reflexivity,
symmetry or transitivity; the record's `pEq` slot needs all three. They are
declared here (`Geo.RPlane.pointRefl`/`pointSymm`/`pointTrans`) rather than in
`creal_point.rs`, which this lane was told not to edit. If a third consumer
appears they belong upstream.

### 5. Playfair did not land, and the obstruction is not budget

`Geo.Affine` — parallelism as "no common point", with existence and uniqueness
of the parallel through an outside point — is **not** in this change. Existence
is easy in both models (the parallel through `P` to `(a,b,c)` is
`(a, b, −(a·x P + b·y P))`, and it inherits `(a,b)`'s non-degeneracy). Uniqueness
is where the two models part company:

- Over ℚ it is reachable: two lines through `P` both disjoint from `l` must have
  coefficient vectors proportional to `l`'s, because otherwise the explicit
  intersection point `((b*C − B*c)/(a*B − b*A), (A*c − a*C)/(a*B − b*A))` exists
  and contradicts disjointness — and `Geo.Rat.eqOrNe` decides the denominator.
  It needs a new file (this lane must not edit `qplane.rs`) and it needs
  `Geo.QPlane.onOfProp` re-exported through it; it did not fit this slice.
- Over ℝ it is **blocked on a proposition this kernel does not have**. The same
  argument gives only `Not (CReal.Apart (a*B − b*A) 0)`; turning that into
  `Equiv (a*B − b*A) 0` is tightness, and `creal.rs`'s
  `not_apart_one_of_pow_succ_eq_one` doc states the position in the open:
  "the converse (tightness, `Not (Apart x y) → Equiv x y`) is Markov's
  principle, *neither proved nor assumed* anywhere in this development … a
  genuinely different (classically-flavoured) proposition, not a missing lemma
  this file failed to look up."

  That is a claim about *this* route, not about ℝ-Playfair, and the honest
  statement of the residue is: **either** find a route to
  `Parallel l m → Equiv (a*B − b*A) 0` that never passes through a negation
  (none is known to this lane), **or** prove tightness for `CReal.Apart`, which
  is constructively available for Cauchy reals — the negation of the two `lt`s
  reduces to a rational-level decision at each index — but is a development of
  its own and is not what `creal.rs`'s doc says it is. Deciding which of those
  two is right is the next slice's question, and it should not be settled by
  quoting the doc comment above, which asserts more than the Cauchy construction
  forces.

## Consequences

- `Geo.Incidence` now has **two** models with structurally different equalities
  (`Eq` on ℚ points, `CPoint.Equiv` on ℝ points) and different apartness
  notions. Its five derived theorems instantiate at both, which is the payoff
  of proving them over an arbitrary `I : Geo.Incidence` and is pinned by
  `the_derived_theorems_instantiate_at_the_real_model`.
- The record's `apart` field is now justified by measurement rather than
  analysis: `Geo.rplane`'s `apart` slot is `∃ k, PosBound (distSq P Q) k`, and
  the mutation that replaces `Nondeg`'s witness with a negation is run below.
- `geo_tests.rs`'s every-declaration sweep is environment-derived, so the 41 new
  names had to be added to the handle list; the vacuity floor moves 70 → 110.
- `creal_point.rs`'s `rn_ring_proof` is now used from outside `creal_point.rs`
  for the first time. It is `pub(crate)` and needed no change.

## Alternatives considered

- **Route `joinUnique` through `CPoint.collinear_of_area_zero`**, as the brief
  suggested. Rejected on measurement of the shape, not on difficulty: that
  theorem produces a `lerp` witness (an `Exists` over `CReal`), and
  `joinUnique`'s conclusion is a `Prop` that never needs one, so the witness
  would be constructed and immediately discarded. The direct polynomial route
  is three small lemmas over bare reals with no point in them at all, which also
  makes them reusable by an affine layer later.
- **State non-degeneracy as `CPoint.NonCollinear`-style `PosBound (cross²) k`.**
  Rejected: `cross` is a three-point determinant and a line has no third point;
  `a² + b²` is the quantity actually divided by.
- **Give `Geo.RLine` a normalized representative** (say `a² + b² ~ 1`) so line
  equality could be `Eq` on coefficients. Rejected: normalizing needs
  `CReal.sqrt` of the witnessed-positive norm and then an inverse, i.e. two more
  divisions and a congruence obligation per coefficient, to buy an equality the
  extensional one already gives for free. `Geo.qplane` made the same call for
  the same reason.
