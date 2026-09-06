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
no transport at all. Playfair did **not** land, and sizing it produced a second finding: the
obstruction is the SHAPE of the parallel predicate, not a missing principle.
"No common point" is negative and forces uniqueness through tightness (absent
by design); parallelism stated positively -- same direction plus a WITNESSED
distinctness -- makes every Playfair obligation a polynomial identity this file
already discharges, with the identities verified and recorded in § 5.
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

### 4. `CPoint.Equiv`'s setoid laws, and a duplicate this lane created knowingly

`creal_point.rs` defines `CPoint.Equiv` and builds its reflexivity, symmetry
and transitivity inline without ever naming them; the record's `pEq` slot needs
all three as terms, so they are declared here as
`Geo.RPlane.pointRefl`/`pointSymm`/`pointTrans`.

**They are the third copies, not the first, and the check that would have said
so is one this lane initially got wrong.** `metric.rs` already declares
`Metric.CPoint.equivRefl`/`equivSymm`/`equivTrans`, with its own doc noting
"the plane prelude builds this inline and never names it". The search that
missed them looked at `CPointPrelude`'s field list — which is *not* the
authority for names under `CPoint`, because another prelude may declare into
that namespace, exactly as CLAUDE.md's kernel gotcha says. The correct search
is over the whole environment, and the gate that catches this class is
merge-hygiene guard 6 (`check-shape-duplicates.py --prebuilt`), which SKIPPED
on this host for want of a built `shape_search`.

The duplication is kept rather than removed because reuse costs more than it
saves: `build_geo_prelude` depends on `build_cpoint_prelude`, not on
`build_metric_prelude`, so citing `metric.rs`'s copies would add the whole
metric prelude to every geo build to save three one-line lemmas. The right
long-term home is `creal_point.rs` beside `CPoint.Equiv` itself, at which point
both this copy and `metric.rs`'s should be deleted. Recorded here so the next
lane finds the fact rather than making a fourth copy.

### 5. Playfair did not land — and the obstruction is the SHAPE of `parallel`, not a missing principle

`Geo.Affine` is **not** in this change. What follows is the sizing, and it
corrects a wrong first answer that is worth recording because it is the same
mistake ADR-1635 already made once and fixed.

**The wrong answer.** Define `Parallel l m := ∀ P, on P l → on P m → False`
("no common point", the classical definition, and what
`Geo.Incidence.Parallel` in this change actually is). Playfair's *uniqueness*
then needs `Parallel l m → Equiv (a*B − b*A) 0`, and the only route from a
negative hypothesis is by contradiction: assume the defect is apart from zero,
construct the intersection point, contradict disjointness. That yields
`Not (Apart (a*B − b*A) 0)`, and turning that into `Equiv (a*B − b*A) 0` is
tightness, which `creal.rs`'s `not_apart_one_of_pow_succ_eq_one` doc calls
Markov's principle and says is "neither proved nor assumed". Over ℚ the same
route works, because `Geo.Rat.eqOrNe` decides the denominator.

Stopping there and reporting "ℝ-Playfair is blocked on tightness" would have
been wrong in exactly the way ADR-1635's `apart` decision was set up to
prevent: **a negative primitive blocks, and the fix is to state the primitive
positively with a witness, not to acquire a classical principle.** Parallelism
is not "they fail to meet"; it is "they have the same direction and are
distinct", and both halves are witnessable:

```text
par l m  :=  Equiv (a*B − b*A) 0                                    -- same direction
         ∧   ∃ k, PosBound ((a*C − c*A)^2 + (b*C − c*B)^2) k        -- distinct, witnessed
```

With that shape every Playfair obligation is a polynomial identity of the kind
this file already discharges, with no case split and no new kernel machinery.
The identities are verified exactly (`Fraction` trials, 300 random tuples,
before encoding):

| obligation | route |
| --- | --- |
| `par l m → on X l → on X m → False` | `a*C − c*A = a*(A*x+B*y+C) − A*(a*x+b*y+c) − y*(a*B − b*A)` and its `b` mirror; both correction terms vanish, so the distinctness witness's own quantity is `~ 0`, refuted by its `PosBound` |
| existence, through `P` **apart from** `l` | `m := (a, b, −(a·x P + b·y P))`; then `(a*C − c*A)^2 + (b*C − c*B)^2 = (a² + b²)·e_P²`, so the witness is the product of the line's `Nondeg` and `P`'s apartness from `l` |
| uniqueness | with `D := A*B' − A'*B`, the unconditional pair `a*D = A*(a*B' − b*A') − A'*(a*B − b*A)` and `b*D = B*(a*B' − b*A') − B'*(a*B − b*A)` gives `(a² + b²)*D ~ 0`, and `Nondeg l` cancels it — the same `cancelPosBound` step `joinUnique` uses. The other two defects of `m` against `n` then come from `defectAC`/`defectBC`, **already declared in this change**, at the shared point `P` |

Note the second row: existence needs `P` **apart from** `l`, not merely
`on P l → False` — the witnessed form `∃ k, PosBound (e_P * e_P) k` — which is
the same strengthening one dimension down that `apart` is for points. That is
the residue this slice hands on, and it is a *design* item, not a blocked one.

So the honest statement is: **`Geo.Affine` did not land for budget, not for
mathematics.** It needs a record with `par` as a primitive field (or as a
per-model positive definition), a witnessed point-apart-from-line relation, and
two instances; the ℝ instance's algebra is the three rows above and reuses
`defectAC`, `defectBC`, `cancelPosBound` and `onOfDefects` unchanged. What this
change ships toward it is `Geo.Incidence.Parallel` (the classical negative
predicate), `parallel_symm`, and `parallel_irrefl` — the last being the only
derived theorem here that consumes an *existence* axiom, since a line is not
parallel to itself precisely because `twoPoints` puts a point on it.

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
- **A negative control over `CReal` must not be a `def_eq` refutation between
  two arithmetic terms.** Measured here, and it cost a verification cycle: the
  first version of the `distSq` pin asserted
  `!def_eq(distSq P Q, sum-of-coordinates form)` and the first `onRaw` pin
  asserted `!def_eq(correct pairing, swapped pairing)`. Both ran past **ten
  minutes** in `--release` on an otherwise-green run and were killed, while the
  identical ℚ pins in the same file finish in seconds. When congruence on
  `CReal.add`/`CReal.mul` fails, the kernel unfolds both sides into `CReal.mk`
  with their regularity proofs and compares sequences under a binder; refuting
  at `CReal.Equiv` is worse still, because `Equiv` unfolds to a `∀ n` over
  `Rat` arithmetic. The rule the rewritten pins follow: **over `CReal`, assert
  `def_eq` only where it SUCCEEDS** (δ/ι plus congruence, fast), and do the
  discriminating half by comparing the stored `Definition` value as an interned
  `ExprId` — exact, `O(1)`, and strictly stronger than `def_eq` for a shape
  claim because it separates shapes that are denotationally equal. CLAUDE.md
  already says a pathological test is worth deleting *including a pathological
  negative control*; what this adds is that over the constructive reals the
  pathology is the default rather than the exception.

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
