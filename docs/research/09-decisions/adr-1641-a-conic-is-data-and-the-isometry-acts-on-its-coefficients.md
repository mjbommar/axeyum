# ADR-1641: A conic is data, and the isometry acts on its coefficients

Status: accepted
Date: 2026-09-05
Index-summary: `CPoint.Conic` is a six-field inductive over `CReal`, not a predicate on points, and `CPoint.Conic.rotate`/`.reflect`/`.translate` are total `Conic → Conic` functions. That choice turns "the discriminant classification is isometry-invariant" from a statement about sets of points into an `Equiv` between two `CReal`s, which the existing `rn_ring_proof` producer discharges flat. The classification's three predicates are `lt`/`Equiv`/`lt` against zero, they are pairwise exclusive and each is inhabited, and they are NOT exhaustive — deciding the sign of a general constructive real is not constructive, and this ADR records that as a permanent boundary of the classification rather than a gap to close.
Index-status: accepted

## Context

Roadmap item W3-9 asks for conics on the real plane: the six-coefficient
family, the discriminant classification, circles as an instance, invariance
under the isometries `creal_point/isometry.rs` already builds, and the
standard forms.

The plane `CPoint` already carries `OnCircle`, `Collinear`, `Isometry` with
`translate`/`rotate`/`reflect` instances, and `isometry_preserves_dot`. Every
one of those predicates is written the same way: a proposition **about
points**, with the geometric object appearing only as parameters
(`OnCircle P O r2` names the centre and the squared radius, not a "circle").
That works for a circle, which is two parameters. A conic is six, and the
question W3-9 actually asks — does an isometry preserve the classification? —
is a question about a map from six-tuples to six-tuples.

The retrieval check ran first: `shape_search --include-constructed
--name-like conic` over 4,402 declarations returns ABSENT, with the
same-kind positive control (`--name-like oncircle --kind definition`)
returning `CPoint.OnCircle`. Nothing about conics existed.

Three things had to be decided before any of it could be written.

## Decision

### 1. A conic is a one-constructor inductive, not a predicate

`CPoint.Conic` is `mk : CReal → CReal → CReal → CReal → CReal → CReal →
Conic` with six large-elimination projections, and
`CPoint.OnConic K P := Equiv (Conic.eval K P) CReal.zero`.

The consequence that matters: the isometry action is a **total function on
the data**. `CPoint.Conic.rotate c s K`, `.reflect c s K` and `.translate T K`
each compute the transformed coefficients, so

- the correspondence between the two descriptions of the same zero set is a
  theorem with a proof (`onConic_rotate_iff` and its two siblings), not an
  identification by fiat; and
- the invariance claim is `Equiv (discriminant (rotate c s K))
  (discriminant K)` — one equation between two reals, and therefore inside
  what `rn_ring_proof` decides.

Had `OnConic` been a six-parameter predicate with no carrier, "the rotated
conic" would have had no name to be the subject of an equation, and the
invariance statement would have had to quantify over points. That form is
strictly weaker (it says the two zero *sets* agree, not that the two
*classifications* agree) and it is the form that cannot be proved by ring
normalization at all.

### 2. `4` is spelled out; it cannot be an opaque scalar

`CPoint.Scalar.four := two + two`, and every ring-normalizer mirror writes it
as four `RnExpr::One`s.

This is forced, not stylistic. Writing the discriminant as `B² − t·AC` for an
opaque `t` makes the invariance identity **false**: matching coefficients of
`t` in

```
B'² − t·A'C'  =  (B² − t·AC)(c² + s²)²
```

requires `A'C' = AC(c²+s²)²`, which is wrong — `A'C'` carries `A²`, `B²` and
`C²` monomials that only cancel against the `t`-free part when `t` is
literally `4`. Checked before the proof was attempted. Had it not been, the
normalizer would have failed with "the two sides have different normal
forms", an assertion that says nothing about which side is wrong or why.

### 3. The classification is exclusive and inhabited; it is not exhaustive

`IsEllipseType K := lt (discriminant K) zero`,
`IsParabolaType K := Equiv (discriminant K) zero`,
`IsHyperbolaType K := lt zero (discriminant K)`.

**There is no trichotomy theorem here and there will not be one.** Deciding
the sign of a general constructive real is not constructive; `CReal.lt`
carries a rational gap as data and no `Conic → Or …` can produce that gap for
an arbitrary conic. This is the same boundary `creal_point/isometry.rs`
records for the `±` choice in the isometry classification, and it is a
property of the carrier, not a missing lemma.

What replaces exhaustiveness, and what this ADR requires of any future
classification predicate in this development:

- **Exclusivity, proved.** `Conic.not_ellipse_and_parabola`,
  `not_ellipse_and_hyperbola`, `not_parabola_and_hyperbola` — each `∀ K,
  Pred₁ K → Pred₂ K → False`. Without them the three predicates could all be
  `True` and every theorem below would still hold.
- **Inhabitation, proved, one instance per class.** `Conic.ellipse`,
  `Conic.parabola`, `Conic.hyperbola` with their sign theorems, plus
  `Conic.circle_isEllipseType` and `Conic.parabolaFocal_isParabolaType`.
  Without them the three predicates could all be `False`.

A classification carrying only one of the two halves is a checker that cannot
fail in one direction, and this repository does not accept one.

The apartness the brief asks for needs no separate declaration:
`CReal.apart x y` is `Or (lt x y) (lt y x)`, so
`IsEllipseType K ∨ IsHyperbolaType K` **is** `apart (discriminant K) zero`
definitionally.

### 4. Invariance is nine theorems, not one

Three predicates crossed with three isometry generators. Each is
`transfer_pred` applied to the matching `discriminant_*` law, so each costs
about twenty lines — but stating one and asserting the other eight in prose
would be exactly the claim shape the flywheel rules forbid. The three
`is*Type_congr` transfer lemmas are declared separately so a fourth generator
costs three corollaries and no new argument.

Two asymmetries in the nine are worth recording because they are the
mathematics:

- **The rotation and the reflection get the *same* factor `(c²+s²)²`.** A
  reflection has `det M = −(c²+s²)`; the discriminant is `−4 det Q` for the
  quadratic-part matrix `Q`, which transforms as `MᵀQM`, so the sign of
  `det M` squares away. The two `discriminant_*` theorems are therefore
  identical in shape and the orientation reversal is invisible to the
  classification — which is the correct answer, since a reflection does not
  turn an ellipse into a hyperbola.
- **The translation needs no hypothesis and its proof is `Equiv.refl`.** It
  copies `A`, `B`, `C` unchanged, so the two discriminants are the same term
  after one iota step. The rotation and reflection need `c² + s² ~ 1` and the
  translation needs nothing; that difference is the whole reason the
  unconditional `discriminant_rotate` is stated separately from
  `discriminant_rotate_unit`.

### 5. Denominators are cleared, and the focus–directrix property compares squares

`Conic.ellipse a b := b²x² + a²y² − a²b²` rather than `x²/a² + y²/b² − 1`,
and `Conic.parabolaFocal p := x² − 4py` rather than `y = a x²` with focus
`(0, 1/(4a))`. `CReal.inv` is **partial** — defined only on a
`PosBound`-witnessed positive — so every appearance of it would drag a
modulus argument through statements that do not otherwise need one.

`parabola_focus_directrix` states
`distSq P (0,p) ~ (P.y + p)²`: the squared distance to the focus equals the
squared distance to the directrix `y = −p`. This is the focus–directrix
property verbatim, not a weakening — the perpendicular distance to a
horizontal line is `|y − (−p)|` and its square is `(y+p)²` with no absolute
value left to interpret — and it is `CReal.sqrt`-free, which matters because
`sqrt` is a limit construction the ring normalizer cannot see through.

### 6. Names live in a registry struct

`ConicNames` is a `Copy` registry field `pub conic: ConicNames` on
`CPointPrelude`, in the ADR-1512 shape, rather than 56 more flat fields. The
2026-08-27 architecture review names the flat-field prelude as a measured root
cause of recurring phase-order bugs; `creal_point.rs` is already at that size
and a new module should not add to it.

## Consequences

- `CPointPrelude` gains one field; the Python mirror gains 56 dotted names
  (`cpoint["conic.discriminant"]` and so on), regenerated by
  `scripts/gen-py-prelude-fields.py`.
- The 56 declarations are registered in
  `creal_point_tests::every_theorem_here_is_axiom_free`, whose coverage half
  reads the ENVIRONMENT rather than the list, so an unregistered `CPoint.*`
  declaration fails it.
- No analytic fact about `CReal` is used anywhere in `creal_point/conic.rs` —
  not `sqrt`, not `inv`, not completeness. Order facts appear only in the four
  sign theorems and the three exclusions.

## What this ADR does not decide, and the size of each

- **"A line meets a conic in at most two points."** Needs the quadratic
  formula over `CReal`, hence `sqrt` of the restricted quadratic's own
  discriminant, hence a decision on that discriminant's sign — which for a
  general conic the three predicates here cannot supply. It is reachable for
  a conic *given* one of the three predicates, and that is the natural next
  slice.
- **The reflective property of the parabola.** Needs the tangent line, so a
  derivative or an explicit tangency condition, neither of which exists on
  `CPoint`. Roughly one new definition (tangency as a double root, stated
  without `sqrt`) plus one ring identity.
- **The general normal form `IsEllipseType K → ∃ isometry, …`.** Needs the
  eigenvector rotation angle (a square root) and the `±` choice
  `creal_point/isometry.rs` sizes at four sub-shelves. Unchanged by this ADR.
