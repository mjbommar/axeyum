# ADR-1615: The angle is a cosine, not a number

Status: accepted
Date: 2026-09-04
Index-summary: Angle measure on `CPoint` is `cosAngle`/`sinAngle` as ratios, not `arccos`; the Pythagorean identity comes from Lagrange, not from the trig series

## Context

[`docs/math-department/05-geometry.md`](../../math-department/05-geometry.md)'s
first "next five" item is that the library "has trigonometry and it has
geometry and they do not touch": `CReal.sin_fn`/`cos_fn` are built as power
series in `creal/trig.rs`/`trig_fn.rs`, and `CPoint` — 94 proved plane facts,
Stewart, Ceva, Menelaus, the Euler line — mentions neither. Item 3 is the
isometry group. This lane (W1-8, W2-13) closes both, and the design question is
the same for each: **what is an angle in this development?**

The obvious answer is a real number in `[0, π]`, which needs `arccos`. That
route was priced first, and the price is the reason this ADR exists.

## Decision

**Angle measure on `CPoint` is a pair of ratios, `cosAngle` and `sinAngle`, not
a number; and a rotation is parameterised by a normalised pair `(c, s)`, not by
an angle.** `arccos` is not built and is not needed for the laws of sines and
cosines.

Concretely, in `creal_point/angle.rs` and `creal_point/isometry.rs`:

```text
norm V          := CReal.sqrt (CPoint.dot V V)
crossV U V      := (x U)(y V) − (y U)(x V)
cosAngle U V k h := ⟨U,V⟩ · (‖U‖‖V‖)⁻¹        -- h : PosBound (‖U‖‖V‖) k
sinAngle U V k h := |U × V| · (‖U‖‖V‖)⁻¹
rotate c s      := fun P => (c·Px − s·Py, s·Px + c·Py)   -- with c² + s² ~ 1
```

The nonzero-denominator condition is **data**: `CReal.inv` consumes a
`PosBound` witness, not an `Apart` proof (an `Apart`-indexed inverse would have
to eliminate a disjunction into a `Type`, which `Or.rec` forbids — see
`CRealPrelude::inv`). So `cosAngle` and `sinAngle` take `(k : Nat)` and the
`PosBound` proof as explicit arguments, exactly the idiom
`CPoint.NonCollinear` already uses for a nonzero determinant.

## Evidence

Three measurements decided it, all against a freshly rebuilt
`shape_search --include-constructed` at `declarations=3935` (positive control
`Metric.CPoint.dotLeSqrtMul`, FOUND 1).

**1. `CReal.sin_sq_add_cos_sq` does not exist, under any spelling.** Neither
does an addition theorem for `sin_fn`/`cos_fn`. The trig layer carries the
series, `cosOneConverges`, `twoLePi`, the half-term bounds, uniform continuity
and a derivative — but not the Pythagorean identity. So `arccos` would not have
been sufficient: `sin² + cos² = 1`, the identity every law of sines is stated
against, would still have had to be proved analytically afterwards.

**2. The identity is already in the file, as algebra.**
`CPoint.lagrange_identity` is `(a²+b²)(c²+e²) − (ac+be)² = (ae−bc)²`. At the
four coordinates of two points that says `‖u‖²‖v‖² − ⟨u,v⟩² = (u × v)²`, and
dividing by `‖u‖²‖v‖²` gives `sin² + cos² = 1` for the ratios above. The whole
proof of `CPoint.sin_sq_add_cos_sq` is five rewrites over the existing ring
normalizer plus `mul_self_abs`, `mul_self_sqrt` and `mul_inv_cancel`. **No
series, no derivative, no analytic input at all.**

**3. `CReal.sqrt` exists, and the file's own doc comments say it does not.**
`CPointPrelude::cauchy_schwarz`, `dist_sq_double_sum_bound`,
`dist_sq_triangle_sq_bound`, `heron_sixteen_area_sq` and others each carry a
comment saying "this kernel has `CReal.natSqrt` but no `CReal.sqrt`, so the
norm form is not expressible, let alone provable, here". That is stale:
`sqrt`, `sqrt_congr`, `sqrt_le_sqrt`, `sqrt_sq`, `sqrt_nonneg`,
`mul_self_sqrt`, `sqrt_mul` and `le_of_sq_le` are all in `CRealPrelude`, which
`CPointPrelude` carries, and `metric.rs` already consumes them one prelude
later. The unsquared statements those comments call inexpressible are
expressible today, and this lane states three of them.

A fourth measurement is a bonus rather than a reason: `CPoint.cross A B C` is
*definitionally* `crossV (sub B A) (sub C B)`, so `CPoint.cross_eq_crossV` is
`equiv_refl`, and every `Collinear`, area, Ceva and Menelaus fact already
proved is a fact about `sinAngle` with no transport.

## Alternatives

**`arccos` first, angle as a real in `[0, π]`.** Rejected on cost, not on
principle. The IVT-by-bisection layer (`creal/ivt.rs`) does give a root of a
continuous sign-changing function, so a root of `cos t − r` is reachable; but a
root is not a *function*, and turning it into one needs a uniqueness argument
(strict monotonicity of `cos` on `[0, π]`, itself unproved) plus a congruence
obligation for the resulting map. Add the missing `sin² + cos² = 1` from
measurement 1 and the missing `cos` monotonicity, and the arccos route is three
analytic results deep before it can state the law of sines — which the ratio
route states without any of them. **If `arccos` is wanted later, nothing here
blocks it**, and `cos_angle_le_one`/`neg_one_le_cos_angle` are exactly the
range condition it would consume.

**Angle as an `Apart`-indexed quantity.** Rejected: `CReal.inv` cannot consume
an `Apart`, so the definition could not be written.

**Rotation parameterised by an angle.** Rejected for the same reason as the
whole ADR — it would reintroduce the `arccos` dependency into `W2-13`, which
otherwise needs nothing analytic. `sin_sq_add_cos_sq` says every
`(cosAngle, sinAngle)` pair is admissible input to `isometry_rotate`, which is
where the two halves of the lane meet.

**Isometry stated over `Metric.CPoint.dist`.** Rejected on layering: `metric.rs`
is a later prelude than `creal_point.rs`, so a `dist`-shaped definition cannot
live in the `cpoint` group at all. `distSq` is the same condition (`sqrt` is
injective on the nonnegatives) and is square-root-free, so every instance is
discharged by the ring normalizer alone.

## Consequences

**What landed** (32 declarations, all admitted, all axiom-footprint-free):

| | |
|---|---|
| norm | `norm`, `norm_nonneg`, `norm_sq`, `norm_congr` |
| cross | `crossV`, `cross_eq_crossV`, `lagrange_vector` |
| angle | `cosAngle`, `sinAngle`, `sin_sq_add_cos_sq`, `abs_cos_angle_le_one`, `cos_angle_le_one`, `neg_one_le_cos_angle` |
| laws | `law_of_cosines_dot`, `norm_mul_cos_angle`, `law_of_sines`, `law_of_cosines` |
| isometry group | `Isometry`, `idMap`, `comp`, `isometry_id`, `isometry_comp` |
| instances | `translate`, `isometry_translate`, `rotate`, `isometry_rotate`, `reflect`, `isometry_reflect` |
| non-example | `scale`, `scale_distSq`, `not_isometry_scale_two` |
| classification | `isometry_preserves_dot` |

`abs_cos_angle_le_one` is unsquared Cauchy–Schwarz for the plane, read off the
Pythagorean identity rather than off `Metric.CPoint.dotLeSqrtMul` — the two are
in different preludes and neither depends on the other.

**What is deliberately NOT here.**

*No `PosBound` producer for `‖U‖‖V‖.* A caller must supply the witness; there
is no lemma deriving it from `PosBound (dot U U) j` and `PosBound (dot V V) l`.
The missing step is `PosBound x k → PosBound (sqrt x) k`, reachable from
`CRealPrelude` alone — with `r := ofRat (1/(k+1))`, `r·r ≤ r ≤ x ~ sqrt x ·
sqrt x`, so `le_of_sq_le` closes it — but it needs `Rat.natDivSucc 1 k ≤
Rat.one` and then a second lemma to fuse two moduli through `mul`
(`1/(j+1) · 1/(l+1) = 1/((j+1)(l+1))`, a `Nat` index computation). **Two lemmas
plus two `Rat` facts.** This is the first thing a follow-on lane should build:
until it exists, the angle layer is stated in full generality but can only be
*instantiated* by a caller who already holds the witness.

*The classification of plane isometries is not proved.* "Every isometry is a
rotation-or-reflection after a translation" needs, beyond
`isometry_preserves_dot`:

1. a scalar multiple of a point (`CPoint.smul`) with its `dot` bilinearity laws
   — six lemmas, none hard, none present;
2. `f(P) − f(0) ~ Px·u + Py·v`, proved by showing the difference `W` has
   `⟨W,W⟩ ~ 0` and closing with the existing
   `CPoint.eq_zero_of_dot_self_zero`. This is the real work, and it needs (1)
   throughout;
3. the `±` split: `u = (c,s)` with `c² + s² ~ 1` forces `v = ±(−s,c)`, and
   choosing the sign is a **decision on the sign of a real**. It *is* decidable
   here — `(u × v)² ~ 1` puts `u × v` apart from `0`, and `CReal.apart_cotrans`
   on the threshold pair `(−1/2, 1/2)` resolves it — but it is a genuine
   argument, not a case split.

**Sized at four sub-shelves, roughly 25–40 new declarations and 1200–1800
lines**, dominated by (1)'s bilinearity boilerplate and (3)'s cotransitivity
argument. Nothing in it is blocked.

**The negative control is a theorem, not a test.**
`CPoint.not_isometry_scale_two : Isometry (scale two) → False` is proved
constructively: instantiate at `(1,0)` and `(0,0)`, the ring normalizer
computes both `distSq` values, `4 ~ 1` follows, two `CReal.add_right_cancel`
steps give `1 + 1 ~ −1`, and `CReal.not_le_zero_neg_one` refutes the `0 ≤ −1`
that follows. This is stronger than a "the kernel rejects it" test, which the
suite *also* carries (an admitted proof re-offered at a neighbouring
statement's type, each row with a matched positive control).

**Stale doc comments are now a known defect.** The "no `CReal.sqrt`" claim
appears in at least five `creal_point.rs` doc comments and made three
reachable statements look inexpressible. They are left in place here — editing
them is a separate, mechanical change that would collide with other lanes in a
21k-line file — but any lane that reads one should disbelieve it.
