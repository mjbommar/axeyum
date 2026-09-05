# Lane: angles-and-isometries — join the analytic trig layer to `CPoint` (W1-8) and give the plane its isometry group (W2-13)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, angles-and-isometries, 2026-09-04).** W1-8 and
W2-13 both landed: **32 declarations, every one admitted, every axiom footprint
empty.** ADR-1615 records the design.

**The decision: the angle is a cosine, not a number.** `arccos` was priced and
rejected, and the reason is a retrieval finding, not a preference:
<!-- absent: CReal.sin_sq_add_cos_sq -->
**`CReal.sin_sq_add_cos_sq` does not exist under any spelling** (checked
against a freshly rebuilt `shape_search --include-constructed`,
`declarations=3935`, positive control `Metric.CPoint.dotLeSqrtMul` FOUND 1).
Neither does an addition theorem for `sin_fn`/`cos_fn`. So `arccos` would not
have been sufficient — the Pythagorean identity would still have had to be
proved analytically afterwards. It is not needed: `CPoint.lagrange_identity`
divided by `‖u‖²‖v‖²` **is** `sin² + cos² = 1` for the ratios
`cosAngle u v := ⟨u,v⟩/(‖u‖‖v‖)` and `sinAngle u v := |u×v|/(‖u‖‖v‖)`, and it
is pure ring algebra — no series, no derivative, no analytic input at all.

**What landed** (`creal_point/angle.rs`, `creal_point/isometry.rs`):

| | |
|---|---|
| norm | `norm`, `norm_nonneg`, `norm_sq`, `norm_congr` |
| cross | `crossV`, `cross_eq_crossV`, `lagrange_vector` |
| angle | `cosAngle`, `sinAngle`, `sin_sq_add_cos_sq`, `abs_cos_angle_le_one`, `cos_angle_le_one`, `neg_one_le_cos_angle` |
| laws | `law_of_cosines_dot`, `norm_mul_cos_angle`, `law_of_sines`, `law_of_cosines` |
| isometry monoid | `Isometry`, `idMap`, `comp`, `isometry_id`, `isometry_comp` |
| instances | `translate`, `isometry_translate`, `rotate`, `isometry_rotate`, `reflect`, `isometry_reflect` |
| non-example | `scale`, `scale_distSq`, `not_isometry_scale_two` |
| classification | `isometry_preserves_dot` |

Three things a later lane should not re-derive:

- **`CPoint.cross_eq_crossV` is `equiv_refl`.** The existing three-POINT
  `cross A B C` is *definitionally* `crossV (sub B A) (sub C B)`, so every
  `Collinear`, area, Ceva and Menelaus fact already proved is a fact about
  `sinAngle` with no transport.
- **A rotation is parameterised by the pair `(c, s)` with `c² + s² ~ 1`, never
  by an angle** — which is why W2-13 needed nothing analytic either, and
  `sin_sq_add_cos_sq` says every `(cosAngle, sinAngle)` pair is admissible
  input.
- **The negative control is a theorem.**
  `not_isometry_scale_two : Isometry (scale two) → False`, constructively: the
  doubling map takes `distSq = 1` to `distSq = 4`, two `add_right_cancel` steps
  give `1 + 1 ~ −1`, `not_le_zero_neg_one` refutes the `0 ≤ −1`.

**Two sized negatives, stated as precisely as the positives.**

1. **No `PosBound` producer for `‖U‖‖V‖`.** A caller must hold the witness. The
   missing step is `PosBound x k → PosBound (sqrt x) k`, reachable from
   `CRealPrelude` alone (`r := ofRat (1/(k+1))`, then `r·r ≤ r ≤ x ~ sqrt x ·
   sqrt x`, closed by `le_of_sq_le`), plus a second lemma fusing two moduli
   through `mul`. **Two lemmas and two `Rat` facts.** Until it exists the angle
   layer is general but its instantiations are hypothesis-bound. This is the
   first thing a follow-on lane should build.
2. **The classification is not proved.** `isometry_preserves_dot` is step 1.
   The rest needs `CPoint.smul` with six bilinearity lemmas, the coordinate
   expansion closed by `eq_zero_of_dot_self_zero`, and a sign decision that is
   real constructive work (decidable via `apart_cotrans` on `(−1/2, 1/2)`
   because `(u×v)² ~ 1` puts `u×v` apart from `0` — but an argument, not a case
   split). **Sized at 25–40 declarations, 1200–1800 lines. Nothing in it is
   blocked.**

**A stale claim that cost this lane time, and will cost the next one.**
`creal_point.rs` doc comments on `cauchy_schwarz`, `dist_sq_double_sum_bound`,
`dist_sq_triangle_sq_bound` and `heron_sixteen_area_sq` each say "this kernel
has `CReal.natSqrt` but no `CReal.sqrt`, so the norm form is not expressible,
let alone provable, here". **That is false today.** `sqrt`, `sqrt_congr`,
`sqrt_le_sqrt`, `sqrt_sq`, `sqrt_nonneg`, `mul_self_sqrt`, `sqrt_mul` and
`le_of_sq_le` are all in `CRealPrelude`, which `CPointPrelude` carries, and
`metric.rs` consumes them one prelude later. Three statements those comments
call inexpressible are stated in this lane. The comments are left in place —
editing them in a 21k-line file shared by other lanes is a separate change —
but disbelieve them.

**Mutation table** (private snapshot, never the shared worktree; each mutant
runs the five tests that can distinguish its outcome, `--test-threads=1`).

| mutant | outcome |
|---|---|
| baseline | 5 passed, 0 failed |
| M1 `crossV`'s sign convention flipped (`(y U)(x V) − (x U)(y V)`) | **killed 5** — `build_cpoint_prelude` itself fails. `lagrange_vector`'s declared conclusion names `crossV`, and the `lagrange_identity` instance proving it produces `ae − bc`; the kernel refuses the mismatch. |
| M2 `translate T P := add T P` instead of `add P T` | **killed 5** — also the build. `isometry_translate`'s ring proof renders `Px + Tx`, and `CReal.add` is not definitionally commutative, so it is not defeq to `Tx + Px`. |
| M3 negative control inverted (`refused.is_err()` → `is_ok()`) | **killed exactly 1**: `a_theorem_here_proves_only_its_own_statement`. The refusals it asserts are real. |
| M4 positive control inverted (`admitted.is_ok()` → `is_err()`) | **killed exactly 1**: the same test. The harness really can admit, so the refusals are not free. |

The finding worth carrying forward: **both subject mutations are caught by the
trusted kernel, not by the test suite**, because each mutated definition is
named in some theorem's *declared type* while its proof term is built against
the intended one. A definition that no theorem's statement pins would be
invisible to the kernel, and `new_definitions_have_the_intended_value` is the
only guard that would see it. The first take of this run was pathological and
was replaced: it ran the whole 69-test suite per mutant, and because `built()`
memoises through a `OnceLock` that a panic leaves uninitialised, a
build-breaking mutant made all 69 tests re-run the release prelude build — 35
failures in 25 minutes and still going.

**Dependency closures, read from the kernel** (`theorem_dependency_inventory`,
one name per invocation):

- `CPoint.cross_eq_crossV` → `CReal.Equiv.refl`. **One edge.** That is the
  machine-checked form of "the triangle determinant IS the vector cross
  product".
- `CPoint.lagrange_vector` → `CPoint.lagrange_identity`. One edge.
- `CPoint.sin_sq_add_cos_sq` → `lagrange_vector`, `norm_sq`, and 16 `CReal`
  ring/setoid lemmas. **No trigonometric name anywhere**, which is the claim
  the ADR rests on, measured rather than argued.
- `CPoint.law_of_sines` → 8 edges, all `CReal` multiplication/inverse laws.
- `CPoint.not_isometry_scale_two` → 21 edges ending at
  `CReal.not_le_zero_neg_one`.

<!-- plan-section: landed-changes -->

| 2026-09-04 | angles-and-isometries | lane opened; step-0 retrieval at `declarations=3935`, `CReal.sin_sq_add_cos_sq` shown ABSENT |
| 2026-09-04 | angles-and-isometries | W1-8 + W2-13: 32 `CPoint` declarations for angle measure and isometries, all axiom-free; ADR-1615 |
| 2026-09-04 | angles-and-isometries | four facts: the Pythagorean identity for the plane angle, the laws of sines and cosines, and the isometry family with its doubling refutation |
