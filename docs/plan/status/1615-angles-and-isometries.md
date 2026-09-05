# Lane: angles-and-isometries — join the analytic trig layer to `CPoint` (W1-8) and give the plane its isometry group (W2-13)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, angles-and-isometries, 2026-09-04).** Step 0 done:
`shape_search --include-constructed` rebuilt at `declarations=3935`, positive
control `Metric.CPoint.dotLeSqrtMul` FOUND 1.

Retrieval findings, all against that fresh index (not a prebuilt binary):

- **`CReal.sin_sq_add_cos_sq` does not exist under any spelling.** The brief
  named it as a step to reuse. `creal.rs` carries `sin_fn`/`cos_fn` as power
  series with uniform-convergence and derivative machinery, but no Pythagorean
  identity, no addition theorem, and no `arccos`. So an `arccos`-first angle is
  blocked on an analytic result nobody has proved here.
- **`CPoint.norm` does not exist** — only `Metric.CPoint.dist P Q :=
  sqrt (distSq P Q)` (metric.rs, a later prelude) and `RN.norm` over `RN.Vec`.
- **No `Isometry`, no `Angle`, no rotation/reflection/translation** anywhere in
  the kernel (`grep` over every `name_str` interning site returns nothing).
- **`CPoint.lagrange_identity` already is the whole Pythagorean identity for the
  angle**: `(a²+b²)(c²+e²) − (ac+be)² = (ae−bc)²` instantiated at the four
  coordinates says `‖u‖²‖v‖² − ⟨u,v⟩² = (u×v)²`, which is `sin² + cos² = 1`
  after dividing by `‖u‖²‖v‖²`. No analytic trigonometry is needed for it.
- **`CPoint.dot_self_sub` already is the law of cosines in `dot` form**, up to
  regrouping: `dot (sub U V) (sub U V) ~ ⟨u,u⟩ − ⟨u,v⟩ − ⟨u,v⟩ + ⟨v,v⟩`, and
  `distSq U V` is definitionally its left side.
- Several `creal_point.rs` doc comments still assert "this kernel has no
  `CReal.sqrt`, only `natSqrt`". **That is stale** — `CReal.sqrt`,
  `sqrt_congr`, `sqrt_le_sqrt`, `sqrt_sq`, `sqrt_nonneg`, `mul_self_sqrt`,
  `sqrt_mul` and `le_of_sq_le` are all in `CRealPrelude`, which the `CPoint`
  prelude carries. The unsquared statements those comments call inexpressible
  are expressible today.

<!-- plan-section: landed-changes -->

| 2026-09-04 | angles-and-isometries | lane opened; step-0 retrieval at `declarations=3935` |
