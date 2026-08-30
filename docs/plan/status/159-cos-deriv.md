# Lane 159 — `HasDerivativeOn cosFnWide (fun x => neg (sinFn x))`

<!-- plan-section: lane-status -->

**Status: PARTIAL — the keystone landed, the target did not, and the gap is
now precisely sized.** 2026-08-27.

The target itself is NOT landed and nothing here should be read as implying
π. What landed is the one missing analytic fact standing under it.

**The searched question, answered.** A "uniform limit of derivatives" theorem
is **genuinely absent** from this development. Measured against a FRESH
`shape_search` index (`declarations=1889`, matching the current tree, so the
stale-prebuilt false-ABSENT hazard does not apply):

- `--concl CReal.HasDerivativeOn` → **FOUND 16**, and all sixteen are
  pointwise combinators (`mk`, `const`, `id`, `sq`, `neg`, `add`, `sub`,
  `smul`, `mul`, `pow`, `pow_two`, `cube`, `chain`, `chain_id_sq`, `congr`,
  `integral_const`). Not one takes a limit hypothesis.
- `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn` → **ABSENT**
  (exit 1, positive control `any-kind=1889 ns CReal=512`).
- `--hyp CReal.UniformConvergesOn` → **FOUND 5**: `.rate`, `.rec`, `.spec`,
  `uniform_converges_add`, and `uniform_limit_uniformly_continuous`. The
  last is the ONLY theorem in the tree that transports any property at all
  through a uniform limit.

**The finite-partial-sum route does not avoid the interchange.** Writing `Sₙ`
for a partial sum and `F` for its uniform limit, the standard split is
`(A) |(F y − F x) − (Sₙ y − Sₙ x)| + (B) |(Sₙ y − Sₙ x) − Sₙ'(x)(y−x)| +
(C) |Sₙ'(x) − F'(x)|·|y−x|`. (B) is each partial sum's own `spec`; (C) is
uniform convergence of the derivative series, which `sinFnUniformConverges`
already supplies. (A) is bounded by uniform convergence of the FUNCTIONS only
by a **constant** `2δₙ`, while `deriv_spec_body`'s budget is
`(1/(e+1))·|y − x|` quantified over every `y` within `1/(m e + 1)` of `x` —
including points arbitrarily close to it. No `n` absorbs a constant into an
`ε·|y − x|` budget, so the interchange is required by the shape of the spec,
not by how the limit happens to be taken.

Detail moved to [`../notes/159-cos-deriv.md`](../notes/159-cos-deriv.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | cos-deriv | `CReal.abs_diff_le_of_deriv_bound` -- mean value inequality; `monotone_of_nonneg_deriv` applied twice, to `r ↦ M·r ∓ F(r)`; axiom-free |
| 2026-08-27 | `creal/mvt.rs::build_hd_linear` → `pub(super)` | reused rather than copied; `hasDerivative_smul ∘ hasDerivative_id` would need a magnitude bound on `M` |
| 2026-08-27 | measured: uniform-limit-of-derivatives is ABSENT | `shape_search` at `declarations=1889`; 16 `HasDerivativeOn` conclusions, all pointwise |
