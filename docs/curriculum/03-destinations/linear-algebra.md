# Linear Algebra

> Layer 3 · destinations · decidability: `computable` · axeyum theory: BV (fixed-size) / LRA / NRA · status: `covered`

## What it is

The theory of **vector spaces** and **linear maps**: vectors, **matrices**,
linear systems `Ax = b`, **determinants**, **rank**, **eigenvalues** and
**eigenvectors**, inner products and orthogonality.

## Role in the tour

A destination resting on fields (the scalars) and functions (linear maps). Its
*concrete, fixed-dimension* content is highly computable, making it a rich source
of self-checking exercises that pressure axeyum's exact-rational and nonlinear
arithmetic.

## Prerequisites

- [Fields](../02-structures/fields.md) — scalars live in a field.
- [Relations & Functions](../00-foundations/relations-and-functions.md) — linear maps are functions.
- [Polynomials](../02-structures/polynomials.md) — characteristic polynomials, eigenvalues.

## Unlocks

(Destination.)

## Testable in axeyum

For **fixed dimensions over ℚ** (or 𝔽ₚ) almost everything is computable and
checkable: solving `Ax = b` (LRA, with the exact rational solution as witness),
matrix identities (`(AB)ᵀ = BᵀAᵀ` at fixed size, refuted-by-negation),
determinant identities (`det(AB) = det A · det B` for `2×2`/`3×3`, a polynomial
identity over NRA), and verifying a claimed eigenvector (`Av = λv`).

Example exercise: solve a `3×3` rational system (witness solution); refute an
inconsistent system with a Farkas certificate; check `det(AB) = det A·det B` for
`2×2` matrices over NRA. Together these pressure exact LRA, finite-field/BV,
and nonlinear-real routes.

**Built** (`Family::LinearAlgebra`, first cut over fixed-size `BitVec` matrices,
exhaustive/witness self-checks): `det_product_2x2` (det(AB)=detA·detB),
`transpose_product_2x2` ((AB)ᵀ=BᵀAᵀ), `mult_associative_2x2` ((AB)C=A(BC) over
𝔽₂), `linear_solve_2x2` (Ax=b with the solution as witness), and
`det_product_3x3_f2`. Separate validated foundational packs cover exact rational
linear algebra, residuals, factorization, spectral shadows, and checked Farkas
contradictions; consult the generated resource audit rather than treating this
scenario list as the entire field surface.

## Proved in the kernel — including at general dimension

This section is new (2026-08-30) and corrects an omission: the page described
only the scenario and solver layers, and did not mention the Lean kernel at all.
Measured with a freshly built `shape_search --include-constructed`, all
axiom-free:

- **General dimension `n` over ℚ.** `Rat.dotN : (Nat → Rat) → (Nat → Rat) →
  Nat → Rat`, with bilinearity (`dotN_add_left`, `dotN_smul_left`), symmetry
  (`dotN_comm`), positive semidefiniteness (`dotN_self_nonneg`) and
  **`Rat.dotN_cauchy_schwarz` at arbitrary `n`**. A vector is a finite function
  plus a dimension — the same encoding `Nat.prodRange` uses — so no `List` or
  product type is required.
- **Finite double sums.** `Rat.sumRange_swap` (the rectangular interchange
  `Σᵢ Σⱼ f i j = Σⱼ Σᵢ f i j`), `Rat.sumRange_diagonal`, `Rat.mul_sumRange`,
  `Rat.sumRange_congr`. `sumRange_swap` is exactly the lemma matrix-product
  associativity needs.
- **The determinant at general dimension `n`, and fixed size 2 and 3 over ℚ.**
  `Rat.det : (Nat → Nat → Rat) → Nat → Rat` (ADR-1120, landed 2026-08-31) is a
  **cofactor recursion over the dimension bound** — the route this page used
  to name as the missing piece, and the honest one since a permutation sum
  needs permutations as data and this kernel has no `List`. `det_zero`/
  `det_succ` are the recursion equations; `det_eq_det2`/`det_eq_det3` prove it
  agrees with the fixed-size forms at `n = 2, 3`: `Rat.det2` with `det2_mul`
  (multiplicativity), `det2_id`, `det2_swap_rows`, `det2_scale_row`,
  `det2_row_add`, `det2_eq_zero_of_lin_dep`; `Rat.det3` with
  `det3_cofactor_row1`, `det3_id`, `det3_scale_row`. Fixed-size entries are
  passed as separate scalar arguments; the general form takes the matrix as a
  `Nat → Nat → Rat` function, matching `matMul`/`matTranspose`.
- **A 2-D inner-product space over the constructed reals.** `CPoint` — 116
  declarations — with `dot`, `cross`, `distSq`, `cauchy_schwarz`,
  `dot_self_zero_iff`, and centroid / circumcentre / Euler-line geometry above
  it.

## The one hard type-theory bound: no `funext`

`funext` is **absent** from this kernel (positive control: `congrFun'`, the
other direction, is present). Two functions that agree pointwise are therefore
not propositionally equal, which decides how a general-dimension statement must
be phrased:

- A conclusion that is a **scalar** is fine — which is why `dotN_cauchy_schwarz`
  was reachable at general `n`.
- A conclusion that is a **vector or matrix equation** — `(AB)C = A(BC)`,
  `(AB)ᵀ = BᵀAᵀ`, `A·A⁻¹ = I` — cannot be stated as `Eq` of functions. State it
  **pointwise**: `∀ i j, i < m → j < n → …`. The same applies to every
  uniqueness statement.

`Nat.Fin` does exist as a dependent inductive if a lane prefers bounds carried
in the type rather than as hypotheses.

## Lean-horizon

The spectral theorem, dimension theory proper, and anything quantifying over
arbitrary vector spaces or fields are Lean-horizon (Mathlib `LinearAlgebra`).

**Two sentences that used to stand here are now both false, and the second went
stale within a day of being written.** The first was "anything quantifying over
all dimensions": general `n` is reachable for scalar-valued conclusions and is
already used (`Rat.dotN_cauchy_schwarz`). The second was "what is genuinely
unbuilt is the matrix layer over `Nat → Nat → Rat`" — that layer landed:
`Rat.matMul`, `Rat.matId`, `Rat.matTranspose`, with `matMul_assoc`,
`matMul_id_left`/`_right`, `matMul_add_left`/`_right`, `matMul_smul_left`,
`matTranspose_mul` ((AB)ᵀ = BᵀAᵀ) and `matTranspose_transpose`, all axiom-free
and all stated pointwise as the absence of `funext` requires. `Rat.cramer2_*`
and the 2×2 adjugate inverse (`inv2_*`, `mul_adj2_*`) are landed too.

**A third sentence needs the same correction, hours after the second.**
Measured 2026-08-31 morning, this destination attributed 55/59 kernel
declarations (ADR-1075/ADR-1082) and named the general-`n` determinant as the
remaining genuine gap. That gap closed the same day (ADR-1120): re-measured
after fixing a bucket-attribution bug in
`scripts/measure-curriculum-kernel-coverage.py` that had silently mis-filed
the new `Rat.det`/`matSkip`/`matMinor`/`altSign`/`matInv2*` declarations under
`rationals`, this destination attributes **81 kernel declarations** (ADR-1140).
The remaining genuine gap is everything spectral — eigenvalues, eigenvectors,
the characteristic polynomial's roots — which is Mathlib-scale.

**Re-measured 2026-08-31, ADR-1205: 90.** ADR-1155's Laplace row-expansion
layer landed nine more declarations, and one of them
(`Rat.sumRange_matSkip`, a reindexing lemma the expansion needs) had the same
bucket-attribution bug ADR-1140 fixed one layer over: its name starts with
`sumRange_`, not `mat`, so it fell through to the `rationals` catch-all until
the pattern was widened. Fixed in the same pass; the gap named above is
unchanged.

## Graded-family treatment

[`../graded-statement-families-number-theory-and-linear-algebra.md`](../graded-statement-families-number-theory-and-linear-algebra.md)
§3 gives the four linear-algebra families with their rows, and the type-theory
verdict in full. Row 2 is empty for all of them, for the reason
[ADR-0716](../../research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md)
gives: `Rat.le_total` is a proved theorem here, so there is no order decision to
extract. The `Ax = b` family's row 3 — `simplex::feasible` / `check_farkas`,
`lra::FarkasCertificate::verify`, and kernel reconstruction through
`prove_unsat_to_lean_module` — is the strongest row 3 anywhere in the
curriculum and is the template other subjects should be measured against.

## References

- Axler, *Linear Algebra Done Right*.
- axeyum: `check_with_lra` (Farkas), NRA (ADR-0024).
