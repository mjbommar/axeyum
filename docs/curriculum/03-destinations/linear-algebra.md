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
`2×2` matrices over NRA. Together these pressure LRA + NRA — the corpora P2.5
needs.

**Built** (`Family::LinearAlgebra`, first cut over fixed-size `BitVec` matrices,
exhaustive/witness self-checks): `det_product_2x2` (det(AB)=detA·detB),
`transpose_product_2x2` ((AB)ᵀ=BᵀAᵀ), `mult_associative_2x2` ((AB)C=A(BC) over
𝔽₂), and `linear_solve_2x2` (Ax=b with the solution as witness). The ℚ/NRA
variants (Farkas-certified solving, 3×3 determinant identities) are the next
increment.

## Lean-horizon

Dimension theory, the spectral theorem, and anything quantifying over all
dimensions/vector spaces are Lean-horizon (Mathlib `LinearAlgebra`).

## References

- Axler, *Linear Algebra Done Right*.
- axeyum: `check_with_lra` (Farkas), NRA (ADR-0024).
