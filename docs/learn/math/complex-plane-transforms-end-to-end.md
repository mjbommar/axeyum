# End To End: Complex Plane Transforms

This lesson follows one exact complex-plane resource from real-pair arithmetic
to finite transform replay. It uses
[complex-plane-transforms-v0](../../../artifacts/examples/math/complex-plane-transforms-v0/).

Concept rows:

- `curriculum_complex`, `curriculum_reals`, and `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_complex_analysis`, `field_linear_algebra`, `field_real_analysis`, and
  `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `unit-root-cycle-replay` | `sat` | replay-only |
| `conjugation-product-replay` | `sat` | replay-only |
| `bad-conjugation-product-imaginary-rejected` | `unsat` | checked |
| `mobius-transform-witness` | `sat` | replay-only |
| `bad-unit-square-real-part-rejected` | `unsat` | checked |
| `general-complex-analysis-lean-horizon` | `not-run` | lean-horizon |

Every checked row is exact rational real-pair replay. The pack does not prove
Cauchy-Riemann equations, Cauchy's theorem, residues, analytic continuation, or
the fundamental theorem of algebra.

## Replay The Unit-Root Cycle

The first row represents `i` as the real pair:

```text
i = [0, 1]
```

and lists its powers:

```text
i^0 = [1, 0]
i^1 = [0, 1]
i^2 = [-1, 0]
i^3 = [0, -1]
i^4 = [1, 0]
```

The validator recomputes each multiplication with exact rational arithmetic and
checks that every nonzero power in the cycle has norm squared `1`.

## Replay Conjugation Over Products

For:

```text
z = [1, 2]
w = [3, -1]
```

the pack records:

```text
z*w = [5, 5]
conjugate(z*w) = [5, -5]
conjugate(z) = [1, -2]
conjugate(w) = [3, 1]
conjugate(z)*conjugate(w) = [5, -5]
```

The checker recomputes the product, each conjugate, and the product of
conjugates. This is a concrete finite witness for a familiar algebraic identity,
not a proof of the universally quantified theorem.

## Reject A False Conjugation-Product Claim

The negative row reuses the same fixed pair but claims:

```text
imaginary_part(conjugate(z)*conjugate(w)) = 5
```

Exact real-pair replay computes:

```text
conjugate(z)*conjugate(w) = [5, -5]
```

so the imaginary part is `-5`, not `5`. The promoted source artifact shifts both
sides by `+5` and records the exact-linear contradiction:

```text
computed_imaginary_part_plus_five = 0
claimed_imaginary_part_plus_five = 10
computed_imaginary_part_plus_five = claimed_imaginary_part_plus_five
```

The `math_resource_lra_routes` regression parses
`artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-conjugation-product-imaginary-farkas-conflict.smt2`,
emits `UnsatFarkas` evidence, and checks the certificate independently.

## Replay A Rational Mobius Transform

The transform row evaluates:

```text
T(z) = (z - 1) / (z + 1)
z = 2 + i = [2, 1]
```

The numerator and denominator are:

```text
z - 1 = [1, 1]
z + 1 = [3, 1]
```

The validator divides by multiplying with the conjugate and the denominator
norm:

```text
norm_squared([3,1]) = 10
T(2+i) = [2/5, 1/5]
norm_squared(T(2+i)) = 1/5
```

This gives a finite rational-function replay shape for complex-plane
transforms. It does not claim general conformality or half-plane mapping
theorems.

## Reject A False Unit-Square Claim

The negative row claims:

```text
Every square of a unit complex number has positive real part.
```

The checked counterexample is:

```text
z = i = [0, 1]
norm_squared(z) = 1
z^2 = [-1, 0]
real_part(z^2) = -1
```

The checker rejects the universal claim over this finite counterexample. The
promoted source artifact records the equivalent exact-linear contradiction:

```text
negated_real_part = 1
negated_real_part < 0
```

The `math_resource_lra_routes` regression parses
`artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-unit-square-real-part-farkas-conflict.smt2`,
emits `UnsatFarkas` evidence, and checks the certificate independently. That is
the reusable pattern: broad mathematical prose becomes a concrete witness or
counterexample row before it is trusted, and the final linear contradiction
gets a small checked certificate.

## Name The Lean Horizon

The pack intentionally stops before analytic complex analysis:

```text
Cauchy-Riemann equations
Cauchy's theorem
residue theorem
analytic continuation
fundamental theorem of algebra
conformal-map theorems
```

Those require theorem-prover reconstruction or dedicated proof artifacts. This
pack only checks exact finite real-pair arithmetic and rational transform
replay.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-plane-transforms-v0
cargo test -p axeyum-solver --test math_resource_lra_routes complex_plane_bad_conjugation_product_imaginary_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes complex_plane_bad_unit_square_real_part_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current complex-plane resource pattern:

```text
untrusted fast search -> complex transform, cycle, identity, or counterexample
trusted small checking -> exact rational real-pair replay and Farkas evidence
remaining horizon -> holomorphic, contour-integral, and global algebraic theorems
```

The graduation target is deterministic real-pair NRA obligations plus Axeyum
model replay for witnesses. The current false conjugation-product and
unit-square rows are promoted only for final exact-rational contradictions
after replay, not for general complex-analysis theorems.
