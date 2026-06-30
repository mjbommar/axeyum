# End To End: Complex Algebraic Replay

This lesson follows one complex-number resource from exact real-pair arithmetic
to polynomial-root replay. It uses the
[complex-algebraic-v0](../../../artifacts/examples/math/complex-algebraic-v0/)
pack.
For finite complex-plane transform replay, read
[End To End: Complex Plane Transforms](complex-plane-transforms-end-to-end.md).

Concept rows:

- `curriculum_complex`, `curriculum_linear_algebra`, and
  `curriculum_polynomials` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_complex_analysis`, `field_linear_algebra`, `field_real_analysis`, and
  `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `complex-arithmetic-replay` | `sat` | replay-only |
| `conjugate-norm-replay` | `sat` | replay-only |
| `bad-norm-squared-rejected` | `unsat` | checked |
| `quadratic-root-witness` | `sat` | replay-only |

The satisfiable rows are exact witness replays over rational real-pair data.
The malformed norm-squared row is checked by QF_LRA/Farkas after exact replay
computes the norm.

## Encode Complex Numbers As Pairs

The pack represents:

```text
a + bi
```

as:

```text
[a, b]
```

where `a` and `b` are exact rational strings. No floating-point arithmetic is
used.

## Replay Addition And Multiplication

The first witness records:

```text
z = 1 + 2i = [1, 2]
w = 3 - i  = [3, -1]
```

The validator checks pair addition:

```text
z + w = [4, 1]
```

and twisted multiplication:

```text
(1 + 2i) * (3 - i) = 5 + 5i = [5, 5]
```

## Replay Conjugation And Norm

The conjugate row records:

```text
z = 3 + 4i
conjugate(z) = 3 - 4i
```

The validator recomputes:

```text
z * conjugate(z) = 25 + 0i
norm_squared = 25
```

This is exact algebra over rational pairs, not numerical approximation.

## Reject A Bad Norm Claim

The bad row reuses the same source object:

```text
z = 3 + 4i
|z|^2 = 25
```

but claims:

```text
|z|^2 = 26
```

The validator recomputes the norm exactly, and the source QF_LRA artifact
checks the final equality conflict with Farkas evidence.

## Replay A Quadratic Root

The polynomial row records the complex number `i`:

```text
i = [0, 1]
i^2 = [-1, 0]
i^2 + 1 = [0, 0]
```

The validator recomputes the square and the polynomial value. This is a fixed
root witness for `x^2 + 1`, not the fundamental theorem of algebra.

## Name The Lean Horizon

The pack explicitly leaves analytic and global algebraic theorems outside the
finite replay checker:

```text
fundamental theorem of algebra
holomorphy
contour integration
residues
analytic continuation
```

Those need theorem-prover reconstruction or dedicated complex-analysis proof
artifacts.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
cargo test -p axeyum-solver --test math_resource_lra_routes complex_algebraic_bad_norm_squared_artifact_emits_checked_farkas
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current complex-number resource pattern:

```text
untrusted fast search -> complex arithmetic or root witness
trusted small checking -> exact rational real-pair replay plus Farkas evidence
remaining gap -> analytic complex-analysis theorem routes
```

The graduation target is deterministic NRA-style real-pair obligations plus
checked replay through Axeyum model evaluation.
