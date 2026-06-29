# Matrix Invariants V0

This pack adds the first exact matrix-invariant slice after the finite spectral
linear-algebra pack. It uses a single rational symmetric `2x2` matrix, so every
claim is finite and exact.

The examples are:

- trace, determinant, and characteristic-polynomial replay;
- characteristic-root replay;
- Cayley-Hamilton replay for one fixed matrix;
- a finite Gershgorin interval containment check;
- checked QF_LRA/Farkas rejection of a false characteristic polynomial.

## Concepts

- `field_linear_algebra`
- `field_abstract_algebra`
- `field_real_analysis`
- `field_numerical_analysis`
- `curriculum_linear_algebra`
- `curriculum_polynomials`
- `curriculum_rationals`
- `curriculum_reals`

## Trust Story

The validator parses every scalar as an exact rational. It recomputes trace,
determinant, the `2x2` characteristic polynomial, root evaluations, `A^2`,
the Cayley-Hamilton matrix polynomial value, and row Gershgorin intervals.

This pack is checked finite evidence for the false characteristic-polynomial
row and replay-only evidence for the positive witnesses. The bad row also
links a `QF_LRA` SMT-LIB artifact and a solver regression that emits
independently rechecked `UnsatFarkas` evidence for the witness-root conflict
`characteristic_value_at_witness = 0` versus
`characteristic_value_at_witness = 2`. General spectral theorems, algebraic
multiplicity theory, higher-dimensional determinant algorithms, and numerical
eigensolvers remain proof or numerical-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
```
