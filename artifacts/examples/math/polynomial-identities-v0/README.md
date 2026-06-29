# Polynomial Identities V0

This pack covers the first core curriculum slice for `polynomials`: fixed-degree
univariate identities, root replay, and factor-theorem witnesses over exact
rational coefficients.

The examples are the exact algebra shadow of Axeyum's fixed-degree BV/NRA route:

- replay the formal coefficient identity `(x + 1)^2 = x^2 + 2x + 1`;
- replay the factor theorem for `x^2 - 5x + 6` at the root `2`;
- reject a fixed false root claim for `x^2 + 1` over the rationals.

These are not broad polynomial-theory proofs. They are small checked artifacts
that establish the table/term discipline needed before adding richer
interpolation, factorization, characteristic-polynomial, or real-root packs.

## Concepts

- `curriculum_polynomials`
- `curriculum_fields`
- `field_abstract_algebra`
- `field_real_analysis`
- `field_complex_analysis`

## Trust Story

The validator parses every coefficient as an exact rational, normalizes trailing
zero coefficients, and recomputes polynomial multiplication and evaluation. A
listed identity is accepted only when the expanded coefficient vectors match.
A root witness is accepted only when evaluation gives exactly zero and the
listed quotient/factor multiplication reconstructs the original polynomial.
The false-root row is checked by exact evaluation.

This pack does not yet emit Axeyum NRA/BV terms or proof certificates. General
factorization, irreducibility, algebraic closure, and quantification over all
polynomials remain Lean-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-identities-v0
```
