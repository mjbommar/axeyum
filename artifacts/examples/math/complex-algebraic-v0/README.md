# Complex Algebraic V0

This pack covers exact algebraic complex-number examples for the `complex`
curriculum node and the `complex_analysis` field row. It models each complex
number `a + bi` as the pair `[a, b]` of exact rational strings.

The examples are intentionally algebraic and finite:

- real-pair complex addition and multiplication;
- conjugation and norm-squared replay;
- malformed product-coordinate and norm-squared rows checked through
  QF_LRA/Farkas evidence;
- a fixed polynomial-root witness for `x^2 + 1` at `i`.

## Concepts

- `curriculum_complex`
- `curriculum_linear_algebra`
- `curriculum_polynomials`
- `field_complex_analysis`
- `field_linear_algebra`
- `field_real_analysis`
- `field_abstract_algebra`

## Trust Story

The validator parses all real and imaginary parts as exact rational strings. It
recomputes pair addition, twisted multiplication, conjugation, norm-squared,
the bad product-coordinate and norm-squared source data, and the fixed
polynomial evaluation without floating-point arithmetic.

The malformed product-coordinate and norm rows are checked by the
QF_LRA/Farkas route after exact real-pair replay computes
`(1 + 2i) * (3 - i) = 5 + 5i` and `|3 + 4i|^2 = 25`.
This pack does not claim the fundamental theorem of algebra, holomorphy,
contour integration, residues, or analytic continuation. Those remain
Lean-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
```
