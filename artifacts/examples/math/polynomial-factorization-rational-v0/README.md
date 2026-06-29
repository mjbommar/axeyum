# Exact Rational Polynomial Factorization Checks

This pack deepens the polynomial curriculum slice beyond fixed identities and
single-root witnesses. It keeps the scope to exact univariate polynomials over
`Q`, represented as low-degree coefficient lists.

It checks:

- factor-list product replay for `x^4 - 1`;
- exact polynomial division with quotient and zero remainder;
- Euclidean GCD replay over rational coefficients;
- square-free decomposition replay through `gcd(p,p')`;
- rejection of a rational linear factorization claim for `x^2 + 1`;
- general polynomial factorization theory as Lean horizon.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-factorization-rational-v0
```
