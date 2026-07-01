# Exact Rational Inner Product Space Checks

This pack adds the exact finite-dimensional inner-product bridge between
linear algebra, dual spaces, spectral linear algebra, least squares, and
functional analysis. It stays in `Q^2`, so every check is exact rational matrix
and vector arithmetic.

It checks:

- standard inner-product table replay and sample bilinearity;
- symmetric positive-definite Gram matrices by exact principal minors;
- Cauchy-Schwarz for fixed rational vectors;
- orthogonal projection onto a one-dimensional subspace;
- checked QF_LRA/Farkas rejection of a malformed projection residual
  orthogonality claim;
- Gram-Schmidt residual replay for a two-vector basis;
- checked QF_LRA/Farkas rejection of a matrix that gives a negative norm
  square;
- general inner-product and Hilbert-space theory as Lean horizon.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
```
