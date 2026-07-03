# Finite Taylor Polynomial Checks

This pack records exact rational Taylor-polynomial replays for fixed
polynomials. It is a calculus and numerical-analysis resource: coefficient
arithmetic, derivative values, factorial divisors, basis powers, and Taylor
values are replayed exactly, while Taylor theorem hypotheses, remainder
theorems, convergence, multivariable Taylor, and floating-point implementation
claims stay in theorem or numerical-honesty lanes.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-taylor-polynomials-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_taylor_polynomials_bad_value_artifact_emits_checked_farkas
```

## Checks

- `quadratic-taylor-at-one-witness` replays a degree-2 Taylor polynomial for
  `1+2x+x^2` at center `1`.
- `cubic-taylor-at-zero-witness` replays a degree-3 Taylor polynomial for
  `1+x+x^2+x^3` at center `0`.
- `truncated-linearization-witness` replays a degree-1 Taylor linearization and
  its exact rational remainder.
- `bad-taylor-value-rejected` rejects a malformed exact Taylor value by replay.
- `qf-lra-bad-taylor-value` routes the scalar contradiction through checked
  QF_LRA/Farkas evidence.
- `general-taylor-theory-lean-horizon` marks the missing theorem and
  numerical-honesty routes.

## Trust Boundary

```text
untrusted fast search -> Taylor coefficients, truncated value, or Farkas certificate
trusted small checking -> exact rational Taylor replay plus checked QF_LRA/Farkas evidence
```
