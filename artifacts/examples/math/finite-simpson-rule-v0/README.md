# Finite Simpson Rule Checks

This pack records exact rational single-panel Simpson-rule replays for fixed
polynomials. It keeps finite quadrature arithmetic separate from general
Simpson exactness, convergence, error-bound, adaptive, and floating-point
claims.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simpson-rule-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_simpson_rule_bad_value_artifact_emits_checked_farkas
```

Rows:

- `simpson-cubic-exact-witness` replays Simpson nodes, weights, sample values,
  weighted sum, quadrature value, and exact polynomial integral for `x^3`.
- `simpson-quadratic-exact-witness` repeats the finite replay for `1+x^2`.
- `bad-simpson-value-rejected` rejects a malformed finite quadrature value by
  exact replay.
- `qf-lra-bad-simpson-value` routes the scalar contradiction through checked
  QF_LRA/Farkas evidence.
- `general-simpson-rule-theory-lean-horizon` marks the missing theorem route.

Trust boundary:

```text
untrusted fast search -> Simpson panel, quadrature value, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA evidence
```
