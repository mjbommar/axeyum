# Finite Gaussian Elimination Checks

Audience: learners, educators, solver contributors, and proof contributors.

This pack turns one exact Gaussian-elimination transcript into a replayable
resource. It checks the row operation, pivot multiplier, determinant factor, and
back-substitution result for a fixed rational linear system. The malformed row
claims the eliminated right-hand-side entry is `8`; exact replay computes `7`,
and a separate QF_LRA artifact owns the checked Farkas refutation.

## Scope

The fixed system is:

```text
A = [ 2  1 ]    b = [  5 ]
    [ 4  5 ]        [ 17 ]
```

One elimination step uses multiplier `2`:

```text
row_2 <- row_2 - 2 row_1
```

which yields:

```text
U = [ 2  1 ]    y = [ 5 ]
    [ 0  3 ]        [ 7 ]
```

Back-substitution gives `x = [4/3, 7/3]`.

## Trust Boundary

- finite replay: recompute the multiplier, row operation, determinant pivot
  product, and back-substitution exactly over rationals;
- checked evidence: reject the malformed eliminated RHS claim through
  QF_LRA/Farkas evidence;
- theorem horizon: general pivoting correctness, rank-revealing elimination,
  stability, fill-in, and floating-point Gaussian-elimination algorithms.

## Commands

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gaussian-elimination-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gaussian_elimination_bad_rhs_artifact_emits_checked_farkas
python3 scripts/query-foundational-resources.py checks --pack finite-gaussian-elimination-v0 --route Farkas --proof-status checked --require-any
```
