# Finite Newton Step

This pack records one exact two-variable Newton step over rational arithmetic.
It is a finite numerical-optimization resource, not a theorem about Newton's
method.

The fixed quadratic is:

```text
f(x,y) = x^2 + x*y + 2*y^2 - 4*x - 6*y
```

At the start point `(0,0)`, exact replay computes:

```text
gradient = [-4, -6]
Hessian  = [[2, 1],
            [1, 4]]
det(Hessian) = 7
```

The Newton direction solves:

```text
Hessian * direction = -gradient = [4, 6]
direction = [10/7, 8/7]
next = [10/7, 8/7]
```

The checked QF_LRA/Farkas row isolates one malformed claim: the next
`x`-coordinate is asserted to be `3/2` even though exact replay computes
`10/7`.

## Boundary

This resource checks one finite rational Newton step, the linear solve behind
it, and the objective decrease for the listed quadratic. It does not prove
Newton convergence, globalization, trust-region methods, line-search
termination, conditioning, floating-point stability, or arbitrary
second-order optimization theory.

## Validate

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-newton-step-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_newton_step_bad_coordinate_artifact_emits_checked_farkas
```
