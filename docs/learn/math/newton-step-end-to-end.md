# End To End: Finite Newton Step

This lesson follows
[finite-newton-step-v0](../../../artifacts/examples/math/finite-newton-step-v0/).
It shows how Axeyum treats a multivariate Newton step as exact rational
replay plus one small checked contradiction.

## The Fixed Problem

The source polynomial is:

```text
f(x,y) = x^2 + x*y + 2*y^2 - 4*x - 6*y
```

At `(0,0)`, exact symbolic differentiation gives:

```text
grad f(0,0) = [-4, -6]
H = [[2,1],
     [1,4]]
```

The leading principal minors are:

```text
2, 7
```

That is a fixed positive-definite shadow for this two-by-two Hessian. It is
not a general convexity or Newton-convergence theorem.

## The Newton System

Newton's direction solves:

```text
H * d = -grad f(0,0)
[[2,1],[1,4]] * d = [4,6]
```

Exact rational replay computes:

```text
d = [10/7, 8/7]
next = [10/7, 8/7]
grad f(next) = [0,0]
f(0,0) = 0
f(next) = -44/7
decrease = 44/7
```

The trusted finite work is small arithmetic: symbolic derivative replay,
matrix-vector multiplication, point update, and exact objective evaluation.

## The Bad Claim

The malformed source row says:

```text
next_x = 3/2
```

Replay computes:

```text
next_x = 10/7
```

The checked SMT-LIB artifact keeps only that final scalar conflict:

```text
newton_next_x = 10/7
newton_next_x = 3/2
```

This is the same trust pattern as the other finite optimization rows:

```text
finite replay        -> compute the derivative, Hessian solve, step, and value
checked evidence     -> reject the malformed scalar coordinate claim
theorem horizon      -> convergence, globalization, conditioning, floating point
```

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-newton-step-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_newton_step_bad_coordinate_artifact_emits_checked_farkas
python3 scripts/query-foundational-resources.py checks --pack finite-newton-step-v0 --route Farkas --proof-status checked --require-any
```

The first command replays the finite data. The second command checks the
source-linked QF_LRA/Farkas artifact. The third command shows the public query
row that a consumer can display.

## Boundary

This resource does not claim Newton's method converges, does not justify
damped or trust-region Newton methods, and does not say anything about
floating-point implementations. Those require theorem reconstruction or
separate numerical-honesty resources.
