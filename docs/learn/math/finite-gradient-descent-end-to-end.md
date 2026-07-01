# Finite Gradient Descent Checks

This lesson follows
[finite-gradient-descent-v0](../../../artifacts/examples/math/finite-gradient-descent-v0/)
from one exact quadratic gradient step through descent replay, step-coordinate
replay, and checked Farkas evidence. It is a finite optimization-step
certificate, not a general convergence theorem.

## Concept

Gradient descent uses local derivative information to choose a new point:

```text
x_next = x - alpha * grad f(x)
```

For smooth convex functions, theorem-level claims require assumptions about
smoothness, convexity, step sizes, stopping criteria, and rates.

The resource starts smaller. It fixes the exact quadratic:

```text
f(x, y) = x^2 + 2y^2
```

and one step from `(1, 1)` with step size `1/4`.

## What Gets Checked

The pack has six rows:

| Row | Result | Evidence |
|---|---|---|
| `quadratic-gradient-replay` | `sat` | replay-only |
| `gradient-descent-step-replay` | `sat` | replay-only |
| `descent-bound-replay` | `sat` | replay-only |
| `bad-descent-value-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-step-coordinate-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-gradient-descent-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not use floating-point
rounding, tolerances, or numerical approximations.

## Gradient Replay

For

```text
f(x, y) = x^2 + 2y^2
```

the gradient and Hessian at `(1, 1)` are:

```text
grad f(1,1) = (2,4)
H = [[2,0],
     [0,4]]
```

The validator recomputes those entries from the listed quadratic matrix.

## Step Replay

The exact step is:

```text
alpha = 1/4
(1,1) - alpha * (2,4) = (1/2,0)
```

This is the trusted-small-checking part. A search procedure can propose the
step size and next point; the validator independently recomputes the update.

## Descent Replay

The objective values are:

```text
f(1,1) = 3
f(1/2,0) = 1/4
decrease = 11/4
```

The finite descent-bound row also checks:

```text
||grad f(1,1)||^2 = 20
alpha/2 * ||grad||^2 = 5/2
descent slack = 11/4 - 5/2 = 1/4
```

This checks one exact step. It does not prove a rate theorem.

## Bad Decrease Row

The malformed row changes only the claimed decrease:

```text
claimed decrease = 2
replayed decrease = 11/4
decrease error = 3/4
```

The source SMT-LIB artifact fixes the decrease error as `3/4` and also claims
it is zero:

```smt2
(set-logic QF_LRA)
(declare-const decrease_error Real)
(assert (= decrease_error (/ 3 4)))
(assert (= decrease_error 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## Bad Step Coordinate Row

The malformed row changes only the claimed x-coordinate of the next point:

```text
claimed next_x = 3/4
replayed next_x = 1 - (1/4) * 2 = 1/2
```

The source SMT-LIB artifact fixes `next_x` as `1/2` and also claims it is
`3/4`:

```smt2
(set-logic QF_LRA)
(declare-const next_x Real)
(assert (= next_x (/ 1 2)))
(assert (= next_x (/ 3 4)))
(check-sat)
```

This checks the step-update arithmetic as a separate exact-linear conflict from
the descent-value row.

## What This Does Not Prove

The pack does not prove gradient descent convergence for arbitrary smooth
convex functions. It does not prove line-search correctness, stochastic
gradient descent, projected-gradient convergence, acceleration, conditioning
rates, or floating-point stability.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite exact descent step: checked now
general convergence theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gradient-descent-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gradient_descent_bad_decrease_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gradient_descent_bad_step_coordinate_artifact_emits_checked_farkas
```
