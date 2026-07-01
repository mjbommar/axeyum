# Finite Projected Gradient Checks

This lesson follows
[finite-projected-gradient-v0](../../../artifacts/examples/math/finite-projected-gradient-v0/)
from one exact constrained gradient step through interval projection and
checked Farkas evidence. It is a finite projected-gradient certificate, not a
general convergence theorem.

## Concept

Projected gradient takes an ordinary gradient step and then projects the trial
point back into the feasible set:

```text
x_trial = x - alpha * grad f(x)
x_next = projection_C(x_trial)
```

The resource fixes the exact rational quadratic and interval constraint:

```text
f(x) = (x - 2)^2
C = [0, 1]
x0 = 0
alpha = 1/2
```

## What Gets Checked

The pack has seven rows:

| Row | Result | Evidence |
|---|---|---|
| `projected-gradient-gradient-replay` | `sat` | replay-only |
| `unconstrained-step-replay` | `sat` | replay-only |
| `interval-projection-replay` | `sat` | replay-only |
| `projected-descent-replay` | `sat` | replay-only |
| `bad-projected-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-projected-decrease-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-projected-gradient-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not use floating-point
rounding, tolerances, or numerical approximations.

## Gradient And Trial Step

For

```text
f(x) = (x - 2)^2
```

the derivative at `x = 0` is:

```text
grad f(0) = -4
```

The unconstrained step is:

```text
x_trial = 0 - (1/2) * (-4) = 2
```

The validator recomputes both the derivative and the trial point.

## Interval Projection

The trial point is outside the feasible interval:

```text
x_trial = 2
C = [0, 1]
```

Projection clamps it to the upper endpoint:

```text
projection of 2 onto [0,1] = 1
distance = |2 - 1| = 1
```

This is the trusted-small-checking part. A search procedure can propose the
step size and trial point; the validator independently recomputes the clamp.

## Projected Descent

The objective values are:

```text
f(0) = 4
f(1) = 1
decrease = 3
```

This checks one exact constrained step. It does not prove a rate theorem or
general convergence.

## Bad Projection Row

The malformed row claims that `3/2` is a feasible projected point for `[0,1]`:

```text
claimed projected point = 3/2
upper bound = 1
violation = 1/2
```

The source SMT-LIB artifact fixes the claimed point as `3/2` and also asserts
it is at most `1`:

```smt2
(set-logic QF_LRA)
(declare-const claimed_projected_x Real)
(assert (= claimed_projected_x (/ 3 2)))
(assert (<= claimed_projected_x 1))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## Bad Decrease Row

The second malformed row keeps the same projected step but claims the decrease
is `4`:

```text
computed decrease = f(0) - f(1) = 4 - 1 = 3
claimed decrease = 4
```

The source SMT-LIB artifact fixes the same decrease to both values:

```smt2
(set-logic QF_LRA)
(declare-const projected_decrease Real)
(assert (= projected_decrease 3))
(assert (= projected_decrease 4))
(check-sat)
```

That keeps projected descent in the same trust story: exact replay computes the
finite objective values, and checked Farkas evidence rejects the malformed
decrease equality.

## What This Does Not Prove

The pack does not prove projected-gradient convergence for arbitrary closed
convex sets or smooth convex functions. It does not prove constraint
qualifications, active-set identification, proximal-gradient variants,
stochastic variants, rates, or floating-point stability.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite exact interval projection: checked now
general projected-gradient theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-projected-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_projected_gradient_bad_
```
