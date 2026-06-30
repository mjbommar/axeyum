# Finite Proximal Gradient Checks

This lesson follows
[finite-proximal-gradient-v0](../../../artifacts/examples/math/finite-proximal-gradient-v0/)
from one exact nonsmooth optimization step through soft-threshold replay and
checked Farkas evidence. It is a finite proximal-gradient certificate, not a
general convergence theorem.

## Concept

Proximal gradient splits a composite objective into a smooth part and a
nonsmooth part:

```text
F(x) = f(x) + g(x)
```

It takes an ordinary gradient step on `f`, then applies the proximal operator
for `g`:

```text
x_trial = x - alpha * grad f(x)
x_next = prox_{alpha g}(x_trial)
```

The resource fixes:

```text
f(x) = 1/2 * (x - 3)^2
g(x) = |x|
x0 = 0
alpha = 1/2
```

## What Gets Checked

The pack has six rows:

| Row | Result | Evidence |
|---|---|---|
| `proximal-gradient-gradient-replay` | `sat` | replay-only |
| `proximal-trial-step-replay` | `sat` | replay-only |
| `soft-threshold-prox-replay` | `sat` | replay-only |
| `composite-decrease-replay` | `sat` | replay-only |
| `bad-proximal-point-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-proximal-gradient-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not use floating-point
rounding, tolerances, or numerical approximations.

## Gradient And Trial Step

For

```text
f(x) = 1/2 * (x - 3)^2
```

the derivative at `x = 0` is:

```text
grad f(0) = -3
```

The ordinary gradient trial point is:

```text
x_trial = 0 - (1/2) * (-3) = 3/2
```

The validator recomputes both the derivative and the trial point.

## Soft Threshold

For `g(x)=|x|`, the proximal map is soft thresholding:

```text
prox(v) = sign(v) * max(|v| - alpha * lambda, 0)
```

Here `v = 3/2` and `alpha * lambda = 1/2`, so:

```text
prox(3/2) = 1
```

The positive-branch optimality residual is:

```text
(1 - 3/2) / (1/2) + 1 = 0
```

That zero residual is the trusted-small-checking part. A search procedure can
propose the trial point and prox point; the validator recomputes the residual
from exact rationals.

## Composite Decrease

The composite objective values are:

```text
F(0) = 9/2
F(1) = 3
decrease = 3/2
```

This checks one exact proximal-gradient step. It does not prove a rate theorem
or general convergence.

## Bad Proximal Point Row

The malformed row claims that `1/4` satisfies the positive-branch optimality
equation:

```text
claimed prox point = 1/4
residual = (1/4 - 3/2) / (1/2) + 1 = -3/2
error = 3/2
```

The source SMT-LIB artifact fixes the replayed error as `3/2` and also asserts
that the error is zero:

```smt2
(set-logic QF_LRA)
(declare-const proximal_optimality_error Real)
(assert (= proximal_optimality_error (/ 3 2)))
(assert (= proximal_optimality_error 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## What This Does Not Prove

The pack does not prove proximal-gradient convergence for arbitrary composite
convex objectives. It does not prove proper lower-semicontinuity facts, step-size
conditions, rate theorems, stochastic variants, active-set identification, or
floating-point stability.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite exact L1 proximal step: checked now
general proximal-gradient theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-proximal-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_proximal_gradient_bad_proximal_point_artifact_emits_checked_farkas
```
