# Finite Line Search Checks

This lesson follows
[finite-line-search-v0](../../../artifacts/examples/math/finite-line-search-v0/)
from one exact Armijo backtracking step through rejected-step replay,
accepted-step replay, and checked Farkas evidence. It is a finite line-search
certificate, not a general convergence theorem.

## Concept

Line search chooses a step size along a proposed descent direction. Armijo
backtracking accepts a step when it gives enough decrease:

```text
f(x + alpha*d) <= f(x) + c*alpha*grad(f)(x)*d
```

The resource fixes the exact rational quadratic:

```text
f(x) = x^2
x0 = 1
direction = -2
c = 1/4
```

## What Gets Checked

The pack has five rows:

| Row | Result | Evidence |
|---|---|---|
| `descent-direction-replay` | `sat` | replay-only |
| `armijo-rejection-replay` | `sat` | replay-only |
| `armijo-acceptance-replay` | `sat` | replay-only |
| `bad-armijo-acceptance-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-line-search-convergence-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not use floating-point
rounding, tolerances, or numerical approximations.

## Descent Direction

For

```text
f(x) = x^2
```

the derivative at `x = 1` is:

```text
grad f(1) = 2
grad f(1) * (-2) = -4
```

The validator recomputes the derivative and checks that the directional
derivative is negative.

## Rejected Trial Step

The first trial step is `alpha = 1`:

```text
x_trial = 1 + 1*(-2) = -1
f(x_trial) = 1
Armijo rhs = 1 + (1/4)*1*(-4) = 0
violation = 1 - 0 = 1
```

Because the violation is positive, the trial step does not satisfy Armijo
decrease.

## Accepted Backtracked Step

After one backtrack by factor `1/2`, the accepted step is:

```text
alpha = 1/2
x_accept = 1 + (1/2)*(-2) = 0
f(x_accept) = 0
Armijo rhs = 1 + (1/4)*(1/2)*(-4) = 1/2
slack = 1/2
```

This checks one exact backtracking trace. A search procedure can propose the
step sizes; the trusted checker recomputes the candidate points, objective
values, right-hand sides, violation, and slack.

## Bad Armijo Row

The malformed row claims the rejected trial step satisfies Armijo:

```text
replayed violation = 1
claimed violation <= 0
```

The source SMT-LIB artifact fixes the violation as `1` and also asserts it is
nonpositive:

```smt2
(set-logic QF_LRA)
(declare-const armijo_violation Real)
(assert (= armijo_violation 1))
(assert (<= armijo_violation 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## What This Does Not Prove

The pack does not prove line-search termination for arbitrary smooth functions.
It does not prove Wolfe conditions, global convergence, rates, stochastic
variants, projected-gradient variants, or floating-point stability.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite exact Armijo trace: checked now
general line-search theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-line-search-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_line_search_bad_armijo_artifact_emits_checked_farkas
```
