# Finite Active-Set Quadratic Program Checks

This lesson follows
[finite-active-set-qp-v0](../../../artifacts/examples/math/finite-active-set-qp-v0/)
from one exact active-set witness through KKT replay, inactive-constraint
replay, and checked Farkas evidence. It is a finite active-set certificate, not
a general active-set convergence theorem.

## Concept

An active-set method guesses which inequality constraints are tight at the
solution, solves the equality-constrained subproblem on that face, and checks
the remaining constraints and multipliers.

The resource fixes:

```text
f(x,y) = (x - 2)^2 + (y - 1)^2
x <= 1
y >= 0
```

The unconstrained minimizer `(2,1)` violates `x <= 1`, so the active set fixes
the face `x = 1`. On that face, the free-coordinate minimizer is `y = 1`.

## What Gets Checked

The pack has six rows:

| Row | Result | Evidence |
|---|---|---|
| `unconstrained-minimizer-replay` | `sat` | replay-only |
| `active-face-candidate-replay` | `sat` | replay-only |
| `active-set-kkt-replay` | `sat` | replay-only |
| `inactive-constraint-slack-replay` | `sat` | replay-only |
| `bad-active-set-free-gradient-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-active-set-method-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not use floating-point
rounding, numerical tolerances, or heuristic optimization stopping criteria.

## Active Face Replay

The unconstrained point is:

```text
(2,1)
grad f(2,1) = (0,0)
```

It is not feasible, because:

```text
x - 1 = 1
```

The active face is therefore `x = 1`. Solving the free coordinate gives:

```text
(x,y) = (1,1)
f(1,1) = 1
grad f(1,1) = (-2,0)
```

## KKT Replay

Encode the constraints as:

```text
a = (1,0),  a . z <= 1
b = (0,-1), b . z <= 0
```

At `(1,1)`, the active multiplier is `lambda = 2` and the inactive multiplier
is `mu = 0`:

```text
grad f(1,1) + 2*a + 0*b = (0,0)
active slack = 0
inactive slack = 1
```

The validator also checks the complementarity products:

```text
2 * 0 = 0
0 * 1 = 0
```

## Bad Active-Set Row

The malformed row claims that `(1,0)` solves the same active-face subproblem.
It is feasible, but it is not stationary along the free coordinate:

```text
grad f(1,0) = (-2,-2)
grad f(1,0) + 2*a + 0*b = (0,-2)
free-coordinate stationarity error = 2
```

The source SMT-LIB artifact fixes the replayed error as `2` and also asserts
that the error is nonpositive:

```smt2
(set-logic QF_LRA)
(declare-const free_stationarity_error Real)
(assert (= free_stationarity_error 2))
(assert (<= free_stationarity_error 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## What This Does Not Prove

The pack does not prove that an active-set method terminates for every convex
quadratic program. It does not prove anti-cycling rules, degeneracy handling,
warm-start correctness, finite termination, convergence rates, or numerical
stability.

Those remain named in the Lean-horizon row:

```text
finite active-set replay: checked now
general active-set method theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-active-set-qp-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_active_set_qp_bad_free_gradient_artifact_emits_checked_farkas
```
