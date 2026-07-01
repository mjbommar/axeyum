# Finite Wolfe Line-Search Checks

This lesson follows
[finite-wolfe-line-search-v0](../../../artifacts/examples/math/finite-wolfe-line-search-v0/)
from one exact line-search witness through Wolfe sufficient-decrease and
curvature replay, then through checked Farkas evidence for a bad minimizer and
bad curvature row. It is a finite Wolfe certificate, not a general line-search
convergence theorem.

## Concept

Wolfe line search strengthens simple sufficient decrease with a curvature
condition. For a smooth objective along a direction `d`, define:

```text
phi(alpha) = f(x + alpha*d)
```

The two finite conditions checked here are:

```text
phi(alpha) <= phi(0) + c1 * alpha * phi'(0)
|phi'(alpha)| <= c2 * |phi'(0)|
```

The resource fixes:

```text
f(x) = x^2
x0 = 1
d = -2
c1 = 1/4
c2 = 1/2
```

## What Gets Checked

The pack has seven rows:

| Row | Result | Evidence |
|---|---|---|
| `wolfe-descent-direction-replay` | `sat` | replay-only |
| `exact-line-minimizer-replay` | `sat` | replay-only |
| `bad-line-minimizer-rejected` | `unsat` | checked QF_LRA/Farkas |
| `wolfe-sufficient-decrease-replay` | `sat` | replay-only |
| `wolfe-curvature-replay` | `sat` | replay-only |
| `bad-wolfe-curvature-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-wolfe-line-search-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not use floating-point
rounding, tolerances, or numerical approximations.

## Descent And Exact Line Minimum

For

```text
f(x) = x^2
```

the derivative at `x = 1` is:

```text
grad f(1) = 2
```

With direction `d = -2`, the initial directional derivative is:

```text
phi'(0) = 2 * (-2) = -4
```

The accepted step is the exact one-dimensional minimizer:

```text
alpha = 1/2
x + alpha*d = 0
f(0) = 0
phi'(1/2) = 0
```

The malformed minimizer row claims the full step is the minimizer:

```text
claimed alpha = 1
claimed x = -1
replayed alpha = 1/2
replayed x = 0
```

The source SMT-LIB artifact fixes the minimizer step as `1/2` and also asserts
the malformed full step:

```smt2
(set-logic QF_LRA)
(declare-const minimizer_alpha Real)
(assert (= minimizer_alpha (/ 1 2)))
(assert (= minimizer_alpha 1))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## Wolfe Replay

The sufficient-decrease right-hand side is:

```text
1 + (1/4) * (1/2) * (-4) = 1/2
```

Since `f(0)=0`, sufficient decrease holds with slack `1/2`.

The curvature bound is:

```text
c2 * |phi'(0)| = (1/2) * 4 = 2
```

At the accepted step, `|phi'(1/2)| = 0`, so curvature holds with slack `2`.

## Bad Curvature Row

The malformed row claims that the full step `alpha = 1` satisfies the Wolfe
curvature bound:

```text
x(1) = -1
grad f(-1) = -2
phi'(1) = (-2) * (-2) = 4
curvature violation = 4 - 2 = 2
```

The source SMT-LIB artifact fixes the replayed violation as `2` and also
asserts that the violation is nonpositive:

```smt2
(set-logic QF_LRA)
(declare-const curvature_violation Real)
(assert (= curvature_violation 2))
(assert (<= curvature_violation 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## What This Does Not Prove

The pack does not prove that a Wolfe step exists for every smooth optimization
problem. It does not prove Zoutendijk-style convergence, rate theorems,
nonconvex convergence, stochastic line search, strong Wolfe variants, or
floating-point stability.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite exact Wolfe replay: checked now
general Wolfe line-search theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-wolfe-line-search-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_wolfe_line_search_bad_minimizer_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_wolfe_line_search_bad_curvature_artifact_emits_checked_farkas
```
