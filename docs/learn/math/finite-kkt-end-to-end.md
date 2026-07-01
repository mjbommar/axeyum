# Finite KKT Checks

This lesson follows
[finite-kkt-v0](../../../artifacts/examples/math/finite-kkt-v0/) from a tiny
constrained quadratic through exact KKT replay and checked Farkas evidence. It
is a finite optimization certificate story, not a general KKT theorem.

## Concept

KKT conditions package the local algebra of constrained optimization:
stationarity, primal feasibility, dual feasibility, and complementary
slackness. In a convex setting, theorem-level KKT results require assumptions
such as constraint qualifications and proof of sufficiency.

The resource starts smaller. It fixes one rational quadratic and one linear
constraint:

```text
minimize (x - 2)^2
subject to x <= 1
```

The candidate is `x = 1` with multiplier `lambda = 2`.

## What Gets Checked

The pack has five rows:

| Row | Result | Evidence |
|---|---|---|
| `finite-quadratic-grid-minimum-replay` | `sat` | replay-only |
| `kkt-stationarity-replay` | `sat` | replay-only |
| `complementary-slackness-replay` | `sat` | replay-only |
| `bad-kkt-stationarity-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-kkt-complementarity-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-kkt-sufficiency-lean-horizon` | `not-run` | Lean horizon |

The replay rows use exact rational arithmetic. They do not sample floating
points and they do not rely on numerical tolerances.

## Finite Grid Replay

The resource lists a feasible grid:

```text
x = -1  ->  f(x) = 9
x =  0  ->  f(x) = 4
x =  1  ->  f(x) = 1
```

The validator recomputes `(x - 2)^2` at each listed point and checks that each
point satisfies `x <= 1`. It also checks that the listed candidate `x = 1` has
the smallest value on this finite grid.

That is useful, but it is not the theorem. A finite grid can miss feasible
points.

## KKT Replay

For the active constraint `g(x) = x - 1 <= 0`, the normal is `1`. At `x = 1`:

```text
f'(x) = 2x - 4
f'(1) = -2
lambda = 2
f'(1) + lambda * 1 = -2 + 2 = 0
```

The same witness satisfies complementary slackness:

```text
g(1) = 0
lambda >= 0
lambda * g(1) = 2 * 0 = 0
```

This is the trusted-small-checking part. A search procedure can propose the
active set and multiplier; the validator independently recomputes the derivative
and the residual.

## Bad Stationarity Row

The malformed row changes only the multiplier:

```text
lambda = 1
f'(1) + lambda * 1 = -2 + 1 = -1
```

The source SMT-LIB artifact fixes the resulting stationarity error from zero as
`1` and also claims it is zero:

```smt2
(set-logic QF_LRA)
(declare-const stationarity_error Real)
(assert (= stationarity_error 1))
(assert (= stationarity_error 0))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## Bad Complementarity Row

The second malformed row leaves the valid point and multiplier alone but claims
the complementary-slackness product is `1`:

```text
g(1) = 1 - 1 = 0
lambda * g(1) = 2 * 0 = 0
```

The source SMT-LIB artifact fixes the resulting complementarity error as `1`
and also claims it is zero:

```smt2
(set-logic QF_LRA)
(declare-const complementarity_error Real)
(assert (= complementarity_error 1))
(assert (= complementarity_error 0))
(check-sat)
```

That keeps complementarity in the same trust story as stationarity: exact
replay computes the small rational product, and the checked Farkas route rejects
the final malformed equality.

## What This Does Not Prove

The pack does not prove general KKT necessity or sufficiency. It does not prove
Slater conditions, LICQ/MFCQ, SDP duality, sensitivity theory, or convergence of
optimization algorithms.

Those are named in the Lean-horizon row so the boundary is visible:

```text
finite KKT replay: checked now
general KKT theorem: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-kkt-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_kkt_bad_stationarity_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_kkt_bad_complementarity_artifact_emits_checked_farkas
```

The validator proves the pack data is internally consistent. The cargo test
proves the bad stationarity and bad complementarity source artifacts reach
checked Farkas evidence.
