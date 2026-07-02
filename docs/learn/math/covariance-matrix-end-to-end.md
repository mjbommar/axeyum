# Exact Finite Covariance Matrix Checks

This page follows
[finite-covariance-matrix-v0](../../../artifacts/examples/math/finite-covariance-matrix-v0/).
It shows how Axeyum treats a covariance matrix as exact finite rational replay,
not as floating-point statistics or asymptotic inference.

## The Finite Object

The pack fixes three observations:

```text
(1, 0), (2, 1), (4, 1)
```

The trusted replay checks:

```text
mean = (7/3, 2/3)
centered rows =
  (-4/3, -2/3)
  (-1/3,  1/3)
  ( 5/3,  1/3)

centered Gram =
  [ 14/3  4/3 ]
  [  4/3  2/3 ]

covariance =
  [ 14/9  4/9 ]
  [  4/9  2/9 ]

leading principal minors = 14/9 and 4/27
```

Those facts are enough for a fixed two-by-two positive-semidefinite shadow.
They are not a general theorem about every covariance matrix or estimator.

## The Bad Claim

The off-diagonal covariance entry is:

```text
((-4/3) * (-2/3) + (-1/3) * (1/3) + (5/3) * (1/3)) / 3 = 4/9
```

The malformed row claims it is `1/2`. The source SMT-LIB artifact isolates only
that final contradiction:

```text
covariance_01 = 4/9
covariance_01 = 1/2
```

The QF_LRA route emits `UnsatFarkas` evidence and independently rechecks it.

## Trust Boundary

```text
finite replay        -> recompute mean, centered rows, Gram matrix, covariance, minors
checked evidence     -> reject the malformed covariance-entry equality
theorem horizon      -> inference, PCA, asymptotics, estimator guarantees, floating point
```

This keeps the resource aligned with Axeyum's core pattern: untrusted fast
search can propose a covariance table or a corrupted row, but trusted small
checking recomputes the exact claim being displayed.

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-covariance-matrix-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_covariance_matrix_bad_entry_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked --require-any
```

The first command checks the finite model, the second command checks the
Farkas evidence route, and the third command verifies that consumers can find
the promoted checked row through the public JSON/query boundary.
