# Finite Cholesky Decomposition Checks

This page follows
[finite-cholesky-decomposition-v0](../../../artifacts/examples/math/finite-cholesky-decomposition-v0/).
It shows how Axeyum treats a Cholesky-style factorization as exact finite
rational replay, not as a floating-point numerical algorithm.

## The Finite Object

The pack fixes:

```text
L = [ 2  0 ]
    [ 1  3 ]

A = [ 4   2 ]
    [ 2  10 ]
```

The trusted replay checks:

```text
L is lower triangular
diag(L) = 2, 3 > 0
L^T = [ 2  1 ]
      [ 0  3 ]
L L^T = A
leading principal minors of A are 4 and 36
```

Those facts are enough for a fixed two-by-two positive-definite shadow. They
are not a general theorem about every positive-definite matrix.

## The Bad Claim

The bottom-right entry of `L L^T` is:

```text
1 * 1 + 3 * 3 = 10
```

The malformed row claims it is `9`. The source SMT-LIB artifact isolates only
that final contradiction:

```text
cholesky_product_11 = 10
cholesky_product_11 = 9
```

The QF_LRA route emits `UnsatFarkas` evidence and independently rechecks it.

## Trust Boundary

```text
finite replay        -> recompute L shape, L*L^T, symmetry, and leading minors
checked evidence     -> reject the malformed product-entry equality
theorem horizon      -> general Cholesky existence, algorithms, conditioning, stability
```

This keeps the resource aligned with Axeyum's core pattern: untrusted fast
search can propose a factorization or a corrupted row, but trusted small
checking recomputes the exact claim being displayed.

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cholesky-decomposition-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_cholesky_decomposition_bad_product_entry_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks --pack finite-cholesky-decomposition-v0 --route Farkas --proof-status checked --require-any
```

The first command checks the finite model, the second command checks the
Farkas evidence route, and the third command verifies that consumers can find
the promoted checked row through the public JSON/query boundary.
