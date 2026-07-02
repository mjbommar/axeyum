# Finite QR Decomposition Checks

This lesson follows
[finite-qr-decomposition-v0](../../../artifacts/examples/math/finite-qr-decomposition-v0/).
It shows how Axeyum treats an exact QR-style factorization as a finite rational
matrix check, not as a floating-point linear algebra algorithm.

## The Fixed Factorization

The pack fixes:

```text
Q = [  3/5  4/5 ]
    [ -4/5  3/5 ]

R = [ 5  1 ]
    [ 0  2 ]
```

The checked finite replay recomputes:

```text
Q^T Q = I
R is upper triangular
Q R = [  3  11/5 ]
      [ -4   2/5 ]
```

All arithmetic is exact rational arithmetic. There is no floating-point
roundoff and no appeal to a numerical QR implementation.

## The Bad Row

The malformed row claims the bottom-right product entry is `1/2`. Replay
recomputes the entry:

```text
(-4/5) * 1 + (3/5) * 2 = 2/5
```

The source-linked QF_LRA artifact checks the final conflict:

```text
qr_product_11 = 2/5
qr_product_11 = 1/2
```

That produces checked Farkas evidence for the finite arithmetic contradiction.

## Trust Boundary

```text
untrusted fast search -> candidate Q/R factors or false product entry
trusted small checking -> exact rational orthogonality/product replay and checked Farkas evidence
theorem horizon       -> QR existence, QR algorithms, least-squares theory, conditioning, stability
```

The checker does not trust a factorization routine, a Gram-Schmidt
implementation, Householder reflection code, or floating-point orthogonality.
It trusts only exact replay of the listed matrices plus the small checked
equality conflict.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-qr-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_qr_decomposition_bad_product_entry_artifact_emits_checked_farkas
python3 scripts/query-foundational-resources.py checks --pack finite-qr-decomposition-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the malformed product
entry row has checked Farkas evidence, and the general QR theory row remains
`lean-horizon`.
