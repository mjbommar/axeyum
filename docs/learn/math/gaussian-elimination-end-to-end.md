# Finite Gaussian Elimination Checks

This page follows
[finite-gaussian-elimination-v0](../../../artifacts/examples/math/finite-gaussian-elimination-v0/).
It shows how Axeyum treats one elimination transcript as exact rational replay,
not as a theorem about every elimination algorithm.

## The Finite Object

The pack fixes:

```text
A = [ 2  1 ]    b = [  5 ]
    [ 4  5 ]        [ 17 ]
```

The first pivot is `2`. The row-two multiplier is `4 / 2 = 2`, so:

```text
[4, 5 | 17] - 2 * [2, 1 | 5] = [0, 3 | 7]
```

The resulting triangular system is:

```text
U = [ 2  1 ]    y = [ 5 ]
    [ 0  3 ]        [ 7 ]
```

Back-substitution gives `x = [4/3, 7/3]`, and exact replay checks both
`U*x = y` and `A*x = b`.

## The Bad Claim

The malformed row claims that the eliminated second right-hand-side entry is
`8`. The replayed row operation computes:

```text
17 - 2 * 5 = 7
```

The source SMT-LIB artifact isolates only that scalar contradiction:

```text
eliminated_rhs_1 = 7
eliminated_rhs_1 = 8
```

The QF_LRA route emits `UnsatFarkas` evidence and independently rechecks it.

## Trust Boundary

```text
finite replay        -> recompute pivot, multiplier, row update, determinant, and back-substitution
checked evidence     -> reject the malformed eliminated-RHS equality
theorem horizon      -> general elimination correctness, pivoting, conditioning, stability
```

This keeps the resource aligned with Axeyum's core pattern: untrusted fast
search may propose an elimination transcript or a corrupted scalar row, while
trusted small checking recomputes the exact claim before accepting it.

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gaussian-elimination-v0

cargo test -p axeyum-solver --test math_resource_lra_routes finite_gaussian_elimination_bad_rhs_artifact_emits_checked_farkas

python3 scripts/query-foundational-resources.py checks --pack finite-gaussian-elimination-v0 --route Farkas --proof-status checked --require-any
```

The first command checks the finite transcript, the second command checks the
Farkas evidence route, and the third command verifies that consumers can find
the promoted checked row through the public JSON/query boundary.
