# Model

All scalars are exact rationals written as strings accepted by Python's
`Fraction` type. Matrices are row-major arrays and vectors are arrays of
fraction strings.

The fixed matrix is:

```text
A = [[2, 1],
     [1, 2]]
```

## Eigenpairs

The validator checks:

```text
A * [1, 1]  = 3 * [1, 1]
A * [1,-1]  = 1 * [1,-1]
```

It also checks that the eigenvectors are orthogonal:

```text
[1,1] dot [1,-1] = 0
```

## Rayleigh Quotient

For `v = [1,1]`, the validator recomputes:

```text
v^T A v = 6
v^T v = 2
(v^T A v) / (v^T v) = 3
```

## Spectral Decomposition

The decomposition is:

```text
P = [[1, 1],
     [1,-1]]

D = [[3,0],
     [0,1]]

P^-1 = [[1/2,  1/2],
        [1/2, -1/2]]
```

The validator checks `P*D*P^-1 = A` and `P*P^-1 = I` exactly.

## Bad Eigenpair Certificate

For the rejected eigenpair claim, exact replay computes:

```text
A * [1,1] = [3,3]
2 * [1,1] = [2,2]
```

The linked proof artifact uses the first component:

```text
eigen_image_0 = 3
eigen_image_0 = 2
```

The pack ties that `QF_LRA` contradiction to a resource-backed
`UnsatFarkas` regression.

These are finite exact checks, not a proof of the general spectral theorem.
