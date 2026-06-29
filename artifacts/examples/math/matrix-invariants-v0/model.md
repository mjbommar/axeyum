# Model

All scalars are exact rationals written as strings accepted by Python's
`Fraction` type. Polynomials are coefficient lists in ascending degree order,
so `["3", "-4", "1"]` means:

```text
3 - 4*lambda + lambda^2
```

The fixed matrix is:

```text
A = [[2, 1],
     [1, 2]]
```

## Invariants

The validator recomputes:

```text
trace(A) = 4
det(A) = 3
chi_A(lambda) = lambda^2 - 4*lambda + 3
```

## Roots

The listed roots are checked by direct polynomial evaluation:

```text
chi_A(1) = 0
chi_A(3) = 0
```

## Cayley-Hamilton

The matrix square is:

```text
A^2 = [[5, 4],
       [4, 5]]
```

The validator checks the fixed matrix polynomial:

```text
A^2 - 4A + 3I = 0
```

This is a finite replay of one Cayley-Hamilton instance, not a proof of the
general theorem.

## Gershgorin Intervals

For each row, the center is the diagonal entry and the radius is the sum of
absolute off-diagonal entries:

```text
row 0: center 2, radius 1, interval [1,3]
row 1: center 2, radius 1, interval [1,3]
```

The listed eigenvalues `1` and `3` are checked to lie in the union of these
intervals.

## Bad Characteristic Polynomial Certificate

For the rejected characteristic-polynomial claim, exact replay checks the
witness root `lambda = 1`:

```text
actual characteristic value at 1 = 0
claimed polynomial value at 1 = 2
```

The linked proof artifact records the resulting exact-rational contradiction:

```text
characteristic_value_at_witness = 0
characteristic_value_at_witness = 2
```

The pack ties that `QF_LRA` contradiction to a resource-backed
`UnsatFarkas` regression.
