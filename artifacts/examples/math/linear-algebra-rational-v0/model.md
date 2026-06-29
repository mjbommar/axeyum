# Model

All scalar values are exact rationals written as strings accepted by Python's
`Fraction` type. Matrices are row-major arrays of fraction strings; vectors are
arrays of fraction strings.

Examples:

```json
{
  "matrix": [["2", "1"], ["1", "-1"]],
  "vector": ["1", "2"],
  "rhs": ["4", "-1"]
}
```

No floating-point arithmetic is used.

## Checks

### Matrix-Vector Solution

For

```text
A = [[2, 1],
     [1, -1]]
x = [1, 2]
b = [4, -1]
```

the pack checks `A*x = b` exactly.

### LU Factorization

For

```text
A = [[2, 1],
     [4, 3]]
L = [[1, 0],
     [2, 1]]
U = [[2, 1],
     [0, 1]]
```

the pack checks `L*U = A` exactly, with `L` lower triangular and unit diagonal
and `U` upper triangular.

### Singular Inconsistent System

The system

```text
x + y = 1
2x + 2y = 3
```

is inconsistent because the second left-hand row is exactly `2` times the first
left-hand row, but the right-hand side is not `2` times the first right-hand
side. This is a tiny replay certificate for inconsistency, not yet a general
Farkas certificate by itself. The Axeyum regression also checks the same fixed
system as a conjunctive `QF_LRA` query:

```text
x + y = 1
2*x + 2*y = 3
```

That query emits `UnsatFarkas` evidence, and the certificate arithmetic is
rechecked independently.

These fixed checks are not general theorem proofs. They are exact replay
targets; the listed inconsistent linear system now has QF_LRA/Farkas evidence.
