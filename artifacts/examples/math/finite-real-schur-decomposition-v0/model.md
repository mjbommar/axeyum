# Model

The pack fixes one rational real Schur decomposition:

```text
Q = [[ 3/5, 4/5],
     [-4/5, 3/5]]

T = [[1, 2],
     [0, 4]]

A = Q*T*Q^T
```

All claims are over exact rationals. There is no floating-point rounding model
and no QR-iteration search claim: a solver may discover the same data, but the
resource only trusts replay of the committed witness and the checked scalar
contradiction.

The malformed row claims the superdiagonal entry `T[0,1]` is `3`; exact replay
computes `2`.
