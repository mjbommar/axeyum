# Model

The pack fixes one rational orthogonal diagonalization:

```text
q1 = [ 3/5, -4/5]
q2 = [ 4/5,  3/5]

Q = [ q1 q2 ]
D = diag(1, 4)
A = Q*D*Q^T
```

All claims are over exact rationals. There is no floating-point rounding model
and no search claim: a solver may discover the same data, but the resource only
trusts replay of the committed witness and the checked scalar contradiction.

The malformed row claims the second diagonal/eigenvalue entry is `5`; exact
replay computes `4`.
