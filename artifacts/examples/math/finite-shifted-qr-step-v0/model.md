# Model

The finite witness is one exact rational shifted QR step:

```text
mu = 1
Q = [[3/5, 4/5], [-4/5, 3/5]]
R = [[5, 2], [0, 1]]
A0 = Q*R + mu*I = [[4, 2], [-4, 0]]
A1 = R*Q + mu*I = [[12/5, 26/5], [-4/5, 8/5]]
```

Replay obligations:

- `Q^T*Q = I` and `Q*Q^T = I`;
- `R` is upper triangular with diagonal `[5, 1]`;
- `A0 - mu*I = Q*R`;
- `A1 = R*Q + mu*I`;
- `Q^T*A0*Q = A1`;
- `trace(A0) = trace(A1) = 4`;
- `det(A0) = det(A1) = 8`.

The bad source row claims `A1[1,1] = 2`; exact replay reads
`A1[1,1] = 8/5`.
