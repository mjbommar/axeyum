# Model

The finite witness is one exact rational unshifted QR step:

```text
Q = [[3/5, 4/5], [-4/5, 3/5]]
R = [[5, 2], [0, 1]]
A0 = Q*R = [[3, 2], [-4, -1]]
A1 = R*Q = [[7/5, 26/5], [-4/5, 3/5]]
```

Replay obligations:

- `Q^T*Q = I` and `Q*Q^T = I`;
- `R` is upper triangular with diagonal `[5, 1]`;
- `Q*R = A0`;
- `R*Q = A1`;
- `Q^T*A0*Q = A1`;
- `trace(A0) = trace(A1) = 2`;
- `det(A0) = det(A1) = 5`.

The bad source row claims `A1[0,0] = 2`; exact replay reads
`A1[0,0] = 7/5`.
