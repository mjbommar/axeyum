# Model

The finite witness is the exact rational polar decomposition:

```text
U = [[3/5, 4/5], [-4/5, 3/5]]
P = [[2, 0], [0, 5]]
A = U*P = [[6/5, 4], [-8/5, 3]]
```

Replay obligations:

- `U^T*U = I` and `U*U^T = I`;
- `P` is symmetric positive diagonal with diagonal `[2, 5]` and leading
  minors `[2, 10]`;
- `U*P = A`;
- `A^T*A = P^2 = [[4,0],[0,25]]`;
- `trace(P) = 7`;
- `det(A) = det(U)*det(P) = 10`.

The bad source row claims `P[1,1] = 4`; exact replay reads `P[1,1] = 5`.
