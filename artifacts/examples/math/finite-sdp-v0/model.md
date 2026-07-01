# Model

The source object is the two-by-two SDP slice:

```text
minimize <C, X>
subject to <I, X> = 1
           X is positive semidefinite

C = [[1, 0],
     [0, 2]]
```

The committed primal witness is:

```text
X = [[1, 0],
     [0, 0]]
```

The trace constraint is `<I, X> = 1`, and the objective is `<C, X> = 1`.

For a symmetric two-by-two matrix

```text
[[a, b],
 [b, c]]
```

the finite replay row checks positive semidefiniteness by the principal minors
`a >= 0`, `c >= 0`, and `ac - b^2 >= 0`. This is the full two-by-two principal
minor check for the listed finite matrices; it is not a proof of general SDP
duality.

The dual witness is `y = 1`. The slack matrix is:

```text
S = C - yI
  = [[0, 0],
     [0, 1]]
```

The slack matrix is positive semidefinite by the same principal-minor replay,
the dual objective is `y = 1`, and the primal-dual gap is `0`.

The checked bad row changes the claimed objective to `0`. Exact replay computes
`<C, X> = 1`, so the claimed objective has error `1`.

The checked bad duality-gap row keeps the same primal and dual witness but
claims gap `1/2`. Exact replay computes:

```text
<C, X> - y = 1 - 1 = 0
```

so the malformed gap claim has error `1/2`.

The checked bad slack-entry row keeps the same dual witness but claims the
bottom-right entry of `S` is `1/2`. Exact replay computes:

```text
S_11 = 1
```

so the malformed slack-entry claim has gap `1/2`.
