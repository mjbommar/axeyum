# Model

The spline uses exact rational data:

```text
knots: 0, 1, 2
values: 0, 1, 0
second derivatives: 0, -3, 0
```

The two cubic pieces are represented by coefficient lists in ascending powers:

```text
S0(x) = 3/2*x - 1/2*x^3
S1(x) = -1 + 9/2*x - 3*x^2 + 1/2*x^3
```

The validator checks:

- `S0(0)=0`, `S0(1)=1`, `S1(1)=1`, `S1(2)=0`;
- `S0'(1)=S1'(1)=0`;
- `S0''(1)=S1''(1)=-3`;
- `S0''(0)=0` and `S1''(2)=0`;
- `S0(1/2)=S1(3/2)=11/16`.

This is a finite exact assembly transcript, not a theorem about arbitrary
knots or spline spaces.
