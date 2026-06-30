# Model

The finite cohomology model is encoded as:

- `vertices`: the declared vertex order;
- `simplices`: all non-empty simplices of the finite complex;
- `dimension`: the source cochain dimension;
- `cochain`: F2 values on all simplices of that dimension;
- `coboundary`: F2 values on all simplices one dimension higher.

Values are `0` or `1`. The validator checks simplex closure first, then
recomputes coboundary values from the finite boundary formula, reducing
coefficients modulo `2`.

For the three-edge circle:

```text
simplices = [a], [b], [c], [a,b], [a,c], [b,c]
```

the vertex potential:

```text
f(a) = 0
f(b) = 1
f(c) = 0
```

has coboundary:

```text
delta f([a,b]) = 1
delta f([a,c]) = 0
delta f([b,c]) = 1
```

The all-ones 1-cochain on the three edges is a cocycle and is not a
coboundary, so the finite rank replay gives:

```text
h0 = 1
h1 = 1
```
