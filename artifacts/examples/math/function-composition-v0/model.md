# Model

The pack models functions as explicit finite graphs.

Each function row has:

- a finite `domain`;
- a finite `codomain`;
- a list of graph `pairs`.

The validator first checks that every graph is total and single-valued. It then
extracts a mapping and computes:

```text
(g o f)(x) = g(f(x))
image(S) = { f(x) | x in S }
preimage(T) = { x | f(x) in T }
f^{-1}(y) = the unique x with f(x) = y
```

For associativity, the validator computes both finite tables:

```text
h o (g o f)
(h o g) o f
```

and requires them to match exactly.

## Limitations

These are fixed finite function tables. They teach the executable shape of
function composition and inverse laws, but they do not certify the general laws
over arbitrary sets or types.
