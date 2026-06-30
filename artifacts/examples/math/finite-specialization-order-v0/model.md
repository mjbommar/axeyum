# Model

The finite topology is encoded as:

- `universe`: unique point identifiers;
- `open_sets`: listed subsets of the universe;
- `specialization_pairs`: ordered pairs `[x, y]` intended to mean `x <= y`;
- optional `singleton_closures`: the listed closure of each singleton.

The validator first checks the finite topology axioms. It then recomputes:

```text
x <= y  iff  every open set containing x also contains y
```

For the three-point example:

```text
open sets = {}, {a}, {a,b}, {a,b,c}
```

the specialization preorder is:

```text
a <= a
b <= b, b <= a
c <= c, c <= b, c <= a
```

The singleton closures are:

```text
closure({a}) = {a,b,c}
closure({b}) = {b,c}
closure({c}) = {c}
```

The indiscrete two-point negative row has only `{}` and `{x,y}` open. Both
points have the same open neighborhoods, so `x <= y` and `y <= x`; a false
`T0`/antisymmetry claim would force `x = y`.
