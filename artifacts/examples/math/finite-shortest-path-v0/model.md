# Model

The graph is directed and weighted:

```text
s -> a  weight 2
s -> b  weight 5
s -> t  weight 9
a -> b  weight 1
a -> t  weight 6
b -> t  weight 2
```

The source is `s` and the target is `t`.

The path witness is:

```text
s -> a -> b -> t
```

The exact length is:

```text
2 + 1 + 2 = 5
```

The potential certificate is:

```text
p(s) = 0
p(a) = 2
p(b) = 3
p(t) = 5
```

For every directed edge `u -> v`, the checker verifies:

```text
p(v) <= p(u) + weight(u,v)
```

Summing those inequalities along any `s`-to-`t` path proves that every path has
length at least `p(t) - p(s) = 5`. Since the listed path also has length `5`,
the fixed finite optimality certificate checks.
