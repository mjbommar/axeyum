# Model

The source finite topology has:

```text
X = {a,b,c}
open(X) = {}, {a,b}, {a,b,c}
```

The quotient map is:

```text
q(a) = p
q(b) = p
q(c) = r
```

so the fibers are:

```text
q^{-1}({p}) = {a,b}
q^{-1}({r}) = {c}
```

The same-fiber equivalence relation is:

```text
a ~ a, a ~ b
b ~ a, b ~ b
c ~ c
```

The quotient topology on `{p,r}` is computed by preimages:

```text
{}      -> {}
{p}     -> {a,b}
{r}     -> {c}
{p,r}   -> {a,b,c}
```

Only `{}`, `{p}`, and `{p,r}` have open preimages in `X`, so these are exactly
the quotient-open subsets.

A subset of `X` is saturated when it is a union of quotient fibers. The set
`{a,b}` is saturated and open; its image is `{p}`, and
`q^{-1}({p}) = {a,b}`.

The rejected representative row uses the same quotient map. Since `a` and `b`
belong to the same fiber, exact replay computes:

```text
q(a) = p
q(b) = p
```

The malformed row claims `q(a) != q(b)`. The source `QF_UF` artifact checks
only that fixed representative-consistency conflict.
