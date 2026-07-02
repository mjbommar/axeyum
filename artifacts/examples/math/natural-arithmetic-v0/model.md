# Model

Each check uses naturals as exact nonnegative integers over a fixed finite
domain when enumeration is needed.

```text
S(n) = n + 1
a + S(b) = S(a + b)
a + b = b + a
a * (b + c) = a*b + a*c
```

The validator checks:

```text
successor addition:  exact replay of a + S(b) = S(a+b)
commutativity:       exact replay of a + b = b + a
distributivity:      exact replay of a*(b+c) = a*b + a*c
successor injective: no x != y with S(x) = S(y) in 0..max
zero predecessor:    no n with S(n) = 0 in 0..max
nonnegative domain:  no n < 0 in 0..max
```

## Axeyum Route

The intended Axeyum route is `QF_BV` for fixed bit-width finite domains or
`QF_LIA` with explicit nonnegative bounds.

The promoted negative-domain row now uses the `QF_LIA` route:

```text
0 <= n
n <= 7
n < 0
```

The finite replay justifies the bounded natural-domain constants. The SMT-LIB
artifact then exercises Axeyum's checked QF_LIA arithmetic evidence route for the
extracted integer contradiction.
