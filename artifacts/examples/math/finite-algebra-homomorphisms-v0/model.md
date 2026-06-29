# Model

## Group Tables

The group rows use explicit Cayley tables. For `Z/4Z` under addition:

```text
carrier = [0, 1, 2, 3]
identity = 0
```

For `Z/2Z`, the carrier is `[0, 1]`. The homomorphism is the parity map:

```text
f(0) = 0
f(1) = 1
f(2) = 0
f(3) = 1
```

The validator checks every pair:

```text
f(a + b) = f(a) + f(b)
```

using the listed source and target tables.

## Kernel, Image, And Quotient

The kernel is represented as a subset of the domain carrier:

```text
ker(f) = {0, 2}
image(f) = {0, 1}
```

The quotient data lists cosets explicitly:

```text
K  = {0, 2}
1K = {1, 3}
```

The quotient operation is checked by multiplying representatives in the source
table and finding the coset that contains the result.

The induced map sends each coset to the common image of its members:

```text
K  -> 0
1K -> 1
```

## Ring Tables

The ring row uses the same carrier map but checks both `add` and `mul` tables.
The validator also checks:

```text
f(0) = 0
f(1) = 1
```

This is one finite table replay, not a theorem about all quotient rings.
