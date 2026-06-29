# Model

## Field

The scalar field is `F2`:

```text
0 + 0 = 0
0 + 1 = 1
1 + 1 = 0
1 * 1 = 1
```

The validator checks the field table before using it as a scalar field.

## Vector Space

The vector carrier is:

```text
00, 10, 01, 11
```

Vector addition is coordinatewise XOR. Scalar multiplication by `0` sends
every vector to `00`; scalar multiplication by `1` is the identity.

The validator checks:

```text
1*v = v
0*v = 0
a*(v+w) = a*v + a*w
(a+b)*v = a*v + b*v
(a*b)*v = a*(b*v)
```

for every scalar and vector in the finite tables.

## Subspace And Span

The x-axis subspace is:

```text
{00, 10}
```

It is the span of the basis vector `10`. The validator recomputes every finite
linear combination over `F2`.

## Linear Map

The projection map is:

```text
00 -> 00
10 -> 10
01 -> 00
11 -> 10
```

The kernel is `{00, 01}` and the image is `{00, 10}`. Since all spaces are over
`F2`, the validator derives dimensions by checking cardinalities are powers of
`2`:

```text
dim(F2^2) = 2
dim(kernel) = 1
dim(image) = 1
2 = 1 + 1
```

## Bad Subspace Certificate

For the rejected subset, exact replay computes:

```text
10 in S
01 in S
10 + 01 = 11
11 not in S
```

Additive closure of a subspace would require:

```text
in_subset(add(10,01)) = present
```

The linked `QF_UF` artifact is therefore unsatisfiable by equality reasoning.
The resource regression checks that Axeyum emits independently rechecked
`UnsatAletheProof` evidence with no trusted reduction step.
