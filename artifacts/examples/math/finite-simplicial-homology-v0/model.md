# Model

## Finite Data

A simplex is represented by a non-empty ordered list of vertex labels. In the
finite-complex rows, simplices use the vertex order from `vertices` so the
basis is deterministic.

The filled triangle witness lists:

```text
vertices = [a, b, c]
simplices = [a], [b], [c], [a,b], [a,c], [b,c], [a,b,c]
```

The circle witness removes the two-simplex and keeps only the three edges.

## Chain Encoding

A chain is a list of terms:

```json
{"coefficient": "-1", "simplex": ["a", "c"]}
```

The validator normalizes chains by simplex and drops zero coefficients.
Coefficients are parsed as exact rationals, although this pack uses integers.

## Boundary Encoding

For an oriented simplex `[v0, ..., vn]`, the boundary is the alternating face
sum:

```text
sum_i (-1)^i [v0, ..., v_{i-1}, v_{i+1}, ..., vn]
```

For `[a,b,c]`, this gives `[b,c] - [a,c] + [a,b]`.

## Homology Rank Encoding

For the finite circle, the validator builds the boundary matrices over exact
rationals and checks:

```text
rank(boundary_1) = 2
rank(boundary_2) = 0
dim C0 = 3
dim C1 = 3
b0 = dim C0 - rank(boundary_1) = 1
b1 = dim C1 - rank(boundary_1) - rank(boundary_2) = 1
```

This is rank replay for one fixed finite complex, not a general theorem about
homology.
