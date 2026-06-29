# Model

The model is finite and table based.

## Vector Spaces

The pack uses the same vector-space table shape as `finite-vector-spaces-v0`:

- a finite field table for `F2`;
- finite carrier lists for vector spaces;
- an addition table;
- a scalar-multiplication table;
- an explicit finite dimension.

## Bilinear Maps

A bilinear map table is a list of triples:

```json
{"left": "10", "right": "1", "value": "10"}
```

The validator checks additivity and scalar preservation in both arguments by
exhaustive enumeration.

## Tensor Factorization

The tensor-map row uses:

```text
gamma(v,w) = h(beta(v,w))
```

where `beta` is the finite tensor map and `h` is a listed linear map from the
tensor space to a codomain vector space.

This is only a finite universal-property shadow. The full universal property
over arbitrary modules remains Lean-horizon.

## Bad Bilinear Certificate

For the rejected map, exact replay computes:

```text
10 + 01 = 11
beta(11,1) = 00
beta(10,1) = 10
beta(01,1) = 01
10 + 01 = 11
```

Left additivity of a bilinear map would require:

```text
beta(10 + 01, 1) = beta(10,1) + beta(01,1)
```

The linked `QF_UF` artifact is therefore unsatisfiable by equality reasoning.
The resource regression checks that Axeyum emits independently rechecked
`UnsatAletheProof` evidence with no trusted reduction step.
