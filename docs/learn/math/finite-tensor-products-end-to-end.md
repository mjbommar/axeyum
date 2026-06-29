# End To End: Finite Tensor Products

This lesson follows one finite tensor-product resource from vector-space and
bilinear-map tables to replayed result and proof/evidence status. It uses the
[finite-tensor-products-v0](../../../artifacts/examples/math/finite-tensor-products-v0/)
pack.

Concept rows:

- `curriculum_linear_algebra`, `curriculum_fields`, and `curriculum_groups` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_linear_algebra`, `field_abstract_algebra`, and
  `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `tensor-product-basis-replay` | `sat` | replay-only |
| `bilinear-map-table-replay` | `sat` | checked |
| `universal-factorization-replay` | `sat` | checked |
| `kronecker-product-replay` | `sat` | checked |
| `bad-bilinear-map-rejected` | `unsat` | checked QF_UF/Alethe |
| `general-tensor-theory-lean-horizon` | `not-run` | lean-horizon |

The checked rows are exact finite replay rows over `F2`. The pack does not
claim the general tensor-product universal property over arbitrary modules,
multilinear algebra, exterior powers, symmetric powers, exactness, or
homological algebra.

## Encode

The left vector space is `F2^2`:

```text
00, 10, 01, 11
```

The right vector space is `F2`:

```text
0, 1
```

The tensor space is represented as another copy of `F2^2`, with basis tensors:

```text
10 tensor 1 -> 10
01 tensor 1 -> 01
```

The dimension row is finite arithmetic:

```text
dim(F2^2 tensor F2) = dim(F2^2) * dim(F2) = 2 * 1 = 2
```

## Replay The Tensor Basis

The checker validates the field and vector-space tables first. Then it checks
that the listed basis tensors span the finite tensor space:

```text
span({10, 01}) = {00, 10, 01, 11}
```

Because the tensor-space carrier has four elements over `F2`, the listed
dimension is:

```text
|tensor_space| = 4 = 2^2
```

This is a finite basis/dimension replay, not a proof that tensor products
always satisfy the dimension formula.

## Replay A Bilinear Map

The canonical finite bilinear table is:

```text
beta(v, a) = a*v
```

Representative rows are:

```text
beta(10, 0) = 00
beta(10, 1) = 10
beta(01, 1) = 01
beta(11, 1) = 11
```

The checker verifies additivity and scalar preservation in each argument. One
left-additivity row is:

```text
beta(10 + 01, 1) = beta(11, 1) = 11
beta(10, 1) + beta(01, 1) = 10 + 01 = 11
```

The validator repeats this over every finite vector, scalar, and argument
position.

## Replay A Finite Factorization Shadow

The factorization row uses a scalar-valued bilinear map `gamma` that factors
through the tensor map by a linear projection `h`:

```text
gamma(v, a) = h(beta(v, a))
```

The projection `h` reads the first coordinate of the tensor-space vector:

```text
h(00) = 0
h(10) = 1
h(01) = 0
h(11) = 1
```

For example:

```text
gamma(11, 1) = 1
h(beta(11, 1)) = h(11) = 1
```

The checker verifies that `beta` is bilinear, that `h` is linear, and that the
factorization equation holds for every listed finite pair. This is a useful
finite shadow of the universal property, not the full theorem.

## Replay A Kronecker Product

The pack also checks a concrete Kronecker product over `F2`:

```text
A = [[1, 1],
     [0, 1]]

B = [[0, 1],
     [1, 0]]
```

The claimed product is:

```text
A tensor B =
[[0, 1, 0, 1],
 [1, 0, 1, 0],
 [0, 0, 0, 1],
 [0, 0, 1, 0]]
```

The checker recomputes every block entry using the finite-field multiplication
table.

## Check The Refutation

The bad row changes the bilinear table so that:

```text
beta(10, 1) = 10
beta(01, 1) = 01
beta(11, 1) = 00
```

Left additivity should give:

```text
beta(10 + 01, 1) = beta(11, 1)
beta(10, 1) + beta(01, 1) = 10 + 01 = 11
```

The bad table claims `00` for the left side, while the recomputed sum is `11`.
The checker rejects the bilinearity claim. The linked `QF_UF` artifact records
`10 + 01 = 11`, `beta(11,1) = 00`, `beta(10,1) = 10`,
`beta(01,1) = 01`, `10 + 01 = 11`, and the fixed left-additivity equality
`beta(10+01,1) = beta(10,1)+beta(01,1)`; Axeyum emits and independently
rechecks an `UnsatAletheProof` for that equality conflict.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite multilinear algebra:

```text
untrusted fast search -> tensor basis, bilinear map, factor map, matrix product
trusted small checking -> basis span, bilinear laws, factorization, matrix replay
checked proof object -> QF_UF/Alethe certificate for the bad bilinear row
```

General tensor products, universal properties, multilinear maps, exterior and
symmetric powers, exactness, and homological algebra require Lean/mathlib-scale
proof support.
