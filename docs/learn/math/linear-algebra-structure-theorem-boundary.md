# Linear Algebra Structure Theorem Boundary

This page separates Axeyum's finite vector-space, dual-space, module, and
tensor-product resources from general vector-space, duality, tensor, module,
and homological-algebra theorems.

Primary packs:

- [finite-vector-spaces-v0](../../../artifacts/examples/math/finite-vector-spaces-v0/)
- [finite-dual-spaces-v0](../../../artifacts/examples/math/finite-dual-spaces-v0/)
- [finite-modules-v0](../../../artifacts/examples/math/finite-modules-v0/)
- [finite-tensor-products-v0](../../../artifacts/examples/math/finite-tensor-products-v0/)

Companion lessons and maps:

- [End To End: Finite Vector Spaces](finite-vector-spaces-end-to-end.md)
- [End To End: Finite Dual Spaces](finite-dual-spaces-end-to-end.md)
- [End To End: Finite Modules](finite-modules-end-to-end.md)
- [End To End: Finite Tensor Products](finite-tensor-products-end-to-end.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Algebra And Number Theory](algebra-and-number-theory.md)
- [Matrix Computation Index](matrix-computation-index.md)
- [Theorem Horizon Queries](../../foundational-resources/THEOREM-HORIZON-QUERIES.md)

## Current Finite Resources

`finite-vector-spaces-v0` checks finite vector-space operation tables over
`F2`, finite subspaces and spans, a linear map with kernel and image, a
rank-nullity replay row, and bad subspace claims. The validator enumerates the
listed carrier and operations; the separate QF_UF/Alethe row checks the
isolated malformed addition-closure equality.

`finite-dual-spaces-v0` checks covectors as finite function tables. It
recomputes dual addition pointwise, validates dual-basis pairings,
annihilators, and transpose maps, and separates bad covector replay from a
checked QF_UF/Alethe additivity contradiction.

`finite-modules-v0` checks a finite `Z/4Z` module action, generated
submodules, a module homomorphism with kernel and image, quotient-module
operation tables, and a checked scalar-closure contradiction.

`finite-tensor-products-v0` checks a finite tensor-basis row, a bilinear map,
factorization through a tensor map, a Kronecker-product matrix, bad bilinear
map replay, and a checked QF_UF/Alethe left-additivity contradiction.

The checked resources cover:

```text
F2^2 vector-space table:       finite carrier and operations       -> replay-only finite table
subspace/span rows:            listed spans and bad subspace       -> replay plus checked bad-row evidence
linear map kernel/image:       first-coordinate projection         -> replay-only finite table
rank-nullity row:              2 = 1 + 1 for one finite map        -> replay-only finite cardinality
dual basis and annihilator:    covector function tables            -> checked finite replay
transpose map:                 (T*phi)(v) = phi(Tv) table          -> checked finite replay
module action and quotient:    Z/4Z regular module                 -> replay-only finite table
tensor basis and bilinear map: F2^2 tensor F2 finite shadow        -> replay plus checked finite table
bad closure/additivity rows:   one malformed equality each         -> checked QF_UF/Alethe evidence
general structure theorems:    arbitrary fields/modules/tensors    -> Lean/theorem work
```

Those rows prove bounded finite facts about the displayed data. They do not
prove dimension theorems, basis extension, duality theorems, tensor universal
properties, exact-sequence lemmas, or module-structure theorems for arbitrary
objects.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `f2-plane-vector-space` | `sat` | replay-only finite table | The listed four-element carrier and operations form `F2^2`. |
| `subspace-span-replay` | `sat` | replay-only finite table | The listed subset is the span of `10` in the displayed finite space. |
| `linear-map-kernel-image` | `sat` | replay-only finite table | The displayed projection has the listed kernel and image. |
| `rank-nullity-replay` | `sat` | replay-only finite table | Rank-nullity is replayed for this one finite map by counting the listed sets. |
| `bad-subspace-rejected` | `unsat` | checked finite replay | The listed malformed subset is not a subspace. |
| `qf-uf-bad-subspace-addition-closure` | `unsat` | checked QF_UF/Alethe | The malformed subset cannot satisfy the claimed addition-closure equality. |
| `dual-basis-pairing-replay` | `sat` | checked finite replay | The displayed covectors pair with the basis as the identity matrix. |
| `annihilator-replay` | `sat` | checked finite replay | The annihilator is recomputed from the finite evaluation table. |
| `transpose-map-replay` | `sat` | checked finite replay | The listed transpose map satisfies the finite evaluation equation. |
| `qf-uf-bad-covector-additivity` | `unsat` | checked QF_UF/Alethe | A malformed covector cannot satisfy additivity on the listed points. |
| `z4-regular-module` | `sat` | replay-only finite table | The listed `Z/4Z` action satisfies the finite module laws. |
| `module-hom-kernel-image` | `sat` | replay-only finite table | Multiplication by `2` has the listed kernel and image. |
| `quotient-module-replay` | `sat` | replay-only finite table | The quotient by `{0,2}` has the listed operation tables. |
| `qf-uf-bad-submodule-scalar-closure` | `unsat` | checked QF_UF/Alethe | The malformed submodule cannot satisfy scalar closure. |
| `tensor-product-basis-replay` | `sat` | replay-only finite table | The listed basis tensors span this finite tensor-product shadow. |
| `bilinear-map-table-replay` | `sat` | checked finite replay | The displayed map is bilinear on the finite tables. |
| `universal-factorization-replay` | `sat` | checked finite replay | One finite bilinear map factors through the listed tensor map. |
| `qf-uf-bad-bilinear-left-additivity` | `unsat` | checked QF_UF/Alethe | The malformed bilinear table cannot satisfy left additivity. |
| `general-vector-space-theory-lean-horizon` | `not-run` | Lean horizon | General vector-space and module theorems remain future proof work. |
| `general-duality-theory-lean-horizon` | `not-run` | Lean horizon | General duality, bidual, adjoint, and topological-dual theorems remain future proof work. |
| `general-module-theory-lean-horizon` | `not-run` | Lean horizon | General module theory and homological algebra remain future proof work. |
| `general-tensor-theory-lean-horizon` | `not-run` | Lean horizon | General tensor products and universal properties remain future proof work. |

The boundary is:

```text
untrusted fast search -> finite table, function graph, span, quotient, tensor witness
trusted small checking -> replayed operations plus scoped QF_UF/Alethe conflicts
theorem horizon       -> basis extension, dimension, duality, tensor, exact-sequence, and module theorems
```

## What Is Not Proved Yet

The current packs do not prove:

- existence of bases for arbitrary vector spaces;
- basis extension, exchange lemmas, or dimension invariance as general theorems;
- rank-nullity for every linear map over every field;
- duality, bidual, adjoint, annihilator, or topological-dual theorems in
  arbitrary settings;
- general tensor-product existence, uniqueness up to isomorphism, adjunction,
  exterior powers, symmetric powers, or multilinear universal properties;
- general module homomorphism, quotient, exact-sequence, projective/injective
  module, Noetherian, Ext, Tor, or homological-algebra theorems;
- infinite-dimensional functional-analysis claims or topological-vector-space
  claims.

Those claims need theorem statements, algebraic hypotheses, and no-`sorry`
proof artifacts before they can graduate from horizon metadata to theorem
coverage.

## Query The Boundary

Find the finite checked and replay rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-vector-spaces-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dual-spaces-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-modules-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-tensor-products-v0 \
  --require-any
```

Find the scoped QF_UF/Alethe certificate rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-vector-spaces-v0 \
  --route Alethe \
  --proof-status checked \
  --text addition-closure \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dual-spaces-v0 \
  --route Alethe \
  --proof-status checked \
  --text additivity \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-modules-v0 \
  --route Alethe \
  --proof-status checked \
  --text scalar-closure \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-tensor-products-v0 \
  --route Alethe \
  --proof-status checked \
  --text left-additivity \
  --require-any
```

Find the explicit theorem horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-vector-spaces-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-dual-spaces-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-modules-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-tensor-products-v0 \
  --require-any
```

Drill into individual teaching rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-vector-spaces-v0 \
  --text rank-nullity \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dual-spaces-v0 \
  --text annihilator \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-modules-v0 \
  --text quotient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-tensor-products-v0 \
  --text factorization \
  --require-any
```

## Graduation Criteria

Linear-algebra structure resources graduate only when they add:

1. precise theorem statements for the vector-space, duality, tensor, module,
   or homological-algebra claim;
2. explicit hypotheses, including field, ring, finite-dimensional,
   commutativity, choice, topology, or exactness assumptions;
3. no-`sorry` proof artifacts for each theorem claim before display labels
   change from finite replay to theorem coverage;
4. a kernel-checked route that explains how finite examples instantiate the
   theorem only where that instantiation is actually proved;
5. display labels that keep finite table replay, checked QF_UF/Alethe equality
   evidence, and theorem horizons separate.

Until then, the structure packs remain finite checked resources and compact
bridges to future algebra and linear-algebra proof resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
python3 scripts/query-foundational-resources.py checks --pack finite-vector-spaces-v0 --route Alethe --proof-status checked --text addition-closure --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-dual-spaces-v0 --route Alethe --proof-status checked --text additivity --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-modules-v0 --route Alethe --proof-status checked --text scalar-closure --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-tensor-products-v0 --route Alethe --proof-status checked --text left-additivity --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-vector-spaces-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-dual-spaces-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-modules-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-tensor-products-v0 --require-any
```

Expected resource boundary: finite carrier, operation, function, quotient, and
tensor rows validate; scoped closure/additivity contradictions stay checked
QF_UF/Alethe evidence; general vector-space, duality, tensor, module, and
homological-algebra theorems remain explicit Lean/theorem horizons.
