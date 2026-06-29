# Finite Vector Spaces V0

This pack extends the linear-algebra and abstract-algebra bridge with exact
finite vector-space checks over `F2`. It treats `F2^2` as finite field data,
finite vector addition, scalar multiplication, subspaces, spans, and linear
maps.

The pack covers:

- vector-space table replay for `F2^2`;
- subspace and span replay for a one-dimensional subspace;
- linear-map replay for first-coordinate projection;
- kernel/image and rank-nullity replay by finite cardinality;
- checked rejection of a non-subspace;
- a Lean-horizon row for general vector-space and module theory.

## Concepts

- `curriculum_linear_algebra`
- `curriculum_fields`
- `curriculum_groups`
- `field_linear_algebra`
- `field_abstract_algebra`
- `field_set_theory_and_foundations`

## Trust Story

The validator parses finite field tables, vector addition tables, scalar
multiplication tables, subspace subsets, bases, and finite maps. It checks all
vector-space laws by finite enumeration, recomputes spans, kernels, images, and
dimensions from exact finite data, and rejects a bad subset by a concrete
addition counterexample.

This is a finite replay pack. It does not prove basis-extension, dimension
uniqueness, quotient-space, module, or infinite-dimensional vector-space
theorems.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
```
