# Exact Finite Specialization Order Checks

Audience: learners, educators, topology contributors, order-theory
contributors, and solver contributors who need a tiny topology-to-preorder
resource.

This pack checks how an explicit finite topology induces a specialization
preorder:

```text
x <= y  iff  every open set containing x also contains y
```

Equivalently, `x <= y` iff `x` lies in `closure({y})`. The checked slice is
finite replay plus one source-linked QF_UF/Alethe contradiction for a false
`T0`/antisymmetry claim.

## Rows

- `specialization-preorder-witness`: recompute the specialization preorder for
  a three-point finite topology.
- `closure-characterization-witness`: recompute singleton closures and compare
  them to the specialization relation.
- `t0-poset-witness`: check that the finite specialization preorder is
  antisymmetric for the listed `T0` example.
- `bad-t0-antisymmetry-rejected`: reject a false `T0` claim for the
  indiscrete two-point topology using checked QF_UF/Alethe evidence.
- `general-specialization-order-lean-horizon`: keep arbitrary-space
  specialization-order theory under Lean horizon.

## Trust Boundary

The finite validator recomputes the topology axioms, specialization relation,
singleton closures, and `T0`/antisymmetry property from the source data. The
promoted bad row is accepted only because the fixed antisymmetry equality
conflict has a checked Alethe proof. This pack does not prove T0 quotients,
sobriety, Alexandroff-space equivalences, or domain-theoretic topology.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-specialization-order-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_specialization_order_bad_t0_antisymmetry_emits_checked_alethe
```
